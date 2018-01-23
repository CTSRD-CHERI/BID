// 2018, Alexandre Joannou, University of Cambridge

import FIFO :: *;
import List :: *;
import Vector :: *;
import BitPat :: *;
import BID :: *;

// example file using the BID framework

////////////////////////////////////////
// Define common state and behaviours //
////////////////////////////////////////////////////////////////////////////////

typedef struct {
  Vector#(32,Reg#(Bit#(32))) regfile;
  Reg#(Bit#(32)) pc;
} MyArchState;

instance ArchState#(MyArchState);

  module initArchState (MyArchState);
    MyArchState s;
    s.regfile <- mkRegFileZ;
    s.pc <- mkReg(0);
    return s;
  endmodule

  function Fmt lightReport (MyArchState s);
    return $format("pc = 0x%0x", s.pc);
  endfunction

  function Fmt fullReport (MyArchState s);
    return (
      $format("regfile %s \n", map(readReg,s.regfile)) +
      $format("pc = 0x%0x", s.pc)
    );
  endfunction

endinstance

typedef struct {
  Mem#(Bit#(32), Bit#(32)) mem;
} MyWorld;

instance World#(MyWorld);

  module initWorld (MyWorld);
    MyWorld w;
    w.mem <- mkSimpleMem(8192);
    return w;
  endmodule

endinstance

function Action pcEpilogue(MyArchState s, MyWorld w) =
  action
    $display("---------- epilogue @%0t ----------", $time);
    Bit#(32) tmpPC = s.pc + 4;
    s.pc <= tmpPC;
    $display("s.pc <= 0x%0x", tmpPC);
  endaction;

////////////////////////////
// Define instruction set //
////////////////////////////////////////////////////////////////////////////////

// These instructions and their encoding are borrowed from the RISC-V I ISA
module [InstrDefModule#(32)] mkBaseISA#(MyArchState s, MyWorld w) ();

  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("add %0d, %0d, %0d", rd, rs1, rs2);
      $display("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]);
      s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
      pcEpilogue(s,w);
    endaction;
  defineInstr(pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  function Action instrADDI(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("addi %0d, %0d, %0d", rd, rs1, imm);
      $display("regfile[%0d] <= %0d", rd, s.regfile[rs1] + signExtend(imm));
      s.regfile[rd] <= s.regfile[rs1] + signExtend(imm);
      pcEpilogue(s,w);
    endaction;
  defineInstr(pat(v, v, n(3'b0), v, n(7'b0010011)),instrADDI);

  function Action instrJAL(Bit#(1) imm20, Bit#(10) imm10_1, Bit#(1) imm11, Bit#(8) imm19_12, Bit#(5) rd) =
    action
      Bit#(32) imm = {signExtend(imm20),imm19_12,imm11,imm10_1,1'b0};
      s.pc <= s.pc + imm;
      s.regfile[rd] <= s.pc + 4;
      $display("jal %0d, %0d", rd, imm);
    endaction;
  defineInstr(pat(v, v, v, v, v, n(7'b1101111)),instrJAL);

  function List#(Action) instrLB(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) =
    list(
      action
        $display("lb %0d, %0d, %0d - step 1", rd, rs1, imm);
        Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
        w.mem.sendReq(tagged ReadReq {addr: addr, numBytes: 1});
      endaction,
      action
        $display("lb %0d, %0d, %0d - step 2", rd, rs1, imm);
        let rsp <- w.mem.getRsp();
        case (rsp) matches tagged ReadRsp .r: s.regfile[rd] <= r; endcase
        pcEpilogue(s,w);
      endaction
    );
  defineInstr(pat(v, v, n(3'b000), v, n(7'b0000011)),instrLB);

  function Action instrSB(Bit#(7) imm11_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) imm4_0) =
    action
      Bit#(32) imm = {signExtend(imm11_5), imm4_0};
      Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
      w.mem.sendReq(tagged WriteReq {addr: addr, byteEnable: 'b1, data: s.regfile[rs2]});
      $display("sb %0d, %0d, %0d", rs1, rs2, imm);
    endaction;
  defineInstr(pat(v, v, v, n(3'b000), v, n(7'b0100011)),instrSB);

endmodule

///////////////////////////////////
// Instanciate the ISA simulator //
////////////////////////////////////////////////////////////////////////////////

module top ();

  MyArchState s <- initArchState;
  MyWorld w <- initWorld;
  InstStream#(32) instStream <- mkInstStream("test-prog.hex", 1024);

  // instanciating simulator
  mkISASim(instStream, s, w, list(mkBaseISA));

endmodule

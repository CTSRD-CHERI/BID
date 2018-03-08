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
  Vector#(32,Reg#(Bit#(n))) regfile;
  PC#(Bit#(n)) pc;
  Reg#(UInt#(64)) instCnt;
} MyArchState#(numeric type n);

module mkArchState (MyArchState#(32));
  MyArchState#(32) s;
  s.regfile <- mkRegFileZ;
  s.pc <- mkPC(0);
  s.instCnt <- mkReg(0);
  return s;
endmodule

instance ArchState#(MyArchState#(n));

  function Fmt lightReport (MyArchState#(n) s);
    return $format("pc = 0x%0x, instCnt = %0d", s.pc, s.instCnt);
  endfunction

  function Fmt fullReport (MyArchState#(n) s);
    return (
      $format("regfile %s \n", map(readReg,s.regfile)) +
      $format("pc = 0x%0x, instCnt = %0d", s.pc, s.instCnt)
    );
  endfunction

endinstance

function Action pcEpilogue(MyArchState#(32) s) =
  action
    printTLog("--------------- epilogue --------------");
    Bit#(32) tmpPC = s.pc + 4;
    s.pc <= tmpPC;
    s.instCnt <= s.instCnt + 1;
    printTLog($format("s.pc <= 0x%0x", tmpPC));
  endaction;

////////////////////////////
// Define instruction set //
////////////////////////////////////////////////////////////////////////////////

// These instructions and their encoding are borrowed from the RISC-V I ISA
module [InstrDefModule#(32)] mkBaseISA#(MyArchState#(32) s, Mem#(Bit#(32), Bit#(32)) mem) ();

  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
    printTLog($format("add %0d, %0d, %0d", rd, rs1, rs2));
    printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]));
    s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
    pcEpilogue(s);
  endaction;
  defineInstr("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  function Action instrADDI(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = action
    printTLog($format("addi %0d, %0d, %0d", rd, rs1, imm));
    printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + signExtend(imm)));
    s.regfile[rd] <= s.regfile[rs1] + signExtend(imm);
    pcEpilogue(s);
  endaction;
  defineInstr("addi",pat(v, v, n(3'b0), v, n(7'b0010011)),instrADDI);

  function Action instrJAL(Bit#(1) imm20, Bit#(10) imm10_1, Bit#(1) imm11, Bit#(8) imm19_12, Bit#(5) rd) = action
    Bit#(32) imm = {signExtend(imm20),imm19_12,imm11,imm10_1,1'b0};
    s.pc <= s.pc + imm;
    s.regfile[rd] <= s.pc + 4;
    printTLog($format("jal %0d, %0d", rd, imm));
  endaction;
  defineInstr("jal",pat(v, v, v, v, v, n(7'b1101111)),instrJAL);

  function Action instrBEQ (Bit#(1) imm12, Bit#(6) imm10_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(4) imm4_1, Bit#(1) imm11) = action
    Bit#(32) imm = {signExtend(imm12),imm11,imm10_5,imm4_1,1'b0};
    if (s.regfile[rs1] == s.regfile[rs2]) s.pc <= s.pc + imm;
    else s.pc <= s.pc + 4;
    printTLog($format("beq", rs1, rs2, imm));
  endaction;
  defineInstr("beq",pat(v, v, v, v, n(3'b000), v, v, n(7'b1100011)), instrBEQ);

  function List#(Action) instrLB(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = list(
    action
      printTLog($format("lb %0d, %0d, %0d - step 1", rd, rs1, imm));
      Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
      mem.sendReq(tagged ReadReq {addr: addr, numBytes: 1});
    endaction,
    action
      printTLog($format("lb %0d, %0d, %0d - step 2", rd, rs1, imm));
      let rsp <- mem.getRsp();
      case (rsp) matches tagged ReadRsp .r: s.regfile[rd] <= r; endcase
      pcEpilogue(s);
    endaction
  );
  defineInstr("lb",pat(v, v, n(3'b000), v, n(7'b0000011)),instrLB);

  function Action instrSB(Bit#(7) imm11_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) imm4_0) = action
    Bit#(32) imm = {signExtend(imm11_5), imm4_0};
    Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
    mem.sendReq(tagged WriteReq {addr: addr, byteEnable: 'b1, data: s.regfile[rs2]});
    printTLog($format("sb %0d, %0d, %0d", rs1, rs2, imm));
    pcEpilogue(s);
  endaction;
  defineInstr("sb",pat(v, v, v, n(3'b000), v, n(7'b0100011)),instrSB);

  function List#(Action) unkInst(Bit#(32) inst) = list(
    action
      printTLog($format("Unknown instruction 0x%0x", inst));
      pcEpilogue(s);
    endaction,
    printTLog($format("bye"))
  );
  defineUnkInstr(unkInst);
  // XXX uncomment to get multiple unknown instruction definition error
  //defineUnkInstr(unkInst);

endmodule

module [InstrDefModule#(32)] mkExtensionISA#(MyArchState#(32) s, Mem#(Bit#(32), Bit#(32)) mem) ();

  // overwriting ADD instruction with new behaviour (just different logging)
  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
    printTLog($format("EXTENDED add %0d, %0d, %0d", rd, rs1, rs2));
    printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]));
    s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
    pcEpilogue(s);
  endaction;
  defineInstr("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  // XXX uncomment to get multiple in module instruction definition error
  //defineInstr("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

endmodule

///////////////////////////////////
// Instanciate the ISA simulator //
////////////////////////////////////////////////////////////////////////////////

module top ();

  MyArchState#(32) s <- mkArchState;
  FullMem#(Bit#(32), Bit#(32), Bit#(32)) mem <- mkFullMem(4096, "test-prog.hex", s.pc.next);

  // instanciating simulator
  //mkISASim(mem, s, list(mkBaseISA));
  mkISASim(mem, s, list(mkBaseISA, mkExtensionISA));

endmodule

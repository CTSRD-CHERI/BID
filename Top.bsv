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
  Reg#(Bit#(n)) instByteSz;
  Reg#(UInt#(64)) instCnt;
  DMem#(Bit#(32), Bit#(32)) dmem;
  IMem#(Bit#(32)) imem;
} MyState#(numeric type n);

module mkState (MyState#(32));
  MyState#(32) s;
  s.regfile <- mkRegFileZ;
  s.pc <- mkPC(0);
  s.instByteSz <- mkBypassRegU;
  s.instCnt <- mkReg(0);
  FullMem#(Bit#(32), Bit#(32), Bit#(32)) mem <- mkFullMem(4096, "test-prog.hex", s.pc.next);
  s.dmem = mem.data;
  s.imem = mem.inst;
  return s;
endmodule

instance State#(MyState#(n));

  function Fmt lightReport (MyState#(n) s);
    return $format("pc = 0x%0x, instCnt = %0d", s.pc, s.instCnt);
  endfunction
  function Fmt fullReport (MyState#(n) s);
    return (
      $format("regfile %s \n", map(readReg,s.regfile)) +
      $format("pc = 0x%0x, instCnt = %0d", s.pc, s.instCnt)
    );
  endfunction
  function Action reqNextInst(MyState#(n) s) = s.imem.reqNext();
  function ActionValue#(Bit#(MaxInstSz)) getNextInst(MyState#(n) s) = actionvalue
    let inst <- s.imem.get();
    s.instByteSz <= (inst[1:0] == 2'b11) ? 4 : 2;
    return inst;
  endactionvalue;

endinstance

function Action pcEpilogue(MyState#(32) s) =
  action
    printTLog("--------------- epilogue --------------");
    Bit#(32) tmpPC = s.pc + s.instByteSz;
    s.pc <= tmpPC;
    s.instCnt <= s.instCnt + 1;
    printTLog($format("s.pc <= 0x%0x", tmpPC));
  endaction;

////////////////////////////
// Define instruction set //
////////////////////////////////////////////////////////////////////////////////

function Action instrADD(MyState#(32) s, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
  printTLog($format("add %0d, %0d, %0d", rd, rs1, rs2));
  printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]));
  s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
  pcEpilogue(s);
endaction;

function Action instrADDI(MyState#(32) s, Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = action
  printTLog($format("addi %0d, %0d, %0d", rd, rs1, imm));
  printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + signExtend(imm)));
  s.regfile[rd] <= s.regfile[rs1] + signExtend(imm);
  pcEpilogue(s);
endaction;

function Action instrJAL(MyState#(32) s, Bit#(1) imm20, Bit#(10) imm10_1, Bit#(1) imm11, Bit#(8) imm19_12, Bit#(5) rd) = action
  Bit#(32) imm = {signExtend(imm20),imm19_12,imm11,imm10_1,1'b0};
  s.pc <= s.pc + imm;
  s.regfile[rd] <= s.pc + s.instByteSz;
  printTLog($format("jal %0d, %0d", rd, imm));
endaction;

function Action instrBEQ (MyState#(32) s, Bit#(1) imm12, Bit#(6) imm10_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(4) imm4_1, Bit#(1) imm11) = action
  Bit#(32) imm = {signExtend(imm12),imm11,imm10_5,imm4_1,1'b0};
  if (s.regfile[rs1] == s.regfile[rs2]) s.pc <= s.pc + imm;
  else s.pc <= s.pc + s.instByteSz;
  printTLog($format("beq", rs1, rs2, imm));
endaction;

function List#(Action) instrLB(MyState#(32) s, Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = list(
  action
    printTLog($format("lb %0d, %0d, %0d - step 1", rd, rs1, imm));
    Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
    s.dmem.sendReq(tagged ReadReq {addr: addr, numBytes: 1});
  endaction,
  action
    printTLog($format("lb %0d, %0d, %0d - step 2", rd, rs1, imm));
    let rsp <- s.dmem.getRsp();
    case (rsp) matches tagged ReadRsp .r: s.regfile[rd] <= r; endcase
    pcEpilogue(s);
  endaction
);

function Action instrSB(MyState#(32) s, Bit#(7) imm11_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) imm4_0) = action
  Bit#(32) imm = {signExtend(imm11_5), imm4_0};
  Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
  s.dmem.sendReq(tagged WriteReq {addr: addr, byteEnable: 'b1, data: s.regfile[rs2]});
  printTLog($format("sb %0d, %0d, %0d", rs1, rs2, imm));
  pcEpilogue(s);
endaction;

function Action instrC_LI(MyState#(32) s, Bit#(1) imm_5, Bit#(5) rd, Bit#(5) imm4_0) = action
  s.regfile[rd] <= signExtend({imm_5, imm4_0});
  printTLog($format("c.li %0d, %0d", rd, {imm_5, imm4_0}));
  s.pc <= s.pc + s.instByteSz;
endaction;

function List#(Action) unkInst(MyState#(32) s, Bit#(MaxInstSz) inst) = list(
  action
    printTLog($format("Unknown instruction 0x%0x", inst));
    pcEpilogue(s);
  endaction,
  printTLog($format("bye"))
);

// example Base ISA definition
// These instructions and their encoding are borrowed from the RISC-V I ISA
module [InstrDefModule] mkBaseISA#(MyState#(32) s) ();

  defineInstr("add" , pat(n(7'b0), v, v, n(3'b000),    v, n(7'b0110011)), instrADD(s));
  defineInstr("addi", pat(         v, v, n(3'b000),    v, n(7'b0010011)), instrADDI(s));
  defineInstr("jal" , pat(                 v, v, v, v, v, n(7'b1101111)), instrJAL(s));
  defineInstr("beq" , pat(   v, v, v, v, n(3'b000), v, v, n(7'b1100011)), instrBEQ(s));
  defineInstr("lb"  , pat(         v, v, n(3'b000),    v, n(7'b0000011)), instrLB(s));
  defineInstr("sb"  , pat(      v, v, v, n(3'b000),    v, n(7'b0100011)), instrSB(s));
  defineInstr("c.li",                  pat(n(3'b010), v, v, v, n(2'b01)), instrC_LI(s));
  defineUnkInstr(unkInst(s));
  // XXX uncomment to get multiple unknown instruction definition error
  //defineUnkInstr(unkInst);

endmodule

// example extension module with instruction overwritting
module [InstrDefModule] mkExtensionISA#(MyState#(32) s) ();

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

  MyState#(32) s <- mkState;

  // instanciating simulator
  // Instruction defined in modules later in the list overwrite earlier definitions
  mkISASim(s, list(mkBaseISA, mkExtensionISA));

endmodule

// 2018, Alexandre Joannou, University of Cambridge

import FIFO :: *;
import List :: *;
import Vector :: *;
import BitPat :: *;
import BID :: *;

typedef struct {
  Vector#(32,Reg#(Bit#(32))) regfile;
  Reg#(Bit#(32)) pc;
  Reg#(Maybe#(Bit#(32))) newPC;
} ArchState;

module initState (ArchState);
  ArchState s;
  s.regfile <- replicateM(mkReg(0));
  s.pc <- mkReg(0);
  s.newPC <- mkReg(tagged Invalid);
  return s;
endmodule

module [InstrDefModule#(32)] mkBaseISA#(ArchState s, World w) ();

  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("world: ", fshow(w));
      $display("add %0d, %0d, %0d", rd, rs1, rs2);
      $display("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]);
      s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
    endaction;
  defineInstr(pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  function Action instrADDI(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("world: ", fshow(w));
      $display("addi %0d, %0d, %0d", rd, rs1, imm);
      $display("regfile[%0d] <= %0d", rd, s.regfile[rs1] + signExtend(imm));
      s.regfile[rd] <= s.regfile[rs1] + signExtend(imm);
    endaction;
  defineInstr(pat(v, v, n(3'b0), v, n(7'b0010011)),instrADDI);

  function Action instrJAL(Bit#(1) imm20, Bit#(10) imm10_1, Bit#(1) imm11, Bit#(8) imm19_12, Bit#(5) rd) =
    action
      Bit#(32) imm = {signExtend(imm20),imm19_12,imm11,imm10_1,1'b0};
      s.newPC <= tagged Valid (s.pc + imm);
      s.regfile[rd] <= s.pc + 4;
      $display("world: ", fshow(w));
      $display("jal %0d, %0d", rd, imm);
    endaction;
  defineInstr(pat(v, v, v, v, v, n(7'b1101111)),instrJAL);

  function List#(Action) instrMultiStepTest(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) =
    List::cons(
    action
      $display("instrMultiCycleTest step 1");
    endaction,
    List::cons(
    action
      $display("instrMultiCycleTest step 2");
      $display("writing newPC");
      s.newPC <= tagged Valid (0);
    endaction,
    List::cons(
    action
      $display("instrMultiCycleTest step 3");
    endaction,
    Nil)));
  defineInstr(pat(v, v, n(3'b111), v, n(7'b1111111)),instrMultiStepTest);

endmodule

function Action epilogue(ArchState s, World w) =
  action
    Bit#(32) tmpPC = fromMaybe(s.pc + 4, s.newPC);
    $display("writing pc <= 0x%0x", tmpPC);
    s.pc <= tmpPC;
    s.newPC <= tagged Invalid;
  endaction;

module top ();
  Reg#(Bit#(2)) toggle <- mkReg(0);
  FIFO#(Bit#(32)) instq <- mkFIFO();
  ArchState s <- initState;
  mkISASim(instq, List::cons(mkBaseISA(s), Nil), epilogue(s));
  rule fetchInstr;
    if (toggle == 0) instq.enq(32'b0000000_00001_00010_000_00011_1101111); // JAL
    else if (toggle == 1) instq.enq(32'b0000000_00001_00010_000_00011_0110011); // ADD
    else if (toggle == 2) instq.enq(32'b0000000_00001_00010_111_00011_1111111); // MultiStepTest
    else if (toggle == 3) instq.enq(32'b0000000_00001_00010_000_00011_0010011); // ADDI
    toggle <= toggle + 1;
  endrule
endmodule

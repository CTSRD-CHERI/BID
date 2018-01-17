// 2018, Alexandre Joannou, University of Cambridge

import List :: *;
import Vector :: *;
import BitPat :: *;
import BID :: *;

typedef struct {
  Vector#(32,Reg#(Bit#(64))) regfile;
  //Reg#(Bit#(64)) pc;
} ArchState;

module [InstrDefModule#(32)] mkBaseISA#(ArchState s, World w) ();

  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("world: %s", fshow(w));
      $display("add %0d, %0d, %0d", rd, rs1, rs2);
      $display("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]);
      s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
    endaction;
  defineInstr(pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  function Action instrADDI(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("world: %s", fshow(w));
      $display("addi %0d, %0d, %0d", rd, rs1, imm);
      $display("regfile[%0d] <= %0d", rd, s.regfile[rs1] + signExtend(imm));
      s.regfile[rd] <= s.regfile[rs1] + signExtend(imm);
    endaction;
  defineInstr(pat(v, v, n(3'b0), v, n(7'b0010011)),instrADDI);

endmodule

module top ();
  Bit#(32) instr = 32'b0000000_00001_00010_000_00011_0110011;
  //Bit#(32) instr = 32'b0000000_00001_00010_000_00011_0010011;
  ArchState s;
  //Vector#(32,Reg#(Bit#(64))) rf <- replicateM(mkReg(0));
  s.regfile <- replicateM(mkReg(0));
  mkISASim(instr, List::cons(mkBaseISA(s), Nil));
endmodule

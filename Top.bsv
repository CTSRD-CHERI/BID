// 2018, Alexandre Joannou, University of Cambridge

import List :: *;
import Vector :: *;
import BitPat :: *;
import BID :: *;

module [InstrDefModule#(32)] mkBaseISA ();

  Vector#(32,Reg#(Bit#(64))) regfile <- replicateM(mkReg(0));

  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("add %0d, %0d, %0d", rd, rs1, rs2);
      $display("regfile[%0d] <= %0d", rd, regfile[rs1] + regfile[rs2]);
      regfile[rd] <= regfile[rs1] + regfile[rs2];
    endaction;
  defineInstr(pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  function Action instrADDI(Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) =
    action
      $display("addi %0d, %0d, %0d", rd, rs1, imm);
      $display("regfile[%0d] <= %0d", rd, regfile[rs1] + signExtend(imm));
      regfile[rd] <= regfile[rs1] + signExtend(imm);
    endaction;
  defineInstr(pat(v, v, n(3'b0), v, n(7'b0010011)),instrADDI);

endmodule

module top ();
  Bit#(32) instr = 32'b0000000_00001_00010_000_00011_0110011;
  //Bit#(32) instr = 32'b0000000_00001_00010_000_00011_0010011;
  mkISASim(instr, List::cons(mkBaseISA, Nil));
endmodule

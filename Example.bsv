/*-
 * Copyright (c) 2018 Alexandre Joannou
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

import Vector :: *;

import BitPat :: *;
import BID :: *;

// Example use of the BID framework

////////////////////////////////////////
// Define common state and behaviours //
////////////////////////////////////////////////////////////////////////////////

// An architectural state of the example machine
typedef struct {
  // register file
  Vector#(32,Reg#(Bit#(32))) regfile;
  // program counter
  PC#(Bit#(32)) pc;
  // current instruction's byte length (useful for variable length instructions
  // support)
  Reg#(Bit#(32)) instByteSz;
  // instruction counter
  Reg#(UInt#(64)) instCnt;
  // interface to data memory
  Mem#(Bit#(32), Bit#(32)) dmem;
  // interface to instruction memory
  Mem#(Bit#(32), Bit#(32)) imem;
} ArchState;

// ArchState initialization module
module mkState (ArchState);
  ArchState s;
  s.regfile <- mkRegFileZ;
  // Use the BID mkPC module that provides an interface with the conventional
  // _read() and _write() methods, together with a next() method capturing the
  // next value of the PC to help for instruction fetching.
  s.pc <- mkPC(0);
  // Use the BID mkBypassRegU module that provides a standard Reg interface
  // with the _read() returning the value written in the current cycle if
  // _write() was called, or the previous value otherwise.
  s.instByteSz <- mkBypassRegU;
  s.instCnt <- mkReg(0);
  // Use BID mkSharedMem2 module initialized with the "test-prog.hex" file's
  // content with a size of 4096 bytes.
  Mem2#(Bit#(32), Bit#(32), Bit#(32)) mem <- mkSharedMem2(4096, "test-prog.hex");
  s.dmem = mem.p0;
  s.imem = mem.p1;
  return s;
endmodule

// Make the ArchState user type an instance of the BID State typeclass so it
// can be later used to create a ISA simulator.
instance State#(ArchState);

  // Some logging
  function Fmt lightReport (ArchState s);
    return $format("pc = 0x%0x, instCnt = %0d", s.pc, s.instCnt);
  endfunction
  // Some heavy logging
  function Fmt fullReport (ArchState s);
    return (
      $format("regfile %s \n", map(readReg,s.regfile)) +
      $format("pc = 0x%0x, instCnt = %0d", s.pc, s.instCnt)
    );
  endfunction
  // Two functions to describe the behaviour the simulator should follow when
  // fetching instructions
  function Action reqNextInst(ArchState s) = s.imem.sendReq(tagged ReadReq {
    addr: s.pc.next, // note the use of the "next" method of the PC register
    numBytes: 4 // request four bytes for an instruction
  });
  function ActionValue#(Bit#(MaxInstSz)) getNextInst(ArchState s) = actionvalue
    let rsp <- s.imem.getRsp(); // get the memory response
    case (rsp) matches
      tagged ReadRsp .val: begin
        // update the current instruction size
        s.instByteSz <= (val[1:0] == 2'b11) ? 4 : 2;
        return val;
      end
      default: return ?;
    endcase
  endactionvalue;

endinstance

// Example of an epilogue helper function that can be invoked at the end of
// an instruction's semantic function.
function Action pcEpilogue(ArchState s) =
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

// A few instructions (from the RISC-V ISA) semantic functions defined as
// toplevel functions, explicitly receiving the architectural state, and
// returning a single Action.
function Action instrADD(ArchState s, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
  printTLog($format("add %0d, %0d, %0d", rd, rs1, rs2));
  printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]));
  s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
  pcEpilogue(s);
endaction;

function Action instrADDI(ArchState s, Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = action
  printTLog($format("addi %0d, %0d, %0d", rd, rs1, imm));
  printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + signExtend(imm)));
  s.regfile[rd] <= s.regfile[rs1] + signExtend(imm);
  pcEpilogue(s);
endaction;

function Action instrJAL(ArchState s, Bit#(1) imm20, Bit#(10) imm10_1, Bit#(1) imm11, Bit#(8) imm19_12, Bit#(5) rd) = action
  Bit#(32) imm = {signExtend(imm20),imm19_12,imm11,imm10_1,1'b0};
  s.pc <= s.pc + imm;
  s.regfile[rd] <= s.pc + s.instByteSz;
  printTLog($format("jal %0d, %0d", rd, imm));
endaction;

function Action instrBEQ (ArchState s, Bit#(1) imm12, Bit#(6) imm10_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(4) imm4_1, Bit#(1) imm11) = action
  Bit#(32) imm = {signExtend(imm12),imm11,imm10_5,imm4_1,1'b0};
  if (s.regfile[rs1] == s.regfile[rs2]) s.pc <= s.pc + imm;
  else s.pc <= s.pc + s.instByteSz;
  printTLog($format("beq", rs1, rs2, imm));
endaction;

// A load byte instruction returning a List#(Action) to express interraction
// with a module with potential latency (the memory).
function List#(Action) instrLB(ArchState s, Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = list(
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

function Action instrSB(ArchState s, Bit#(7) imm11_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) imm4_0) = action
  Bit#(32) imm = {signExtend(imm11_5), imm4_0};
  Bit#(32) addr = s.regfile[rs1] + signExtend(imm);
  s.dmem.sendReq(tagged WriteReq {addr: addr, byteEnable: 'b1, data: s.regfile[rs2]});
  printTLog($format("sb %0d, %0d, %0d", rs1, rs2, imm));
  pcEpilogue(s);
endaction;

// An example of a compressed instruction. See the pattern definition for details.
function Action instrC_LI(ArchState s, Bit#(1) imm_5, Bit#(5) rd, Bit#(5) imm4_0) = action
  s.regfile[rd] <= signExtend({imm_5, imm4_0});
  printTLog($format("c.li %0d, %0d", rd, {imm_5, imm4_0}));
  s.pc <= s.pc + s.instByteSz;
endaction;

// The unknown instruction, to be executed when no other instruction matched.
function List#(Action) unkInst(ArchState s, Bit#(MaxInstSz) inst) = list(
  action
    printTLog($format("Unknown instruction 0x%0x", inst));
    pcEpilogue(s);
  endaction,
  printTLog($format("bye"))
);

// Define a BID InstrDefModule module to enable the use of defineInstr and
// defineUnkInstr. Note the BID State instance as a module argument.
module [InstrDefModule] mkBaseISA#(ArchState s) ();

  // Use the BID defineInstr primitive to register an instruction with the
  // simulator. The first argument is a string to identify an instruction, the
  // second argument is a pattern to be matched. The third argument is the
  // semantic function of the instruction being registered.
  // The pat() function creates a pattern where opcodes fields can be expressed
  // as a numeric constant via the n() fuction, and the v() function can be
  // used for variable fields which get passed to the semantic function. The
  // types of the variables is infered from the semantic function's signature:
  // note that the following semantic functions are all partially applied with
  // the architectural state, effectivelly leaving only the relevant arguments
  // to correctly infer the types in the pattern.
  defineInstr("add" , pat(n(7'b0), v, v, n(3'b000),    v, n(7'b0110011)), instrADD(s));
  defineInstr("addi", pat(         v, v, n(3'b000),    v, n(7'b0010011)), instrADDI(s));
  defineInstr("jal" , pat(                 v, v, v, v, v, n(7'b1101111)), instrJAL(s));
  defineInstr("beq" , pat(   v, v, v, v, n(3'b000), v, v, n(7'b1100011)), instrBEQ(s));
  defineInstr("lb"  , pat(         v, v, n(3'b000),    v, n(7'b0000011)), instrLB(s));
  defineInstr("sb"  , pat(      v, v, v, n(3'b000),    v, n(7'b0100011)), instrSB(s));
  // Note the pattern size for c.li (16 bits as opposed to 32 bits for the
  // other instructions). Together with the instruction fetch behaviour, this is
  // enough to implement variable length instructions.
  defineInstr("c.li", pat(n(3'b010), v, v, v, n(2'b01)), instrC_LI(s));
  // The unknown instruction does not require a pattern.
  defineUnkInstr(unkInst(s));
  // XXX Uncomment to get multiple unknown instruction definition error.
  //defineUnkInstr(unkInst);

endmodule

// An example extension module with instruction overwritting
module [InstrDefModule] mkExtensionISA#(ArchState s) ();

  // A new semantic function intended to replace the conventional add.
  // Note that the architectural state is not an explicit argument as it is
  // implicitly accessible from within the module that recieves it as argument.
  // The previous style (explicit state argument of a toplevel function) is
  // prefered if the semantic function is to be imported in other BSV files.
  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
    printTLog($format("EXTENDED add %0d, %0d, %0d", rd, rs1, rs2));
    printTLog($format("regfile[%0d] <= %0d", rd, s.regfile[rs1] + s.regfile[rs2]));
    s.regfile[rd] <= s.regfile[rs1] + s.regfile[rs2];
    pcEpilogue(s);
  endaction;
  // The use of the same string "add" as in the mkBaseISA will cause
  // overwriting of the previous declaration.
  defineInstr("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  // XXX Uncomment to get multiple in module instruction definition error
  //defineInstr("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

endmodule

///////////////////////////////////
// Instanciate the ISA simulator //
////////////////////////////////////////////////////////////////////////////////

interface Probes;
  method Bit#(32) peekPC();
endinterface

module bidExample (Probes);

  // Initialize architectural state
  ArchState s <- mkState;

  // Instanciate ISA simulator
  // The first argument is the architectural state, the second argument is a
  // list of `InstrDeModule` modules defining the instructions. Instructions
  // defined in modules later in the list with the same name as earlier
  // definitions overwrite the definition.
  mkISASim(s, list(mkBaseISA, mkExtensionISA));

  /*
  // XXX TEST virtualize Reg
  Reg#(Bit#(32)) tmp <- mkReg(0);
  let r <- virtualize(asReg(tmp), 4);
  Reg#(Bit#(2)) cnt <- mkReg(0);
  rule count; cnt <= cnt + 1; endrule
  rule test0 (cnt == 0); r[0] <= 0; printTLog("test0"); endrule
  rule test1 (cnt == 1); r[1] <= 1; printTLog("test1"); endrule
  rule test2 (cnt == 2); r[2] <= 2; printTLog("test2"); endrule
  rule test3 (cnt == 3); r[3] <= 3; printTLog("test3"); endrule
  // XXX TEST
  */

  // Probing interface -- usefull when synthesizing
  method Bit#(32) peekPC() = s.pc;

endmodule

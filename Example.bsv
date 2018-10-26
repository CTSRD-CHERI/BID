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
import ConfigReg :: *;

// non standard packages
import BID :: *;
import BitPat :: *;
import BlueUtils :: *;
import BlueBasics :: *;
import ListExtra :: *;
import Recipe :: *;
import SourceSink :: *;

// Example use of the BID framework

////////////////////////////////////////
// Define common state and behaviours //
////////////////////////////////////////////////////////////////////////////////

// An architectural state of the example machine
typedef struct {
  // register file
  ArchRegFile#(32, Bit#(32)) regfile;
  // program counter
  ArchReg#(Bit#(32)) pc;
  // current instruction's byte length (useful for variable length instructions
  // support)
  Reg#(Bit#(32)) instByteSz;
  // instruction counter
  Reg#(UInt#(64)) instCnt;
  // interface to data memory
  Mem#(Bit#(32), Bit#(32)) dmem;
  // interface to instruction memory
  Mem#(Bit#(32), Bit#(32)) imem;
  // somme conflicting resource between normal flow and interlude
  Reg#(Bit#(32)) dummy;
} ArchState;

// ArchState initialization module
module mkState (ArchState);
  ArchState s;
  s.regfile <- mkRegFileZ;
  // Use the BID mkPC module that provides an interface with the conventional
  // _read() and _write() methods, together with a next() method capturing the
  // next value of the PC to help for instruction fetching.
  s.pc <- mkArchReg(0);
  // Use the BID mkBypassRegU module that provides a standard Reg interface
  // with the _read() returning the value written in the current cycle if
  // _write() was called, or the previous value otherwise.
  s.instByteSz <- mkBypassRegU;
  s.instCnt <- mkReg(0);
  // Use BID mkSharedMem2 module initialized with the "test-prog.hex" file's
  // content with a size of 4096 bytes.
  Mem#(Bit#(32), Bit#(32)) mem[2] <- mkSharedMem2(4096, Valid("test-prog.hex"));
  s.dmem = mem[0];
  s.imem = mem[1];
  s.dummy <- mkConfigRegU;
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
    Fmt str = $format("regfile\n");
    for (Integer i = 0; i < 6; i = i + 1) begin
      for (Integer j = 0; j < 5; j = j + 1) begin
        Bit#(5) ridx = fromInteger(i*5+j);
        str = str + $format("r[%0d]: 0x%8x\t", ridx, s.regfile.r[ridx]);
      end
      str = str + $format("\n");
    end
    str = str + $format("r[30]: 0x%8x\t", s.regfile.r[30]);
    str = str + $format("r[31]: 0x%8x", s.regfile.r[31]);
    str = str + $format("\npc = 0x%0x, instCnt = %0d", s.pc, s.instCnt);
    return str;
  endfunction
  function Action commit (ArchState s) = action
    s.pc.commit;
  endaction;

endinstance

////////////////////////////
// Define instruction set //
////////////////////////////////////////////////////////////////////////////////

// A few instructions (from the RISC-V ISA) semantic functions defined as
// toplevel functions, explicitly receiving the architectural state, and
// returning a single Action.
function Action instrADD(ArchState s, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
  s.regfile.r[rd] <= s.regfile.r[rs1] + s.regfile.r[rs2];
  printTLogPlusArgs("itrace", $format("add %0d, %0d, %0d", rd, rs1, rs2));
  printTLogPlusArgs("itrace", $format("regfile.r[%0d] <= 0x%0x", rd, s.regfile.r[rs1] + s.regfile.r[rs2]));
endaction;

function Action instrADDI(ArchState s, Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = action
  s.regfile.r[rd] <= s.regfile.r[rs1] + signExtend(imm);
  printTLogPlusArgs("itrace", $format("addi %0d, %0d, 0x%0x", rd, rs1, imm));
  printTLogPlusArgs("itrace", $format("regfile.r[%0d] <= 0x%0x", rd, s.regfile.r[rs1] + signExtend(imm)));
endaction;

function Action instrJAL(ArchState s, Bit#(1) imm20, Bit#(10) imm10_1, Bit#(1) imm11, Bit#(8) imm19_12, Bit#(5) rd) = action
  Bit#(32) imm = {signExtend(imm20),imm19_12,imm11,imm10_1,1'b0};
  s.pc <= s.pc + imm;
  s.regfile.r[rd] <= s.pc + s.instByteSz;
  printTLogPlusArgs("itrace", $format("jal %0d, 0x%0x", rd, imm));
endaction;

function Action instrBEQ (ArchState s, Bit#(1) imm12, Bit#(6) imm10_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(4) imm4_1, Bit#(1) imm11) = action
  Bit#(32) imm = {signExtend(imm12),imm11,imm10_5,imm4_1,1'b0};
  String taken = "not taken";
  if (s.regfile.r[rs1] == s.regfile.r[rs2]) begin
    s.pc <= s.pc + imm;
    taken = "taken";
  end
  printTLogPlusArgs("itrace", $format("beq %0d, %0d, 0x%0x -- %s", rs1, rs2, imm, taken));
  //TODO no pcEpilogue
endaction;

// A load byte instruction returning a List#(Action) to express interraction
// with a module with potential latency (the memory).
function List#(Action) instrLB(ArchState s, Bit#(12) imm, Bit#(5) rs1, Bit#(5) rd) = list(
  action
    Bit#(32) addr = s.regfile.r[rs1] + signExtend(imm);
    s.dmem.sink.put(tagged ReadReq {addr: addr, numBytes: 1});
    printTLogPlusArgs("itrace", $format("lb %0d, %0d, 0x%0x - step 1", rd, rs1, imm));
  endaction,
  action
    let rsp <- s.dmem.source.get();
    case (rsp) matches tagged ReadRsp .r: s.regfile.r[rd] <= r; endcase
    printTLogPlusArgs("itrace", $format("lb %0d, %0d, 0x%0x - step 2", rd, rs1, imm));
  endaction
);

function Action instrSB(ArchState s, Bit#(7) imm11_5, Bit#(5) rs2, Bit#(5) rs1, Bit#(5) imm4_0) = action
  Bit#(32) imm = {signExtend(imm11_5), imm4_0};
  Bit#(32) addr = s.regfile.r[rs1] + signExtend(imm);
  s.dmem.sink.put(tagged WriteReq {addr: addr, byteEnable: 'b1, data: s.regfile.r[rs2]});
  printTLogPlusArgs("itrace", $format("sb %0d, %0d, 0x%0x", rs1, rs2, imm));
endaction;

// An example of a compressed instruction. See the pattern definition for details.
function Action instrC_LI(ArchState s, Bit#(1) imm_5, Bit#(5) rd, Bit#(5) imm4_0) = action
  s.regfile.r[rd] <= signExtend({imm_5, imm4_0});
  printTLogPlusArgs("itrace", $format("c.li %0d, 0x%0x", rd, {imm_5, imm4_0}));
endaction;

// The unknown instruction, to be executed when no other instruction matched.
function List#(Action) unkInst(ArchState s, Bit#(MaxInstSz) inst) = list(
  printTLogPlusArgs("itrace", $format("Unknown instruction 0x%0x", inst)),
  noAction//printTLog($format("UNKNOWN INSTRUCTION 0x%0x", inst))
);

// Define architectural behaviour for instruction fetching
function Recipe instFetch(ArchState s, Sink#(Bit#(MaxInstSz)) snk) =
rPipe(rBlock(
  // put a reqd request to the instruction memory
  s.imem.sink.put(tagged ReadReq {
    addr: s.pc.late, // note the use of the "latet" interface of the PC register
    numBytes: 4 // request four bytes for an instruction
  }),
  // get the response from the instruction memory
  action
    let rsp <- s.imem.source.get(); // get the memory response
    case (rsp) matches
      tagged ReadRsp .val: begin
        // update the current instruction size
        s.instByteSz <= (val[1:0] == 2'b11) ? 4 : 2;
        snk.put(val);
      end
      default: snk.put(?);
    endcase
  endaction
));

// Define a BID InstrDefModule module to enable the use of defineInstEntry and
// defineUnkInstEntry. Note the BID State instance as a module argument.
module [ISADefModule] mkBaseISA#(ArchState s) ();

  // Use the BID defineInstEntry primitive to register an instruction with the
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
  defineInstEntry("add" , pat(n(7'b0), v, v, n(3'b000),    v, n(7'b0110011)), instrADD(s));
  defineInstEntry("addi", pat(         v, v, n(3'b000),    v, n(7'b0010011)), instrADDI(s));
  defineInstEntry("jal" , pat(                 v, v, v, v, v, n(7'b1101111)), instrJAL(s));
  defineInstEntry("beq" , pat(   v, v, v, v, n(3'b000), v, v, n(7'b1100011)), instrBEQ(s));
  defineInstEntry("lb"  , pat(         v, v, n(3'b000),    v, n(7'b0000011)), instrLB(s));
  defineInstEntry("sb"  , pat(      v, v, v, n(3'b000),    v, n(7'b0100011)), instrSB(s));
  // Note the pattern size for c.li (16 bits as opposed to 32 bits for the
  // other instructions). Together with the instruction fetch behaviour, this is
  // enough to implement variable length instructions.
  defineInstEntry("c.li", pat(n(3'b010), v, v, v, n(2'b01)), instrC_LI(s));
  // The unknown instruction does not require a pattern.
  defineUnkInstEntry(unkInst(s));
  // XXX Uncomment to get multiple unknown instruction definition error.
  //defineUnkInstEntry(unkInst(s));

  // initialization definition
  defineInitEntry(noAction);

  // instruction fetching definition
  defineFetchInstEntry(instFetch(s));

  // Prologue to prepare Next PC
  defineProEntry(action asIfc(s.pc.early) <= s.pc + s.instByteSz; endaction);

  // Prologue to write the dummy
  defineProEntry(action s.dummy <= 42; endaction);

  // Epilogue to display the dummy
  defineEpiEntry(action
    printTLogPlusArgs("itrace", $format("dummy = %0d", s.dummy));
  endaction);

  // Epilogue happening after each instruction.
  defineEpiEntry(action
    s.instCnt <= s.instCnt + 1;
    printTLogPlusArgs("itrace", "--------------- epilogue --------------");
  endaction);

  // some counter to make some events happen
  Reg#(Bit#(16)) cnt <- mkReg(0);
  rule count; cnt <= cnt + 1; endrule

  // this defines an interlude to happen between instructions when the guard is true
  defineInterEntry(Guarded { guard: (cnt[2:0] == 3'b100), val: action
    s.dummy <= 84;
    printTLog("!!! An interlude when cnt[2:0] == 3'b100 !!!");
  endaction });

endmodule

// An example extension module with instruction overwritting
module [ISADefModule] mkExtensionISA#(ArchState s) ();

  // A new semantic function intended to replace the conventional add.
  // Note that the architectural state is not an explicit argument as it is
  // implicitly accessible from within the module that recieves it as argument.
  // The previous style (explicit state argument of a toplevel function) is
  // prefered if the semantic function is to be imported in other BSV files.
  function Action instrADD(Bit#(5) rs2, Bit#(5) rs1, Bit#(5) rd) = action
    s.regfile.r[rd] <= s.regfile.r[rs1] + s.regfile.r[rs2];
    printTLogPlusArgs("itrace", $format("add %0d, %0d, %0d -- EXTENDED", rd, rs1, rs2));
    printTLogPlusArgs("itrace", $format("regfile.r[%0d] <= 0x%0x", rd, s.regfile.r[rs1] + s.regfile.r[rs2]));
  endaction;
  // The use of the same string "add" as in the mkBaseISA will cause
  // overwriting of the previous declaration.
  defineInstEntry("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

  // XXX Uncomment to get multiple in module instruction definition error
  //defineInstEntry("add",pat(n(7'b0), v, v, n(3'b0), v, n(7'b0110011)),instrADD);

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
  //mkISASim(s, list(mkBaseISA));

  // Probing interface -- usefull when synthesizing
  method Bit#(32) peekPC() = s.pc;

endmodule

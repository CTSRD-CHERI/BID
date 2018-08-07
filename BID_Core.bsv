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

import List :: *;
import FIFO :: *;
import Printf :: *;
import ModuleCollect :: *;

import Recipe :: *;
import BitPat :: *;

import BID_Collections :: *;
import BlueUtils :: *;

interface BIDProbes;
  method Bool latchedInst0Valid;
  method Bit#(MaxInstSz) latchedInst0;
  method Bool latchedInst1Valid;
  method Bit#(MaxInstSz) latchedInst1;
  method Bool doInstFetch0;
  method Bool doInstFetch1;
  method Bool peek_imem_fired;
  method Bool on_inst_commit_fired;
  method Bool fetch_next_instr_fired;
endinterface

//////////////////////////
// ISA simulator engine //
////////////////////////////////////////////////////////////////////////////////

module [Module] mkISASim#(
  state_t state, List#(function InstrDefModule#(ifc) mkMod (state_t st)) ms)
  (BIDProbes)
provisos (State#(state_t));

  // local signals and registers
  PulseWire instDone <- mkPulseWireOR;
  Reg#(Bool) doInstFetch[2] <- mkCReg(2, False);
  Reg#(Bool) doEpilogue[2]  <- mkCReg(2, False);
  Reg#(Bool) isReset <- mkReg(True);
  Reg#(Bit#(64)) instCommitted <- mkReg(0);
  Reg#(Maybe#(Bit#(MaxInstSz))) latchedInst[2] <- mkCReg(2, tagged Invalid);
  Reg#(Maybe#(Bit#(MaxInstSz))) inst = latchedInst[1];

  // harvest collections
  BIDCollections cols <- getCollections(state, ms);
  function Bool getGuard(Guarded#(Recipe) x) = x.guard;
  function Recipe getRecipe(Guarded#(Recipe) x) = x.val;

  // probing wires
  PulseWire w_peek_imem_fired <- mkPulseWire;
  PulseWire w_on_inst_commit_fired <- mkPulseWire;
  PulseWire w_fetch_next_instr_fired <- mkPulseWire;

  // reset rule
  //////////////////////////////////////////////////////////////////////////////

  rule on_reset (isReset);
    // fetch instruction on reset
    reqNextInst(state);
    // clear reseet after first cycle
    isReset <= False;
  endrule

  // instruction fetch rule
  //////////////////////////////////////////////////////////////////////////////
  rule fetch_next_instr (!isReset && doInstFetch[1]);
    w_fetch_next_instr_fired.send; // probing
    reqNextInst(state);
    doInstFetch[1] <= False;
    printTLogPlusArgs("BID_Core", $format("fetching next instr"));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // Peek at next instruction from imem
  //////////////////////////////////////////////////////////////////////////////
  rule peek_imem;
    w_peek_imem_fired.send; // probing
    Bit#(MaxInstSz) rsp <- getNextInst(state);
    latchedInst[0] <= tagged Valid rsp;
    printTLogPlusArgs("BID_Core", $format("received instruction response: ", fshow(rsp)));
  endrule
  rule debug_current_inst;
    printTLogPlusArgs("BID_Core", $format("current instructions: ", fshow(inst)));
  endrule

  // generate rules for instruction execution
  //////////////////////////////////////////////////////////////////////////////
  function getGuardedRecipe(x) = tpl_2(x)(fromMaybe(?, inst));
  List#(Guarded#(Recipe)) grs = map(getGuardedRecipe, cols.instrDefs);
  List#(Bool)    instGuards = map(getGuard, grs);
  List#(Recipe) instRecipes = map(getRecipe, grs);
  let allInsts <- compile(rOneMatch(instGuards, instRecipes, cols.unkInstrDef(fromMaybe(?, inst))));
  rule runInst (isValid(inst)); allInsts.start(); endrule

  // general rule triggered on instruction commit
  //////////////////////////////////////////////////////////////////////////////
  rule on_inst_commit (allInsts.isLastCycle);
    w_on_inst_commit_fired.send; // probing
    instCommitted <= instCommitted + 1; // TODO not count for unknown inst !!! XXX
    inst <= tagged Invalid;
    doEpilogue[0]  <= True;
    printTLogPlusArgs("BID_Core", $format("Committing instruction rule"));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // run epilogue actions
  //////////////////////////////////////////////////////////////////////////////
  Guarded#(Recipe) noEpilogue = Guarded {guard: True, val: rAct(noAction)};
  List#(Guarded#(Recipe)) epilogues = cons(noEpilogue, cols.epiDefs);
  let epilogue <- compile(rAllGuard(map(getGuard, epilogues), map(getRecipe, epilogues)));
  rule epilogueStart(doEpilogue[1]); epilogue.start(); endrule
  rule epilogueDone(epilogue.isLastCycle); doEpilogue[1]  <= False; endrule

  // run interlude
  //////////////////////////////////////////////////////////////////////////////
  List#(Bool)    interludeGuards = cons(False, map(getGuard, cols.interDefs));
  List#(Recipe) interludeRecipes = cons(rAct(noAction), map(getRecipe, cols.interDefs));
  let allInterludes <- compile(rOneMatchDelay(interludeGuards, interludeRecipes, rAct(noAction)));
  rule runInterlude (epilogue.isLastCycle); allInterludes.start(); endrule
  rule interludeDone(allInterludes.isLastCycle); doInstFetch[0]  <= True; endrule

  // Simulation only
  //////////////////////////////////////////////////////////////////////////////
  if (genC) begin
    Reg#(Bit#(64)) startTime <- mkReg(0);
    Reg#(Bit#(64)) countCycles <- mkReg(0);
    rule sim_reset (isReset);
      startTime <= unpack(sysTime);
    endrule
    rule count_cycles;
      countCycles <= countCycles + 1;
    endrule
    rule sim_speed (instCommitted[17:0] == 0);
      Bit#(64) t = unpack(sysTime) - startTime;
      Bit#(64) kips = (t > 0) ? (instCommitted / 1000) / t : 0;
      Bit#(64) kcps = (t > 0) ? (countCycles / 1000) / t : 0;
      printPlusArgs("BID_kips", $format("(%0d kips) executed %0d instructions in %0d seconds", kips, instCommitted, t));
      printPlusArgs("BID_kcps", $format("(%0d kcps) simulated %0d cycles in %0d seconds", kcps, countCycles, t));
      Bool doPrintIPC <- $test$plusargs("BID_ipc");
      if (doPrintIPC) printIPC (instCommitted, countCycles);
    endrule
  end

  // populate probes
  method latchedInst0 = fromMaybe(?,latchedInst[0]);
  method latchedInst0Valid = isValid(latchedInst[0]);
  method latchedInst1 = fromMaybe(?,latchedInst[1]);
  method latchedInst1Valid = isValid(latchedInst[1]);
  method doInstFetch0 = doInstFetch[0];
  method doInstFetch1 = doInstFetch[1];
  method peek_imem_fired = w_peek_imem_fired;
  method on_inst_commit_fired = w_on_inst_commit_fired;
  method fetch_next_instr_fired = w_fetch_next_instr_fired;

endmodule

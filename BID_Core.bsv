// 2018, Alexandre Joannou, University of Cambridge

import List :: *;
import FIFO :: *;
import Printf :: *;
import ModuleCollect :: *;

import Recipe :: *;
import BitPat :: *;

import BID_Interface :: *;
import BID_Collections :: *;
import BID_SimUtils :: *;

//////////////////////////
// ISA simulator engine //
////////////////////////////////////////////////////////////////////////////////

module [Module] mkISASim#(
  state_t state, List#(function InstrDefModule#(ifc) mkMod (state_t st)) ms) ()
provisos (State#(state_t));

  // local state
  PulseWire instDone <- mkPulseWireOR;
  Reg#(Bool) doInstFetch[2] <- mkCReg(2, False);
  Reg#(Bool) isReset <- mkReg(True);
  Reg#(Bit#(64)) instCommitted <- mkReg(0);

  // Peek at next instruction from imem
  Reg#(Maybe#(Bit#(MaxInstSz))) latchedInst[2] <- mkCReg(2, tagged Invalid);
  rule peek_imem;
    Bit#(MaxInstSz) rsp <- getNextInst(state);
    latchedInst[0] <= tagged Valid rsp;
    printTLogPlusArgs("BID_Core", $format("received instruction response: ", fshow(rsp)));
  endrule
  Reg#(Maybe#(Bit#(MaxInstSz))) inst = latchedInst[1];
  rule debug_current_inst;
    printTLogPlusArgs("BID_Core", $format("current instructions: ", fshow(inst)));
  endrule

  // harvest collections
  BIDCollections cols <- getCollections(state, ms);

  // generate rules for instruction execution
  //////////////////////////////////////////////////////////////////////////////
  function getGuardedRecipe(x) = tpl_2(x)(fromMaybe(?, inst));
  function Bool getGuard(Guarded#(Recipe) x) = x.guard;
  function Recipe getRecipe(Guarded#(Recipe) x) = x.val;
  List#(Guarded#(Recipe)) grs = map(getGuardedRecipe, cols.instrDefs);
  List#(Bool) guards = map(getGuard, grs);
  Bool isUnkInst = ! any(id, guards);
  List#(Tuple2#(Rules, RecipeFSM)) allInsts <- mapM(compileRules, map(getRecipe, grs));
  module mkRunInst#(Bool g, RecipeFSM m) ();
    rule runInst (g);
      m.start();
    endrule
    rule pulseInstDone (m.isLastCycle);
      instDone.send();
    endrule
  endmodule
  zipWithM(mkRunInst, guards, map(tpl_2, allInsts));
  // general rule triggered on instruction commit
  rule on_inst_commit (instDone);
    instCommitted <= instCommitted + 1;
    inst <= tagged Invalid;
    doInstFetch[0] <= True;
    printTLogPlusArgs("BID_Core", $format("Committing instruction rule"));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // generate rules for unknown instruction
  //////////////////////////////////////////////////////////////////////////////
  Tuple2#(Rules, RecipeFSM) unkInst <- compileRules(cols.unkInstrDef(fromMaybe(?, inst)));
  module mkRunUnkInst#(Bool g, RecipeFSM m) ();
    rule runUnkInst (g);
      m.start();
    endrule
    rule unkInstDone (m.isLastCycle);
      inst <= tagged Invalid;
      doInstFetch[0] <= True;
    endrule
  endmodule
  mkRunUnkInst(!isReset && isValid(inst) && isUnkInst, tpl_2(unkInst));

  // Add all compiled rules
  //////////////////////////////////////////////////////////////////////////////
  addRules(fold(rJoinMutuallyExclusive, cons(tpl_1(unkInst), map(tpl_1, allInsts))));

  // other rules
  //////////////////////////////////////////////////////////////////////////////

  rule on_reset (isReset);
    // fetch instruction on reset
    reqNextInst(state);
    // clear reseet after first cycle
    isReset <= False;
  endrule

  // fetch next instruction on doInstFetch
  rule fetch_next_instr (!isReset && doInstFetch[1]);
    reqNextInst(state);
    doInstFetch[1] <= False;
    printTLogPlusArgs("BID_Core", $format("fetching next instr"));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // print sim speed
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

endmodule

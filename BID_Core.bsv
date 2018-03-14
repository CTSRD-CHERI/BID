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
  FullMem#(addr_t, inst_t, data_t) mem,
  archstate_t archState,
  List#(function InstrDefModule#(ifc) mkMod (archstate_t st, Mem#(addr_t, data_t) dmem)) ms) ()
provisos (
  ArchState#(archstate_t),
  Bits#(inst_t, MaxInstSz),
  Bits#(addr_t, addr_sz),
  FShow#(inst_t)
);

  // local state
  PulseWire instDone <- mkPulseWireOR;
  Reg#(Bool) doInstFetch[2] <- mkCReg(2, False);
  Reg#(Bool) isReset <- mkReg(True);
  Reg#(Bit#(64)) instCommitted <- mkReg(0);

  // Peek at next instruction from imem
  Reg#(Maybe#(Bit#(MaxInstSz))) latchedInst[2] <- mkCReg(2, tagged Invalid);
  rule peek_imem;
    inst_t rsp <- mem.inst.get();
    latchedInst[0] <= tagged Valid pack(rsp);
    printTLogPlusArgs("BID_Core", $format("received instruction response: ", fshow(rsp)));
  endrule
  Reg#(Maybe#(Bit#(MaxInstSz))) inst = latchedInst[1];
  rule debug_current_inst;
    printTLogPlusArgs("BID_Core", $format("current instructions: ", fshow(inst)));
  endrule

  // harvest collections
  BIDCollections cols <- getCollections(mem, archState, ms);

  // generate rules for instruction execution
  //////////////////////////////////////////////////////////////////////////////
  function getGuardedRecipe(x) = tpl_2(x)(fromMaybe(?, inst));
  List#(GuardedRecipe) grs = map(getGuardedRecipe, cols.instrDefs);
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

  // clear reseet after first cycle
  rule clear_reset (isReset);
    isReset <= False;
  endrule

  // fetch instruction on reset
  rule fetch_reset (isReset);
    mem.inst.reqNext();
  endrule

  // fetch next instruction on doInstFetch
  rule fetch_next_instr (!isReset && doInstFetch[1]);
    mem.inst.reqNext();
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

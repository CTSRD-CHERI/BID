// 2018, Alexandre Joannou, University of Cambridge

import List :: *;
import FIFO :: *;
import Printf :: *;
import ModuleCollect :: *;

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
  List#(function InstrDefModule#(inst_sz, ifc) mkMod (archstate_t st, Mem#(addr_t, data_t) dmem)) ms) ()
provisos (
  ArchState#(archstate_t),
  Bits#(inst_t, inst_sz), Div#(inst_sz, BitsPerByte, inst_byte_sz),
  Bits#(addr_t, addr_sz),
  FShow#(inst_t)
);

  // local state
  Reg#(UInt#(8)) stepCounter <- mkReg(0);
  PulseWire instCommitting <- mkPulseWire;
  Reg#(Bool) doInstFetch[2] <- mkCReg(2, False);
  Reg#(Bool) isReset <- mkReg(True);
  Reg#(Bit#(64)) instCommitted <- mkReg(0);

  // Peek at next instruction from imem
  Reg#(Maybe#(Bit#(inst_sz))) latchedInst[2] <- mkCReg(2, tagged Invalid);
  rule peek_imem;
    inst_t rsp <- mem.inst.get();
    latchedInst[0] <= tagged Valid pack(rsp);
    printTLogPlusArgs("BID_Core", $format("received instruction response: ", fshow(rsp)));
  endrule
  Reg#(Maybe#(Bit#(inst_sz))) inst = latchedInst[1];
  rule debug_current_inst;
    printTLogPlusArgs("BID_Core", $format("current instructions: ", fshow(inst)));
  endrule

  // harvest collections
  BIDCollections#(inst_sz) cols <- getCollections(mem, archState, ms);

  // generate rules for instruction execution
  //////////////////////////////////////////////////////////////////////////////
  function getGuardedAction(x) = tpl_2(x)(fromMaybe(?, inst));
  List#(GuardedActions) gacts = map(getGuardedAction, cols.instrDefs);
  function Bool getGuard(GuardedActions ga) = ga.guard;
  // Bluespec confuses the list "or" function with the "or" keyword
  // escape it with "\" before and explicitly put a " " after
  // Possible alternative: Bool isUnkInst = ! any(id, map(getGuard, gacts));
  Bool isUnkInst = ! \or (map(getGuard, gacts));
  let gactsLen = length(gacts);
  for (Integer i = 0; i < gactsLen; i = i + 1) begin
    GuardedActions ga = head(gacts);
    let nbSteps = length(ga.body);
    for (Integer j = 0; j < nbSteps; j = j + 1) begin
      let body = head(ga.body);
      rule instr_body (!isReset && isValid(inst) && stepCounter == fromInteger(j) && ga.guard);
        printTLogPlusArgs("BID_Core", $format("-------------------- step %0d ------------------", stepCounter));
        printTLogPlusArgs("BID_Core", $format("inst: 0x%0x", fromMaybe(?, inst)));
        printLogPlusArgs("BID_Core", lightReport(archState));
        body;
        if (stepCounter == fromInteger(nbSteps - 1)) begin
          stepCounter <= 0;
          instCommitted <= instCommitted + 1;
          inst <= tagged Invalid;
          instCommitting.send();
          doInstFetch[0] <= True;
        end else stepCounter <= fromInteger(j + 1);
      endrule
      ga.body = tail(ga.body);
    end
    gacts = tail(gacts);
  end

  // generate rules for unknown instruction
  //////////////////////////////////////////////////////////////////////////////
  List#(Action) unkInst = cols.unkInstrDef(fromMaybe(?, inst));
  let unkInstLen = length(unkInst);
  for (Integer i = 0; i < unkInstLen; i = i + 1) begin
    let body = head(unkInst);
    rule unknown_instr_rule (!isReset && isValid(inst) && stepCounter == fromInteger(i) && isUnkInst);
      body;
      if (stepCounter == fromInteger(unkInstLen - 1)) begin
        stepCounter <= 0;
        doInstFetch[0] <= True;
      end else stepCounter <= fromInteger(i + 1);
    endrule
    unkInst = tail(unkInst);
  end

  // other rules
  //////////////////////////////////////////////////////////////////////////////

  // general rule triggered on instruction commit
  rule on_inst_commit (instCommitting);
    printTLogPlusArgs("BID_Core", $format("Committing instruction rule"));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

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

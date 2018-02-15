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
  Mem#(addr_t, inst_t, data_t) mem,
  ArchStateDefModule#(addr_sz, archstate_t) mstate,
  List#(function InstrDefModule#(inst_sz, ifc) mkMod (archstate_t st, DMem#(addr_t, data_t) dmem)) ms) ()
provisos (
  ArchState#(archstate_t),
  Bits#(inst_t, inst_sz),
  Bits#(addr_t, addr_sz)
);

  // local state
  Reg#(UInt#(8)) stepCounter <- mkReg(0);
  PulseWire instCommitting <- mkPulseWire;
  PulseWire doInstFetch <- mkPulseWire;
  Reg#(Bool) isReset <- mkReg(True);
  Reg#(UInt#(64)) instCommitted <- mkReg(0);

  // Peek at next instruction from imem
  Reg#(Maybe#(Bit#(inst_sz))) latchedInst[2] <- mkCReg(2, tagged Invalid);
  rule peek_imem;
    latchedInst[0] <= tagged Valid pack(mem.inst.nextInst);
  endrule
  Reg#(Maybe#(Bit#(inst_sz))) inst = latchedInst[1];

  // harvest collections
  BIDCollections#(addr_sz, inst_sz, archstate_t)
    cols <- getCollections(mem, mstate, ms);

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
        printLogPlusArgs("BID_Core", lightReport(cols.archState));
        body;
        if (stepCounter == fromInteger(nbSteps - 1)) begin
          stepCounter <= 0;
          instCommitted <= instCommitted + 1;
          inst <= tagged Invalid;
          instCommitting.send();
          doInstFetch.send();
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
        doInstFetch.send();
      end else stepCounter <= fromInteger(i + 1);
    endrule
    unkInst = tail(unkInst);
  end

  // other rules
  //////////////////////////////////////////////////////////////////////////////

  // general rule triggered on instruction commit
  rule on_inst_commit (instCommitting);
    printTLogPlusArgs("BID_Core", $format("Committing instruction rule"));
    List#(Action) as = cols.onInstCommits;
    let onInstCommitsLen = length(cols.onInstCommits);
    for (Integer i = 0; i < onInstCommitsLen; i = i + 1) begin
      head(as);
      as = tail(as);
    end
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // clear reseet after first cycle
  rule clear_reset (isReset);
    isReset <= False;
  endrule

  // fetch instruction on reset
  rule fetch_reset (isReset);
    mem.inst.fetchInst(unpack(cols.archPC));
  endrule

  // fetch next instruction on doInstFetch
  rule fetch_next_instr (!isReset && doInstFetch);
    mem.inst.fetchInst(unpack(cols.archPC));
    printTLogPlusArgs("BID_Core", $format("fetching next instr from 0x%0x", cols.archPC));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // print sim speed
  if (genC) begin
    Reg#(UInt#(64)) startTime <- mkReg(0);
    rule sim_reset (isReset);
      startTime <= unpack(sysTime);
    endrule
    rule sim_speed (pack(instCommitted)[17:0] == 0);
      UInt#(64) t = unpack(sysTime) - startTime;
      UInt#(64) kips = (t > 0) ? (instCommitted / 1000) / t : 0;
      printPlusArgs("BID_kips", $format("(%0d kips) executed %0d instructions in %0d seconds ", kips, instCommitted, t));
    endrule
  end

endmodule

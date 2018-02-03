// 2018, Alexandre Joannou, University of Cambridge

import List :: *;
import FIFO :: *;
import Assert :: *;
import Printf :: *;
import ModuleCollect :: *;

import BitPat :: *;

import BID_Interface :: *;
import BID_ModuleCollect :: *;
import BID_SimUtils :: *;

//////////////////////////
// ISA simulator engine //
////////////////////////////////////////////////////////////////////////////////

module [Module] mkISASim#(
  Mem#(addr_t, inst_t, data_t) mem,
  ArchStateDefModule#(addr_sz, archstate_t#(addr_sz)) mstate,
  List#(function InstrDefModule#(inst_sz, ifc) mkMod (archstate_t#(addr_sz) st, DMem#(addr_t, data_t) dmem)) ms) ()
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
  PulseWire instDecoded <- mkPulseWireOR;

  // Peek at next instruction from imem
  Bit#(inst_sz) inst = pack(mem.inst.nextInst);

  // harvest state
  //////////////////////////////////////////////////////////////////////////////
  IWithCollection#(ISAStateDfn#(addr_sz), archstate_t#(addr_sz)) s <- exposeCollection(mstate);
  // architectural PC
  let archPCs = concat(map(getArchPC, s.collection()));
  let lenArchPCs = length(archPCs);
  //XXX must build with -check-assert to detect this error !
  staticAssert(lenArchPCs == 1, sprintf("There must be exactly one architectural PC defined with mkPC (%0d detected)", lenArchPCs));
  let archPC = head(archPCs);
  // on-instruction-commit actions
  let onInstCommits = concat(map(getOnInstCommit, s.collection()));
  let onInstCommitsLen = length(onInstCommits);

  // harvest instructions
  //////////////////////////////////////////////////////////////////////////////
  // apply state and mem, and get collections for each module
  function applyStateAndMem (g) = g(s.device, mem.data);
  let cs <- mapM(exposeCollection,map(applyStateAndMem, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(List#(ISAInstDfn#(inst_sz))) isaInstrModuleDefs = map(getItems, cs);
  // split definitions per type
  let instrModuleDefs = map(sortBy(cmpInstrDefn),map(getInstDefs, isaInstrModuleDefs));
  let unkInstrModuleDefs = map(getUnkInstDefs, isaInstrModuleDefs);
  // instruction definitions
  List#(InstrDefn#(inst_sz)) instrDefsTuples = mergeInstrDefns(instrModuleDefs);
  List#(function GuardedActions f(Bit#(inst_sz) instr)) instrDefs = map(tpl_2, instrDefsTuples);
  let instrDefsLen = length(instrDefs);
  // unknown instruction definitions
  let unkInstrDefs = concat(unkInstrModuleDefs);
  let unkInstrDefsLen = length(unkInstrDefs);
  //XXX must build with -check-assert to detect this error !
  staticAssert(unkInstrDefsLen == 1, sprintf("There must be exactly one unknown instruction behaviour defined with defineUnkInst (%0d detected)", unkInstrDefsLen));
  List#(Action) unkInst = head(unkInstrDefs)(inst);

  // generate rules for instruction execution
  //////////////////////////////////////////////////////////////////////////////
  for (Integer i = 0; i < instrDefsLen; i = i + 1) begin
    let f = head(instrDefs);
    GuardedActions acts = f(inst);
    let nbSteps = length(acts.body);
    for (Integer j = 0; j < nbSteps; j = j + 1) begin
      let body = head(acts.body);
      rule instr_rule (!isReset && stepCounter == fromInteger(j) && acts.guard);
        instDecoded.send();
        printTLogPlusArgs("BID_Core", $format("-------------------- step %0d ------------------", stepCounter));
        printTLogPlusArgs("BID_Core", $format("inst: 0x%0x", inst));
        printLogPlusArgs("BID_Core", lightReport(s.device));
        body;
        if (stepCounter == fromInteger(nbSteps - 1)) begin
          stepCounter <= 0;
          instCommitted <= instCommitted + 1;
          instCommitting.send();
          doInstFetch.send();
        end else stepCounter <= fromInteger(j + 1);
      endrule
      acts.body = tail(acts.body);
    end
    instrDefs = tail(instrDefs);
  end

  // generate rules for unknown instruction
  //////////////////////////////////////////////////////////////////////////////
  let unkInstLen = length(unkInst);
  for (Integer i = 0; i < unkInstLen; i = i + 1) begin
    let body = head(unkInst);
    rule unknown_instr_rule (!isReset && stepCounter == fromInteger(i) && ! instDecoded);
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
    //let _ <- mapM_(id,onInstCommits);
    List#(Action) as = onInstCommits;
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
    mem.inst.fetchInst(unpack(archPC));
  endrule

  // fetch next instruction on doInstFetch
  rule fetch_next_instr (!isReset && doInstFetch);
    mem.inst.fetchInst(unpack(archPC));
    printTLogPlusArgs("BID_Core", $format("fetching next instr from 0x%0x", archPC));
    printLogPlusArgs("BID_Core", "==============================================");
  endrule

  // print sim speed
  if (genC) begin
    Reg#(UInt#(64)) startTime <- mkReg(0);
    rule sim_reset (isReset);
      startTime <= unpack(sysTime);
    endrule
    rule sim_speed (pack(instCommitted)[12:0] == 0);
      UInt#(64) t = unpack(sysTime) - startTime;
      UInt#(64) kips = (t > 0) ? (instCommitted / 1000) / t : 0;
      printPlusArgs("BID_kips", $format("(%0d kips) executed %0d instructions in %0d seconds ", kips, instCommitted, t));
    endrule
  end

endmodule

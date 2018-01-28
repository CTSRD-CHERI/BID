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
  IMem#(imem_addr, inst) imem,
  world_t w,
  ArchStateDefModule#(n, archstate_t#(n)) mstate,
  List#(function InstrDefModule#(inst_sz, ifc) mkMod (archstate_t#(n) st, world_t wo)) ms) ()
provisos (
  ArchState#(archstate_t),
  World#(world_t),
  Bits#(inst, inst_sz),
  Bits#(imem_addr, n)
);

  // local state
  Reg#(UInt#(8)) stepCounter <- mkReg(0);
  PulseWire instCommitting <- mkPulseWire;
  Reg#(Bool) isReset <- mkReg(True);
  Reg#(UInt#(64)) instCommitted <- mkReg(0);

  // harvest state
  IWithCollection#(ArchStateDfn#(n), archstate_t#(n)) s <- exposeCollection(mstate);
  let archPCs = concat(map(getArchPC, s.collection()));
  let lenArchPCs = length(archPCs);
  //XXX must build with -check-assert to detect this error !
  staticAssert(lenArchPCs == 1, sprintf("There must be exactly one architectural PC defined with mkPC (%0d detected)", lenArchPCs));
  let archPC = head(archPCs);
  // harvest on inst commit actions
  let onInstCommits = concat(map(getOnInstCommit, s.collection()));
  let onInstCommitsLen = length(onInstCommits);

  // harvest instructions
  function applyStateAndWorld (g) = g(s.device, w);
  let cs <- mapM(exposeCollection,List::map(applyStateAndWorld, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(InstrDefn#(inst_sz)) instrDefs = concat(map(getItems, cs));

  // generate rules for instruction execution
  Integer n0 = length(instrDefs);
  for (Integer i = 0; i < n0; i = i + 1) begin
    let f = List::head(instrDefs);
    GuardedActions acts = f(pack(imem.nextInst));
    Integer n1 = length(acts.body);
    for (Integer j = 0; j < n1; j = j + 1) begin
      let body = List::head(acts.body);
      rule instr_rule (!isReset && stepCounter == fromInteger(j) && acts.guard);
        printTLogPlusArgs("BID_Core", $format("-------------------- step %0d ------------------", stepCounter));
        printLogPlusArgs("BID_Core", lightReport(s.device));
        body;
        if (stepCounter == fromInteger(n1 - 1)) begin
          stepCounter <= 0;
          instCommitted <= instCommitted + 1;
          instCommitting.send();
        end else stepCounter <= fromInteger(j + 1);
      endrule
      acts.body = List::tail(acts.body);
    end
    instrDefs = List::tail(instrDefs);
  end

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
    imem.fetchInst(unpack(archPC));
  endrule
  // fetch next instruction on instruction commit
  rule fetch_next_instr (!isReset && instCommitting);
    imem.fetchInst(unpack(archPC));
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

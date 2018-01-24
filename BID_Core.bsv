// 2018, Alexandre Joannou, University of Cambridge

import List :: *;
import FIFO :: *;
import Assert :: *;
import Printf :: *;
import ModuleCollect :: *;

import BitPat :: *;

import BID_Interface :: *;
import BID_ModuleCollect :: *;

//////////////////////////
// ISA simulator engine //
////////////////////////////////////////////////////////////////////////////////

module [Module] mkISASim#(
  InstStream#(n) instStream,
  world_t w,
  ArchStateDefModule#(m, archstate_t#(m)) mstate,
  List#(function InstrDefModule#(n, ifc) mkMod (archstate_t#(m) st, world_t wo)) ms) ()
  provisos (ArchState#(archstate_t), World#(world_t));

  // local state
  Reg#(UInt#(8)) stepCounter <- mkReg(0);
  PulseWire fetchNextInstr <- mkPulseWire;

  // harvest state
  IWithCollection#(ArchStateDfn#(m), archstate_t#(m)) s <- exposeCollection(mstate);
  let archPCs = concat(map(getArchPC, s.collection()));
  let lenArchPCs = length(archPCs);
  //XXX must build with -check-assert to detect this error !
  staticAssert(lenArchPCs == 1, sprintf("There must be exactly one architectural PC defined with mkPC (%0d detected)", lenArchPCs));
  let archPC = head(archPCs);

  // harvest instructions
  function applyStateAndWorld (g) = g(s.device, w);
  let cs <- mapM(exposeCollection,List::map(applyStateAndWorld, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(InstrDefn#(n)) instrDefs = concat(map(getItems, cs));

  // generate rules for instruction execution
  Integer n0 = length(instrDefs);
  for (Integer i = 0; i < n0; i = i + 1) begin
    let f = List::head(instrDefs);
    GuardedActions acts = f(instStream.peekInst());
    Integer n1 = length(acts.body);
    for (Integer j = 0; j < n1; j = j + 1) begin
      let body = List::head(acts.body);
      rule instr_rule (stepCounter == fromInteger(j) && acts.guard);
        $display("--------------- step %0d @%0t --------------", stepCounter, $time);
        $display(lightReport(s.device));
        body;
        if (stepCounter == fromInteger(n1 - 1)) begin
          stepCounter <= 0;
          instStream.nextInst();
          fetchNextInstr.send();
          $display("==============================================");
        end else stepCounter <= fromInteger(j + 1);
      endrule
      acts.body = List::tail(acts.body);
    end
    instrDefs = List::tail(instrDefs);
  end

  // rule to fetch the next instruction
  rule fetch_next_instr (fetchNextInstr);
    $display("@%0t -- fetching next instr from 0x%0x", $time, archPC);
    $display("==============================================");
  endrule

endmodule

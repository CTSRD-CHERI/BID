// 2018, Alexandre Joannou, University of Cambridge

import BitPat::*;
import List::*;
import FIFO :: *;
import ModuleCollect::*;

typedef Bool World;

typedef function GuardedActions f(Bit#(n) subject) InstrDefn#(numeric type n);
typedef ModuleCollect#(InstrDefn#(n), ifc) InstrDefModule#(numeric type n, type ifc);
typedef InstrDefModule#(32, ifc) Instr32DefModule#(type ifc);

typeclass DefineInstr#(type a);
  module [InstrDefModule#(n)] defineInstr#(BitPat#(n, t, a) p, function t f)();
endtypeclass

instance DefineInstr#(Action);
  module [InstrDefModule#(n)] defineInstr#(BitPat#(n, t, Action) p, function t f)();
    function flipPat(x);
      Tuple2#(Bool, Action) res = p(x, f);
      return GuardedActions { guard: tpl_1(res), body: List::cons(tpl_2(res), Nil) };
    endfunction
    addToCollection(flipPat);
  endmodule
endinstance

instance DefineInstr#(List#(Action));
  module [InstrDefModule#(n)] defineInstr#(BitPat#(n, t, List#(Action)) p, function t f)();
    function flipPat(x);
      Tuple2#(Bool, List#(Action)) res = p(x, f);
      return GuardedActions { guard: tpl_1(res), body: tpl_2(res) };
    endfunction
    addToCollection(flipPat);
  endmodule
endinstance

typedef enum { Prologue, Instruction, Epilogue } SimStage deriving (Bits, Eq);
module [Module] mkISASim#(FIFO#(Bit#(n)) instq, List#(function InstrDefModule#(n, ifc) mkMod (World wo)) ms, function Action epilogue (World w)) ();

  Reg#(UInt#(8)) stepCounter <- mkReg(0);
  Reg#(SimStage) simStage <- mkReg(Instruction);
  World w = True;

  function applyWorld (g) = g(w);
  let cs <- mapM(exposeCollection,List::map(applyWorld, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(InstrDefn#(n)) instrDefs = concat(map(getItems, cs));
  Integer n0 = length(instrDefs);
  for (Integer i = 0; i < n0; i = i + 1) begin
    let f = List::head(instrDefs);
    GuardedActions acts = f(instq.first());
    Integer n1 = length(acts.body);
    for (Integer j = 0; j < n1; j = j + 1) begin
      let body = List::head(acts.body);
      rule generatedRule (simStage == Instruction && stepCounter == fromInteger(j) && acts.guard);
        $display("--------------- step %0d @ %0t --------------", stepCounter, $time);
        body;
        if (stepCounter == fromInteger(n1 - 1)) begin
          stepCounter <= 0;
          simStage <= Epilogue;
        end else stepCounter <= fromInteger(j + 1);
      endrule
      acts.body = List::tail(acts.body);
    end
    instrDefs = List::tail(instrDefs);
  end
  rule do_epilogue (simStage == Epilogue);
    $display("--------------- epilogue @ %0t --------------", $time);
    epilogue(w);
    simStage <= Instruction;
    instq.deq();
    $display("=====================================================================");
  endrule
endmodule

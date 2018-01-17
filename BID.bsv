// 2018, Alexandre Joannou, University of Cambridge

import BitPat::*;
import List::*;
import ModuleCollect::*;

typedef Bool World;

typedef function GuardedAction f(Bit#(n) subject) InstrDefn#(numeric type n);
typedef ModuleCollect#(InstrDefn#(n), ifc) InstrDefModule#(numeric type n, type ifc);
typedef InstrDefModule#(32, ifc) Instr32DefModule#(type ifc);

module [InstrDefModule#(n)] defineInstr#(BitPat#(n, t, Action) p, function t f)();
  function flipPat(x);
    Tuple2#(Bool, Action) res = p(x, f);
    return GuardedAction { guard: tpl_1(res), body: tpl_2(res) };
  endfunction
  addToCollection(flipPat);
endmodule

module [Module] mkISASim#(Bit#(n) instr, List#(function InstrDefModule#(n, ifc) mkMod (World wo)) ms) ();
  World w = True;
  function applyWorld (g) = g(w);
  let cs <- mapM(exposeCollection,List::map(applyWorld, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(InstrDefn#(n)) instrDefs = concat(map(getItems, cs));
  Integer n = length(instrDefs);
  for (Integer i = 0; i < n; i = i + 1) begin
    let f = List::head(instrDefs);
    GuardedAction act = f(instr);
    rule generatedRule (act.guard);
      act.body;
    endrule
    instrDefs = List::tail(instrDefs);
  end
endmodule

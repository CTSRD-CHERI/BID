// 2018, Alexandre Joannou, University of Cambridge

import BitPat::*;
import List::*;
import FIFO :: *;
import ModuleCollect::*;

// Nice friendly list constructor lifted from Bluecheck's sources

typeclass MkList#(type a, type b) dependencies (a determines b);
  function a mkList(List#(b) acc);
endtypeclass

instance MkList#(List#(b), b);
  function List#(b) mkList(List#(b) acc) = List::reverse(acc);
endinstance

instance MkList#(function a f(b val), b) provisos (MkList#(a, b));
  function mkList(acc, val) = mkList(Cons(val, acc));
endinstance

function a list() provisos (MkList#(a, b));
  return mkList(Nil);
endfunction

/////////////////
// state types //
////////////////////////////////////////////////////////////////////////////////

typeclass ArchState#(type a);
  module initArchState(a);
  function Fmt lightReport (a s);
  function Fmt fullReport (a s);
endtypeclass

typedef Bool World;

///////////////////////////////////
// Types to harvest instructions //
////////////////////////////////////////////////////////////////////////////////

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

//////////////////////////
// ISA simulator engine //
////////////////////////////////////////////////////////////////////////////////

module [Module] mkISASim#(
  FIFO#(Bit#(n)) instq,
  aState s,
  List#(function InstrDefModule#(n, ifc) mkMod (aState st, World wo)) ms) ()
  provisos (ArchState#(aState));

  // local state
  Reg#(UInt#(8)) stepCounter <- mkReg(0);
  World w = True;

  // harvest instructions
  function applyStateAndWorld (g) = g(s,w);
  let cs <- mapM(exposeCollection,List::map(applyStateAndWorld, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(InstrDefn#(n)) instrDefs = concat(map(getItems, cs));

  // generate rules for instruction execution
  Integer n0 = length(instrDefs);
  for (Integer i = 0; i < n0; i = i + 1) begin
    let f = List::head(instrDefs);
    GuardedActions acts = f(instq.first());
    Integer n1 = length(acts.body);
    for (Integer j = 0; j < n1; j = j + 1) begin
      let body = List::head(acts.body);
      rule generatedRule (stepCounter == fromInteger(j) && acts.guard);
        $display("--------------- step %0d @%0t --------------", stepCounter, $time);
        $display(lightReport(s));
        body;
        if (stepCounter == fromInteger(n1 - 1)) begin
          stepCounter <= 0;
          instq.deq();
          $display("==============================================");
        end else stepCounter <= fromInteger(j + 1);
      endrule
      acts.body = List::tail(acts.body);
    end
    instrDefs = List::tail(instrDefs);
  end

endmodule

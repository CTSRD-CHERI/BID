// 2018, Alexandre Joannou, University of Cambridge

import Recipe :: *;
import BitPat :: *;

import List :: *;
import Printf :: *;
import ModuleCollect :: *;

import BID_SimUtils :: *;
import BID_Interface :: *;

//////////////////////////
// Simulator state type //
////////////////////////////////////////////////////////////////////////////////

typeclass State#(type a);
  function Fmt lightReport (a s);
  function Fmt fullReport (a s);
  function Action reqNextInst(a s);
  function ActionValue#(Bit#(MaxInstSz)) getNextInst(a s);
endtypeclass

///////////////////
// GuardedRecipe //
////////////////////////////////////////////////////////////////////////////////
typedef struct {
  Bool guard;
  Recipe recipe;
} GuardedRecipe;
function Bool getGuard(GuardedRecipe x) = x.guard;
function Recipe getRecipe(GuardedRecipe x) = x.recipe;

///////////////////////////////////
// Types to harvest instructions //
////////////////////////////////////////////////////////////////////////////////

`ifdef MAX_INST_SZ
typedef MAX_INST_SZ MaxInstSz;
`else
typedef 32 MaxInstSz;
`endif

typedef Tuple2#(String, function GuardedRecipe f(Bit#(MaxInstSz) subject)) InstrDefn;
typedef function Recipe f(Bit#(MaxInstSz) subject) UnkInstrDefn;

typedef union tagged {
  InstrDefn InstDef;
  UnkInstrDefn UnkInstDef;
} ISAInstDfn;

function List#(InstrDefn) getInstDef (ISAInstDfn e) =
  e matches tagged InstDef .x ? cons(x, Nil) : Nil;
function List#(UnkInstrDefn) getUnkInstDef (ISAInstDfn e) =
  e matches tagged UnkInstDef .x ? cons(x, Nil) : Nil;
function List#(InstrDefn) getInstDefs(List#(ISAInstDfn) defs) =
  concat(map(getInstDef,defs));
function List#(UnkInstrDefn) getUnkInstDefs(List#(ISAInstDfn) defs) =
  concat(map(getUnkInstDef,defs));

typedef ModuleCollect#(ISAInstDfn, ifc) InstrDefModule#(type ifc);

////////////////////////////////////////////////////////////////////////////////

typeclass DefineInstr#(type a);
  module [InstrDefModule]
    defineInstr#(String name, BitPat#(n, t, a) p, function t f) ()
    provisos (Add#(a__, n, MaxInstSz));
endtypeclass

instance DefineInstr#(Action);
  module [InstrDefModule] defineInstr#(String name, BitPat#(n, t, Action) p, function t f)()
  provisos (Add#(a__, n, MaxInstSz));
    function GuardedRecipe flipPat(Bit#(MaxInstSz) x);
      Bit#(n) subject = truncate(x);
      Tuple2#(Bool, Action) res = p(subject, f);
      return GuardedRecipe { guard: tpl_1(res), recipe: rAct(tpl_2(res)) };
    endfunction
    addToCollection(InstDef(tuple2(name,flipPat)));
  endmodule
endinstance

instance DefineInstr#(List#(Action));
  module [InstrDefModule] defineInstr#(String name, BitPat#(n, t, List#(Action)) p, function t f)()
  provisos (Add#(a__, n, MaxInstSz));
    function flipPat(x);
      Tuple2#(Bool, List#(Action)) res = p(truncate(x), f);
      return GuardedRecipe { guard: tpl_1(res), recipe: rPar(map(rAct, tpl_2(res))) };
    endfunction
    addToCollection(InstDef(tuple2(name, flipPat)));
  endmodule
endinstance

instance DefineInstr#(Recipe);
  module [InstrDefModule] defineInstr#(String name, BitPat#(n, t, Recipe) p, function t f)()
  provisos (Add#(a__, n, MaxInstSz));
    function flipPat(x);
      Tuple2#(Bool, Recipe) res = p(truncate(x), f);
      return GuardedRecipe { guard: tpl_1(res), recipe: tpl_2(res) };
    endfunction
    addToCollection(InstDef(tuple2(name, flipPat)));
  endmodule
endinstance

function List#(InstrDefn) checkInstrDefns(List#(InstrDefn) ls);
  function check(a,b) = (tpl_1(a) != tpl_1(b)) ?
    b : error(sprintf("Multiple definition of the %s instruction within the same module.", tpl_1(a)));
  if (ls matches Nil) return Nil;
  else return cons(head(ls), zipWith(check, ls, tail(ls)));
endfunction

function Ordering cmpInstrDefn(InstrDefn x, InstrDefn y);
  function Ordering cmpCharList(List#(Char) a, List#(Char) b);
    Ordering ord;
    if (a == Nil) ord = (b == Nil) ? EQ : LT;
    else if (b == Nil) ord = GT; else begin
      let tmp = compare(head(a), head(b));
      ord = (tmp == EQ) ? cmpCharList(tail(a), tail(b)) : tmp;
    end
    return ord;
  endfunction
  return cmpCharList(stringToCharList(tpl_1(x)), stringToCharList(tpl_1(y)));
endfunction

function List#(InstrDefn) mergeInstrDefns(List#(List#(InstrDefn)) ls);
  function List#(InstrDefn) merge2(List#(InstrDefn) a, List#(InstrDefn) b);
    if (a matches Nil) return b;
    else if (b matches Nil) return a;
    else case (cmpInstrDefn(head(a), head(b)))
        LT: return cons(head(a), merge2(tail(a), b));
        GT: return cons(head(b), merge2(a, tail(b)));
        // drop entry in a and overwrite with one in b
        EQ: return cons(head(b), merge2(tail(a), tail(b)));
    endcase
  endfunction
  return foldl1(merge2,ls);
endfunction

////////////////////////////////////////////////////////////////////////////////

typeclass DefineUnkInstr#(type a);
  module [InstrDefModule]
    defineUnkInstr#(function a f(Bit#(n) s))() provisos (Add#(a__, n, MaxInstSz));
endtypeclass

instance DefineUnkInstr#(Action);
  module [InstrDefModule] defineUnkInstr#(function Action f(Bit#(n) s))()
  provisos (Add#(a__, n, MaxInstSz));
    function Recipe applyFunc(Bit#(MaxInstSz) x) = rAct(f(truncate(x)));
    addToCollection(UnkInstDef(applyFunc));
  endmodule
endinstance

instance DefineUnkInstr#(List#(Action));
  module [InstrDefModule] defineUnkInstr#(function List#(Action) f(Bit#(n) s))()
  provisos (Add#(a__, n, MaxInstSz));
    function Recipe applyFunc(Bit#(MaxInstSz) x) = rPar(map(rAct, f(truncate(x))));
    addToCollection(UnkInstDef(applyFunc));
  endmodule
endinstance

/////////////////
// Collections //
////////////////////////////////////////////////////////////////////////////////

typedef struct {
  List#(InstrDefn) instrDefs;
  UnkInstrDefn unkInstrDef;
} BIDCollections;

module [Module] getCollections#(
  state_t state, List#(function InstrDefModule#(ifc) mkMod (state_t st)) ms)
  (BIDCollections);

  // harvest instructions
  //////////////////////////////////////////////////////////////////////////////
  // apply state, and get collections for each module
  function applyState(g) = g(state);
  let cs <- mapM(exposeCollection,map(applyState, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(List#(ISAInstDfn)) isaInstrModuleDefs = map(getItems, cs);
  // split definitions per type
  let func = compose(checkInstrDefns,compose(sortBy(cmpInstrDefn),getInstDefs));
  let instrModuleDefs = map(func, isaInstrModuleDefs);
  let unkInstrModuleDefs = map(getUnkInstDefs, isaInstrModuleDefs);
  // instruction definitions
  List#(InstrDefn) instrDefs = mergeInstrDefns(instrModuleDefs);
  // unknown instruction definitions
  let unkInstrDefs = concat(unkInstrModuleDefs);
  let unkInstrDefsLen = length(unkInstrDefs);
  if (unkInstrDefsLen != 1)
    errorM(sprintf("There must be exactly one unknown instruction behaviour defined with defineUnkInst (%0d detected)", unkInstrDefsLen));

  return BIDCollections {
    instrDefs: instrDefs,
    unkInstrDef: head(unkInstrDefs)
  };

endmodule

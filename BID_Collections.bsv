// 2018, Alexandre Joannou, University of Cambridge

import Recipe :: *;
import BitPat :: *;

import List :: *;
import Printf :: *;
import ModuleCollect :: *;

import BID_SimUtils :: *;
import BID_Interface :: *;

///////////////////////////
// Simulator state types //
////////////////////////////////////////////////////////////////////////////////

typeclass ArchState#(type a);
  function Fmt lightReport (a s);
  function Fmt fullReport (a s);
endtypeclass

typeclass World#(type a);
  module initWorld(a);
endtypeclass

///////////////////////////////////
// Types to harvest instructions //
////////////////////////////////////////////////////////////////////////////////

typedef Tuple2#(String, function GuardedRecipe f(Bit#(n) subject)) InstrDefn#(numeric type n);
typedef function Recipe f(Bit#(n) subject) UnkInstrDefn#(numeric type n);

typedef union tagged {
  InstrDefn#(n) InstDef;
  UnkInstrDefn#(n) UnkInstDef;
} ISAInstDfn#(numeric type n);

function List#(InstrDefn#(n)) getInstDef (ISAInstDfn#(n) e) =
  e matches tagged InstDef .x ? cons(x, Nil) : Nil;
function List#(UnkInstrDefn#(n)) getUnkInstDef (ISAInstDfn#(n) e) =
  e matches tagged UnkInstDef .x ? cons(x, Nil) : Nil;
function List#(InstrDefn#(n)) getInstDefs(List#(ISAInstDfn#(n)) defs) =
  concat(map(getInstDef,defs));
function List#(UnkInstrDefn#(n)) getUnkInstDefs(List#(ISAInstDfn#(n)) defs) =
  concat(map(getUnkInstDef,defs));

typedef ModuleCollect#(ISAInstDfn#(n), ifc) InstrDefModule#(numeric type n, type ifc);
typedef InstrDefModule#(32, ifc) Instr32DefModule#(type ifc);

////////////////////////////////////////////////////////////////////////////////

typeclass DefineInstr#(type a);
  module [InstrDefModule#(n)] defineInstr#(String name, BitPat#(n, t, a) p, function t f)();
endtypeclass

instance DefineInstr#(Action);
  module [InstrDefModule#(n)] defineInstr#(String name, BitPat#(n, t, Action) p, function t f)();
    function flipPat(x);
      Tuple2#(Bool, Action) res = p(x, f);
      return GuardedRecipe { guard: tpl_1(res), recipe: rAct(tpl_2(res)) };
    endfunction
    addToCollection(InstDef(tuple2(name,flipPat)));
  endmodule
endinstance

instance DefineInstr#(List#(Action));
  module [InstrDefModule#(n)] defineInstr#(String name, BitPat#(n, t, List#(Action)) p, function t f)();
    function flipPat(x);
      Tuple2#(Bool, List#(Action)) res = p(x, f);
      return GuardedRecipe { guard: tpl_1(res), recipe: rPar(map(rAct, tpl_2(res))) };
    endfunction
    addToCollection(InstDef(tuple2(name, flipPat)));
  endmodule
endinstance

instance DefineInstr#(Recipe);
  module [InstrDefModule#(n)] defineInstr#(String name, BitPat#(n, t, Recipe) p, function t f)();
    function flipPat(x);
      Tuple2#(Bool, Recipe) res = p(x, f);
      return GuardedRecipe { guard: tpl_1(res), recipe: tpl_2(res) };
    endfunction
    addToCollection(InstDef(tuple2(name, flipPat)));
  endmodule
endinstance

function List#(InstrDefn#(n)) checkInstrDefns(List#(InstrDefn#(n)) ls);
  function check(a,b) = (tpl_1(a) != tpl_1(b)) ?
    b : error(sprintf("Multiple definition of the %s instruction within the same module.", tpl_1(a)));
  if (ls matches Nil) return Nil;
  else return cons(head(ls), zipWith(check, ls, tail(ls)));
endfunction

function Ordering cmpInstrDefn(InstrDefn#(n) x, InstrDefn#(n) y);
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

function List#(InstrDefn#(n)) mergeInstrDefns(List#(List#(InstrDefn#(n))) ls);
  function List#(InstrDefn#(n)) merge2(
    List#(InstrDefn#(n)) a,
    List#(InstrDefn#(n)) b);
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
  module [InstrDefModule#(n)] defineUnkInstr#(function a f(Bit#(n) s))();
endtypeclass

instance DefineUnkInstr#(Action);
  module [InstrDefModule#(n)] defineUnkInstr#(function Action f(Bit#(n) s))();
    function Recipe applyFunc(Bit#(n) x) = rAct(f(x));
    addToCollection(UnkInstDef(applyFunc));
  endmodule
endinstance

instance DefineUnkInstr#(List#(Action));
  module [InstrDefModule#(n)] defineUnkInstr#(function List#(Action) f(Bit#(n) s))();
    function Recipe applyFunc(Bit#(n) x) = rPar(map(rAct, f(x)));
    addToCollection(UnkInstDef(applyFunc));
  endmodule
endinstance

/////////////////
// Collections //
////////////////////////////////////////////////////////////////////////////////

typedef struct {
  List#(InstrDefn#(inst_sz)) instrDefs;
  UnkInstrDefn#(inst_sz) unkInstrDef;
} BIDCollections#(numeric type inst_sz);

module [Module] getCollections#(
  FullMem#(addr_t, inst_t, data_t) mem,
  archstate_t archState,
  List#(function InstrDefModule#(inst_sz, ifc) mkMod (archstate_t st, Mem#(addr_t, data_t) dmem)) ms)
  (BIDCollections#(inst_sz));

  // harvest instructions
  //////////////////////////////////////////////////////////////////////////////
  // apply state and mem, and get collections for each module
  function applyStateAndMem (g) = g(archState, mem.data);
  let cs <- mapM(exposeCollection,map(applyStateAndMem, ms));
  function List#(a) getItems (IWithCollection#(a,i) c) = c.collection();
  List#(List#(ISAInstDfn#(inst_sz))) isaInstrModuleDefs = map(getItems, cs);
  // split definitions per type
  let func = compose(checkInstrDefns,compose(sortBy(cmpInstrDefn),getInstDefs));
  let instrModuleDefs = map(func, isaInstrModuleDefs);
  let unkInstrModuleDefs = map(getUnkInstDefs, isaInstrModuleDefs);
  // instruction definitions
  List#(InstrDefn#(inst_sz)) instrDefs = mergeInstrDefns(instrModuleDefs);
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

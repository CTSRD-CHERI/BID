/*-
 * Copyright (c) 2018 Alexandre Joannou
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

import List :: *;
import Printf :: *;
import ModuleCollect :: *;

// non standard packages
import Recipe :: *;
import BitPat :: *;

//////////////////////////
// Simulator state type //
////////////////////////////////////////////////////////////////////////////////

typeclass State#(type a);
  function Fmt lightReport (a s);
  function Fmt fullReport (a s);
  function Action reqNextInst(a s);
  function ActionValue#(Bit#(MaxInstSz)) getNextInst(a s);
endtypeclass

//////////////////////////////////////
// Types to harvest ISA description //
////////////////////////////////////////////////////////////////////////////////

`ifdef MAX_INST_SZ
typedef MAX_INST_SZ MaxInstSz;
`else
typedef 32 MaxInstSz;
`endif

typedef Tuple2#(String, function Guarded#(Recipe) f(Bit#(MaxInstSz) subject)) InstrDefn;
typedef function Recipe f(Bit#(MaxInstSz) subject) UnkInstrDefn;
typedef Recipe InitDefn;
typedef Guarded#(Recipe) ProDefn;
typedef Guarded#(Recipe) EpiDefn;
typedef Guarded#(Recipe) InterDefn;

typedef union tagged {
  InitDefn InitDef; // To define an initialization recipe
  InstrDefn InstrDef; // To define an the behaviour of an instruction
  UnkInstrDefn UnkInstrDef; // To define the behaviour on an unknown instruction
  ProDefn ProDef; // To define a behaviour at the beginning of instructions
  EpiDefn EpiDef; // To define a behaviour at the end of instructions
  InterDefn InterDef; // To define a behaviour between instructions
} ISAInstDfn;

`define defGet(n)\
function List#(``n``Defn) get``n``Def (ISAInstDfn e) =\
  e matches tagged n``Def .x ? cons(x, Nil) : Nil;\
function List#(``n``Defn) get``n``Defs(List#(ISAInstDfn) defs) =\
  concat(map(get``n``Def,defs));

`defGet(Init)
`defGet(Instr)
`defGet(UnkInstr)
`defGet(Pro)
`defGet(Epi)
`defGet(Inter)

`undef defGet

typedef ModuleCollect#(ISAInstDfn, ifc) InstrDefModule#(type ifc);

// define an InitDef
////////////////////////////////////////////////////////////////////////////////
typeclass DefineInit#(type a);
  module [InstrDefModule] defineInit#(a x)();
endtypeclass
instance DefineInit#(Action);
  module [InstrDefModule] defineInit#(Action x)();
    addToCollection(InitDef(rAct(x)));
  endmodule
endinstance
instance DefineInit#(Recipe);
  module [InstrDefModule] defineInit#(Recipe x)();
    addToCollection(InitDef(x));
  endmodule
endinstance

// define an InstrDef
////////////////////////////////////////////////////////////////////////////////

typeclass DefineInstr#(type a);
  module [InstrDefModule]
    defineInstr#(String name, BitPat#(n, t, a) p, function t f) ()
    provisos (Add#(a__, n, MaxInstSz));
endtypeclass

instance DefineInstr#(Action);
  module [InstrDefModule] defineInstr#(String name, BitPat#(n, t, Action) p, function t f)()
  provisos (Add#(a__, n, MaxInstSz));
    function Guarded#(Recipe) flipPat(Bit#(MaxInstSz) x);
      Bit#(n) subject = truncate(x);
      Tuple2#(GCol#(Bit#(0)), Action) res = p(subject, f);
      return Guarded { guard: tpl_1(res).guard, val: rAct(tpl_2(res)) };
    endfunction
    addToCollection(InstrDef(tuple2(name,flipPat)));
  endmodule
endinstance

instance DefineInstr#(List#(Action));
  module [InstrDefModule] defineInstr#(String name, BitPat#(n, t, List#(Action)) p, function t f)()
  provisos (Add#(a__, n, MaxInstSz));
    function flipPat(x);
      Tuple2#(GCol#(Bit#(0)), List#(Action)) res = p(truncate(x), f);
      return Guarded { guard: tpl_1(res).guard, val: rPar(map(rAct, tpl_2(res))) };
    endfunction
    addToCollection(InstrDef(tuple2(name, flipPat)));
  endmodule
endinstance

instance DefineInstr#(Recipe);
  module [InstrDefModule] defineInstr#(String name, BitPat#(n, t, Recipe) p, function t f)()
  provisos (Add#(a__, n, MaxInstSz));
    function flipPat(x);
      Tuple2#(GCol#(Bit#(0)), Recipe) res = p(truncate(x), f);
      return Guarded { guard: tpl_1(res).guard, val: tpl_2(res) };
    endfunction
    addToCollection(InstrDef(tuple2(name, flipPat)));
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

// define an UnkInstrDef
////////////////////////////////////////////////////////////////////////////////

typeclass DefineUnkInstr#(type a);
  module [InstrDefModule]
    defineUnkInstr#(function a f(Bit#(n) s))() provisos (Add#(a__, n, MaxInstSz));
endtypeclass

instance DefineUnkInstr#(Action);
  module [InstrDefModule] defineUnkInstr#(function Action f(Bit#(n) s))()
  provisos (Add#(a__, n, MaxInstSz));
    function Recipe applyFunc(Bit#(MaxInstSz) x) = rAct(f(truncate(x)));
    addToCollection(UnkInstrDef(applyFunc));
  endmodule
endinstance

instance DefineUnkInstr#(List#(Action));
  module [InstrDefModule] defineUnkInstr#(function List#(Action) f(Bit#(n) s))()
  provisos (Add#(a__, n, MaxInstSz));
    function Recipe applyFunc(Bit#(MaxInstSz) x) = rPar(map(rAct, f(truncate(x))));
    addToCollection(UnkInstrDef(applyFunc));
  endmodule
endinstance

// define an prologue/epilogue/interlude
////////////////////////////////////////////////////////////////////////////////

`define defGuardedRecipe(methodname, consname)\
typeclass Class_``methodname``#(type a);\
  module [InstrDefModule] methodname``#(a x)();\
endtypeclass\
instance Class_``methodname``#(Action);\
  module [InstrDefModule] methodname``#(Action x)();\
    addToCollection(``consname``Def(Guarded { guard: True, val: rAct(x) }));\
  endmodule\
endinstance\
instance Class_``methodname``#(Guarded#(Action));\
  module [InstrDefModule] methodname``#(Guarded#(Action) x)();\
    addToCollection(``consname``Def(Guarded { guard: x.guard, val: rAct(x.val) }));\
  endmodule\
endinstance

`defGuardedRecipe(definePrologue, Pro)
`defGuardedRecipe(defineEpilogue, Epi)
`defGuardedRecipe(defineInterlude, Inter)

`undef defGuardedRecipe

/////////////////
// Collections //
////////////////////////////////////////////////////////////////////////////////

typedef struct {
  InitDefn initDef;
  List#(InstrDefn) instrDefs;
  UnkInstrDefn unkInstrDef;
  List#(ProDefn) proDefs;
  List#(EpiDefn) epiDefs;
  List#(InterDefn) interDefs;
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
  let func = compose(checkInstrDefns,compose(sortBy(cmpInstrDefn),getInstrDefs));
  let initModuleDefs = map(getInitDefs, isaInstrModuleDefs);
  let instrModuleDefs = map(func, isaInstrModuleDefs);
  let unkInstrModuleDefs = map(getUnkInstrDefs, isaInstrModuleDefs);
  let proModuleDefs = map(getProDefs, isaInstrModuleDefs);
  let epiModuleDefs = map(getEpiDefs, isaInstrModuleDefs);
  let interModuleDefs = map(getInterDefs, isaInstrModuleDefs);
  // init definitions
  let initDefs = concat(initModuleDefs);
  let initDefsLen = length(initDefs);
  if (initDefsLen != 1)
    errorM(sprintf("There must be exactly one initialization defined with defineInit (%0d detected)", initDefsLen));
  // instruction definitions
  List#(InstrDefn) instrDefs = mergeInstrDefns(instrModuleDefs);
  let instrDefsLen = length(instrDefs);
  if (instrDefsLen < 1)
    errorM(sprintf("There must be at least one instruction defined with defineInstr (%0d detected)", instrDefsLen));
  // unknown instruction definitions
  let unkInstrDefs = concat(unkInstrModuleDefs);
  let unkInstrDefsLen = length(unkInstrDefs);
  if (unkInstrDefsLen != 1)
    errorM(sprintf("There must be exactly one unknown instruction defined with defineUnkInstr (%0d detected)", unkInstrDefsLen));
  // flatten list of prologues
  let proDefs = concat(proModuleDefs);
  // flatten list of epilogues
  let epiDefs = concat(epiModuleDefs);
  // flatten list of interludes
  let interDefs = concat(interModuleDefs);

  return BIDCollections {
    initDef: head(initDefs),
    instrDefs: instrDefs,
    unkInstrDef: head(unkInstrDefs),
    proDefs: proDefs,
    epiDefs: epiDefs,
    interDefs: interDefs
  };

endmodule

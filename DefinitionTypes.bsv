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

import SourceSink :: *;
import Recipe :: *;
import BitPat :: *;

`ifdef MAX_INST_SZ
typedef MAX_INST_SZ MaxInstSz;
`else
typedef 32 MaxInstSz;
`endif

////////////////
// State type //
////////////////////////////////////////////////////////////////////////////////

typeclass State#(type a);
  function Fmt lightReport (a s);
  function Fmt fullReport (a s);
  function Action commit (a s);
endtypeclass

//////////////////////////////////
// ISA Definition Entry classes //
////////////////////////////////////////////////////////////////////////////////

typedef Recipe InitDefEntry;
typedef function Recipe f(Sink#(Bit#(MaxInstSz)) snk) FetchInstDefEntry;
typedef function Recipe f(Bit#(MaxInstSz) subject) UnkInstDefEntry;
typedef Tuple2#(String, function Guarded#(Recipe) f(Bit#(MaxInstSz) subject))
  InstDefEntry;
typedef Guarded#(Recipe) ProDefEntry;
typedef Guarded#(Recipe) EpiDefEntry;
typedef Guarded#(Recipe) InterDefEntry;

typedef union tagged {
  InitDefEntry      InitEntry;
  FetchInstDefEntry FetchInstEntry;
  UnkInstDefEntry   UnkInstEntry;
  InstDefEntry      InstEntry;
  ProDefEntry       ProEntry;
  EpiDefEntry       EpiEntry;
  InterDefEntry     InterEntry;
} ISAEntry;

`define defGet(n)\
function List#(``n``DefEntry) get``n``DefEntry (ISAEntry e) =\
  e matches tagged n``Entry .x ? cons(x, Nil) : Nil;\
function List#(``n``DefEntry) get``n``DefEntries(List#(ISAEntry) defs) =\
  concat(map(get``n``DefEntry, defs));

`defGet(Init)
`defGet(FetchInst)
`defGet(UnkInst)
`defGet(Inst)
`defGet(Pro)
`defGet(Epi)
`defGet(Inter)

`undef defGet

typedef ModuleCollect#(ISAEntry, ifc) ISADefModule#(type ifc);

//////////////////////////////////////
// ISADefs entries defining methods //
////////////////////////////////////////////////////////////////////////////////

`define defISADE(name)\
typeclass Define``name``Entry#(type a);\
  module [ISADefModule] define``name``Entry#(a x) (Empty);\
endtypeclass\
instance Define``name``Entry#(name``DefEntry);\
  module [ISADefModule] define``name``Entry#(name``DefEntry x) (Empty);\
    addToCollection(name``Entry(x));\
  endmodule\
endinstance

// Init entries
////////////////////////////////////////////////////////////////////////////////
`defISADE(Init)
instance DefineInitEntry#(Action);
  module [ISADefModule] defineInitEntry#(Action x) (Empty);
    addToCollection(InitEntry(rAct(x)));
  endmodule
endinstance
// Fetch instruction entries
////////////////////////////////////////////////////////////////////////////////
`defISADE(FetchInst)
// Unknown instruction entries
////////////////////////////////////////////////////////////////////////////////
typeclass DefineUnkInstEntry#(type a);
  module [ISADefModule] defineUnkInstEntry#(
    function a f(Bit#(n) s)) (Empty) provisos (Add#(a__, n, MaxInstSz));
endtypeclass
instance DefineUnkInstEntry#(Action);
  module [ISADefModule] defineUnkInstEntry#(function Action f(Bit#(n) s)) (Empty)
    provisos (Add#(a__, n, MaxInstSz));
    function Recipe applyFunc(Bit#(MaxInstSz) x) = rAct(f(truncate(x)));
    addToCollection(UnkInstEntry(applyFunc));
  endmodule
endinstance
instance DefineUnkInstEntry#(List#(Action));
  module [ISADefModule] defineUnkInstEntry#(
    function List#(Action) f(Bit#(n) s)) (Empty)
    provisos (Add#(a__, n, MaxInstSz));
    function Recipe applyFunc(Bit#(MaxInstSz) x) =
      rPar(map(rAct, f(truncate(x))));
    addToCollection(UnkInstEntry(applyFunc));
  endmodule
endinstance
// Instruction entries
////////////////////////////////////////////////////////////////////////////////
typeclass DefineInstEntry#(type a);
  module [ISADefModule]
    defineInstEntry#(String name, BitPat#(n, t, a) p, function t f) (Empty)
      provisos (Add#(a__, n, MaxInstSz));
endtypeclass
instance DefineInstEntry#(Action);
  module [ISADefModule]
    defineInstEntry#(String name, BitPat#(n, t, Action) p, function t f) (Empty)
    provisos (Add#(a__, n, MaxInstSz));
    function Guarded#(Recipe) flipPat(Bit#(MaxInstSz) x);
      Bit#(n) subject = truncate(x);
      Tuple2#(GCol#(Bit#(0)), Action) res = p(subject, f);
      return Guarded { guard: tpl_1(res).guard, val: rAct(tpl_2(res)) };
    endfunction
    addToCollection(InstEntry(tuple2(name, flipPat)));
  endmodule
endinstance
instance DefineInstEntry#(List#(Action));
  module [ISADefModule] defineInstEntry#(
    String name, BitPat#(n, t, List#(Action)) p, function t f) (Empty)
    provisos (Add#(a__, n, MaxInstSz));
    function flipPat(x);
      Tuple2#(GCol#(Bit#(0)), List#(Action)) res = p(truncate(x), f);
      return Guarded {
        guard: tpl_1(res).guard, val: rPar(map(rAct, tpl_2(res)))
      };
    endfunction
    addToCollection(InstEntry(tuple2(name, flipPat)));
  endmodule
endinstance
instance DefineInstEntry#(Recipe);
  module [ISADefModule] defineInstEntry#(
    String name, BitPat#(n, t, Recipe) p, function t f) (Empty)
    provisos (Add#(a__, n, MaxInstSz));
    function flipPat(x);
      Tuple2#(GCol#(Bit#(0)), Recipe) res = p(truncate(x), f);
      return Guarded { guard: tpl_1(res).guard, val: tpl_2(res) };
    endfunction
    addToCollection(InstEntry(tuple2(name, flipPat)));
  endmodule
endinstance
// Prologue/Epilogue/Interlude entries
////////////////////////////////////////////////////////////////////////////////
`define defProEpiInter(name)\
`defISADE(name)\
instance Define``name``Entry#(Guarded#(Action));\
  module [ISADefModule] define``name``Entry#(Guarded#(Action) x) (Empty);\
    addToCollection(name``Entry(Guarded { guard: x.guard, val: rAct(x.val) }));\
  endmodule\
endinstance\
instance Define``name``Entry#(Action);\
  module [ISADefModule] define``name``Entry#(Action x) (Empty);\
    addToCollection(name``Entry(Guarded { guard: True, val: rAct(x) }));\
  endmodule\
endinstance\
instance Define``name``Entry#(Recipe);\
  module [ISADefModule] define``name``Entry#(Recipe x) (Empty);\
    addToCollection(name``Entry(Guarded { guard: True, val: x }));\
  endmodule\
endinstance
`defProEpiInter(Pro)
`defProEpiInter(Epi)
`defProEpiInter(Inter)
`undef defProEpiInter

`undef defISADE

/////////////////////
// InstDef filters //
////////////////////////////////////////////////////////////////////////////////

function List#(InstDefEntry) uniqueInstDefs(List#(InstDefEntry) ls);
  function check(a,b) = (tpl_1(a) != tpl_1(b)) ?
    b : error(sprintf("Multiple definition of the %s instruction "
                    + "within the same module.", tpl_1(a)));
  if (ls matches Nil) return Nil;
  else return cons(head(ls), zipWith(check, ls, tail(ls)));
endfunction

function Ordering cmpInstDefs(InstDefEntry x, InstDefEntry y);
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

function List#(InstDefEntry) mergeInstDefs(List#(List#(InstDefEntry)) ls);
  function List#(InstDefEntry) merge2(List#(InstDefEntry) a, List#(InstDefEntry) b);
    if (a matches Nil) return b;
    else if (b matches Nil) return a;
    else case (cmpInstDefs(head(a), head(b)))
        LT: return cons(head(a), merge2(tail(a), b));
        GT: return cons(head(b), merge2(a, tail(b)));
        // drop entry in a and overwrite with one in b
        EQ: return cons(head(b), merge2(tail(a), tail(b)));
    endcase
  endfunction
  return foldl1(merge2,ls);
endfunction

///////////////////////////////////////////
// BID ISA definition entries harvesting //
////////////////////////////////////////////////////////////////////////////////

typedef struct {
  InitDefEntry         initEntry;
  FetchInstDefEntry    fetchInstEntry;
  UnkInstDefEntry      unkInstEntry;
  List#(InstDefEntry)  instEntries;
  List#(ProDefEntry)   proEntries;
  List#(EpiDefEntry)   epiEntries;
  List#(InterDefEntry) interEntries;
} ISAEntries;

module [Module] getISAEntries#(
  state_t state, List#(function ISADefModule#(ifc) mkMod (state_t st)) ms)
  (ISAEntries);

  // apply state, and get ISADefs for each module
  //////////////////////////////////////////////////////////////////////////////
  function applyState(g) = g(state);
  let cs <- mapM(exposeCollection, map(applyState, ms));
  function List#(a) getItems (IWithCollection#(a, i) c) = c.collection();
  List#(List#(ISAEntry)) modDefs = map(getItems, cs);
  // split definitions per type
  let initModDefs      = map(getInitDefEntries, modDefs);
  let fetchInstModDefs = map(getFetchInstDefEntries, modDefs);
  let unkInstModDefs   = map(getUnkInstDefEntries, modDefs);
  let instModDefs      = map(getInstDefEntries, modDefs);
  let proModDefs       = map(getProDefEntries, modDefs);
  let epiModDefs       = map(getEpiDefEntries, modDefs);
  let interModDefs     = map(getInterDefEntries, modDefs);

  // filters and assertions on the definitions
  //////////////////////////////////////////////////////////////////////////////
  // initialize
  let initDefs = concat(initModDefs);
  let initDefsLen = length(initDefs);
  if (initDefsLen != 1)
    errorM(sprintf(
      "There must be exactly one initialization ISA definition entry defined "
    + "with defineInitEntry (%0d detected)", initDefsLen));
  // fetch instruction
  let fetchInstDefs = concat(fetchInstModDefs);
  let fetchInstDefsLen = length(fetchInstDefs);
  if (fetchInstDefsLen != 1)
    errorM(sprintf(
      "There must be exactly one instruction fetch ISA definition entry "
    + "defined with defineFetchInstEntry (%0d detected)", fetchInstDefsLen));
  // unknown instruction
  let unkInstDefs = concat(unkInstModDefs);
  let unkInstDefsLen = length(unkInstDefs);
  if (unkInstDefsLen != 1)
    errorM(sprintf(
      "There must be exactly one unkown instruction ISA definition entry "
    + "defined with defineUnkInstEntry (%0d detected)", unkInstDefsLen));
  // instructions
  let func = compose(uniqueInstDefs,sortBy(cmpInstDefs));
  let instDefs = mergeInstDefs(map(func, instModDefs));
  let instDefsLen = length(instDefs);
  if (instDefsLen < 1)
    errorM(sprintf(
      "There must be at least one instruction ISA definition entry defined "
    + "with defineInstEntry (%0d detected)", instDefsLen));
  // prologues
  let proDefs = concat(proModDefs);
  // epilogues
  let epiDefs = concat(epiModDefs);
  // interludes
  let interDefs = concat(interModDefs);

  return ISAEntries {
    initEntry:      head(initDefs),
    fetchInstEntry: head(fetchInstDefs),
    unkInstEntry:   head(unkInstDefs),
    instEntries:    instDefs,
    proEntries:     proDefs,
    epiEntries:     epiDefs,
    interEntries:   interDefs
  };

endmodule

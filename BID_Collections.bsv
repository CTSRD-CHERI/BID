// 2018, Alexandre Joannou, University of Cambridge

import BitPat :: *;

import List :: *;
import Printf :: *;
import ModuleCollect :: *;

import BID_SimUtils :: *;

//////////////////////////////////////////
// Types to harvest architectural state //
////////////////////////////////////////////////////////////////////////////////

typedef union tagged {
  Bit#(n) ArchPC;
  Action OnInstCommit;
} ISAStateDfn#(numeric type n);
function List#(Bit#(m)) getArchPC (ISAStateDfn#(m) e) =
  e matches tagged ArchPC .x ? cons(x, Nil) : Nil;
function List#(Action) getOnInstCommit (ISAStateDfn#(m) e) =
  e matches tagged OnInstCommit .x ? cons(x, Nil) : Nil;
typedef ModuleCollect#(ISAStateDfn#(n), ifc) ArchStateDefModule#(numeric type n, type ifc);

////////////////////////////////////////////////////////////////////////////////

module [ArchStateDefModule#(n)] mkPC (Reg#(a_type))
provisos(
  Bits#(a_type, n),
  Literal#(a_type)
);
  Reg#(a_type) r[2] <- mkCReg(2,0);
  addToCollection(tagged ArchPC pack(r[1]));
  return r[0];
endmodule

////////////////////////////////////////////////////////////////////////////////

module [ArchStateDefModule#(n)] mkCommittedInstCnt (Reg#(a_type))
provisos(
  Bits#(a_type, a_type_sz),
  Arith#(a_type)
);
  Reg#(a_type) r <- mkReg(0);
  ISAStateDfn#(n) element = tagged OnInstCommit action r <= r + 1; endaction;
  addToCollection(element);
  method a_type _read() = r;
  method Action _write(a_type v);
    printLog($format("WARNING - ignoring write of %0d to an inst counter", v));
  endmethod
endmodule

///////////////////////////////////
// Types to harvest instructions //
////////////////////////////////////////////////////////////////////////////////

typedef Tuple2#(String, function GuardedActions f(Bit#(n) subject)) InstrDefn#(numeric type n);
typedef function List#(Action) f(Bit#(n) subject) UnkInstrDefn#(numeric type n);

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
      return GuardedActions { guard: tpl_1(res), body: cons(tpl_2(res), Nil) };
    endfunction
    addToCollection(tagged InstDef tuple2(name,flipPat));
  endmodule
endinstance

instance DefineInstr#(List#(Action));
  module [InstrDefModule#(n)] defineInstr#(String name, BitPat#(n, t, List#(Action)) p, function t f)();
    function flipPat(x);
      Tuple2#(Bool, List#(Action)) res = p(x, f);
      return GuardedActions { guard: tpl_1(res), body: tpl_2(res) };
    endfunction
    addToCollection(tagged InstDef tuple2(name, flipPat));
  endmodule
endinstance

function List#(InstrDefn#(n)) checkInstrDefns(List#(InstrDefn#(n)) ls);
  function check(a,b) = (tpl_1(a) != tpl_1(b)) ?
    b : error(sprintf("Multiple definition of the %s instruction within the same module.", tpl_1(a)));
  return cons(head(ls), zipWith(check, ls, tail(ls)));
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
    function List#(Action) applyFunc(Bit#(n) x) = cons(f(x),Nil);
    addToCollection(tagged UnkInstDef applyFunc);
  endmodule
endinstance

instance DefineUnkInstr#(List#(Action));
  module [InstrDefModule#(n)] defineUnkInstr#(function List#(Action) f(Bit#(n) s))();
    function List#(Action) applyFunc(Bit#(n) x) = f(x);
    addToCollection(tagged UnkInstDef applyFunc);
  endmodule
endinstance

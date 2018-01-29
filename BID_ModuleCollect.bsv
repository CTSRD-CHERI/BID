// 2018, Alexandre Joannou, University of Cambridge

import BitPat :: *;

import List :: *;
import ModuleCollect :: *;

import BID_SimUtils :: *;

//////////////////////////////////////////
// Types to harvest architectural state //
////////////////////////////////////////////////////////////////////////////////

typedef union tagged {
  Bit#(n) ArchPC;
  Action OnInstCommit;
} ArchStateDfn#(numeric type n);
function List#(Bit#(m)) getArchPC (ArchStateDfn#(m) e) =
  e matches tagged ArchPC .x ? cons(x, Nil) : Nil;
function List#(Action) getOnInstCommit (ArchStateDfn#(m) e) =
  e matches tagged OnInstCommit .x ? cons(x, Nil) : Nil;
typedef ModuleCollect#(ArchStateDfn#(n), ifc) ArchStateDefModule#(numeric type n, type ifc);

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
  ArchStateDfn#(n) element = tagged OnInstCommit action r <= r + 1; endaction;
  addToCollection(element);
  method a_type _read() = r;
  method Action _write(a_type v);
    printLog($format("WARNING - ignoring write of %0d to an inst counter", v));
  endmethod
endmodule

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
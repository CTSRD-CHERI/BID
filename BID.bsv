// 2018, Alexandre Joannou, University of Cambridge

import BitPat :: *;

import List :: *;
import FIFO :: *;
import RegFile :: *;
import ModuleCollect :: *;

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

typeclass World#(type a);
  module initWorld(a);
endtypeclass

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
  archstate_t s,
  world_t w,
  List#(function InstrDefModule#(n, ifc) mkMod (archstate_t st, world_t wo)) ms) ()
  provisos (ArchState#(archstate_t), World#(world_t));

  // local state
  Reg#(UInt#(8)) stepCounter <- mkReg(0);

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

////////////////
// Simple Mem //
////////////////////////////////////////////////////////////////////////////////

typedef union tagged {
  struct {
    index_t addr;
    Bit#(5) byteWidth;
  } ReadReq;
  struct {
    index_t addr;
    Bit#(5) byteWidth;
    data_t data;
  } WriteReq;
} MemReq#(type index_t, type data_t) deriving (Bits, FShow);

typedef union tagged {
  data_t ReadRsp;
  void Failure;
} MemRsp#(type data_t) deriving (Bits, FShow);

interface Mem#(type index_t, type data_t);
  method Action sendReq (MemReq#(index_t, data_t) req);
  method ActionValue#(MemRsp#(data_t)) getRsp ();
endinterface

module mkMem#(Integer size) (Mem#(index_t, data_t))
provisos(
  Bits#(index_t, index_w),
  Literal#(index_t),
  Bits#(data_t, data_w),
  FShow#(data_t)
);

  RegFile#(index_t, data_t) mem <- mkRegFile(0, fromInteger(size - 1));
  Reg#(Maybe#(MemRsp#(data_t))) rsp <- mkReg(tagged Invalid);

  method Action sendReq (MemReq#(index_t, data_t) req);
    case (req) matches
      tagged ReadReq .r: begin
        rsp <= tagged Valid (tagged ReadRsp mem.sub(r.addr));
        $display("simple mem -- read addr 0x%0x", r.addr);
      end
      tagged WriteReq .w: begin
        mem.upd(w.addr, w.data);
        $display("simple mem -- write addr 0x%0x with data 0x%0x", w.addr, w.data);
      end
    endcase
  endmethod

  method ActionValue#(MemRsp#(data_t)) getRsp () if (isValid(rsp));
    let retRsp = fromMaybe(tagged Failure, rsp);
    $display("simple mem -- returning ", fshow(retRsp));
    return retRsp;
  endmethod

endmodule

// 2018, Alexandre Joannou, University of Cambridge

import BitPat :: *;

import List :: *;
import FIFO :: *;
import SpecialFIFOs :: *;
import RegFile :: *;
import NumberTypes :: *;
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

typedef 8 BitsPerByte;

// Memory request
typedef union tagged {
`define ACCESS_W_T BuffIndex#(TLog#(TDiv#(SizeOf#(data_t), BitsPerByte)), TDiv#(SizeOf#(data_t), BitsPerByte))
  struct {
    idx_t addr;
    `ACCESS_W_T byteWidth; // XXX Note 0 maps to largest size
  } ReadReq;
  struct {
    idx_t addr;
    `ACCESS_W_T byteWidth; // XXX Note 0 maps to largest size
    data_t data;
  } WriteReq;
} MemReq#(type idx_t, type data_t);

// Memory response
typedef union tagged {
  data_t ReadRsp;
  void Failure;
} MemRsp#(type data_t) deriving (Bits, FShow);

// Memory interface
interface Mem#(type idx_t, type data_t);
  method Action sendReq (MemReq#(idx_t, data_t) req);
  method ActionValue#(MemRsp#(data_t)) getRsp ();
endinterface

// Memory module
module mkMem#(Integer size) (Mem#(idx_t, data_t))
provisos(
  // type sizes
  Bits#(idx_t, idx_sz),
  Bits#(data_t, data_sz),
  Div#(data_sz, BitsPerByte, data_byte_sz),
  Log#(data_byte_sz, offset_sz),
  Add#(offset_sz, 1, offset_large_sz),
  Add#(offset_sz, iidx_sz, idx_sz),
  // assertion with interface type
  Add#(x, TLog#(TDiv#(data_sz, BitsPerByte)), offset_large_sz),
  // other properties
  Literal#(idx_t),
  FShow#(data_t)
);

`define OFFSET_T Bit#(offset_sz)
`define OFFSET_LARGE_T Bit#(offset_large_sz)
`define IIDX_T Bit#(iidx_sz)

  // RegFile to store actual values
  RegFile#(`IIDX_T, Bit#(data_sz)) mem <- mkRegFile(0, fromInteger(size - 1));

  // Read request FIFOs
  FIFO#(Tuple3#(`IIDX_T, `OFFSET_T, `OFFSET_LARGE_T))
    readReqFIFO <- mkBypassFIFO;
  FIFO#(Tuple4#(Bit#(data_sz), `IIDX_T, `OFFSET_LARGE_T, `OFFSET_LARGE_T))
    readNextFIFO <- mkSizedFIFO(1);
  FIFO#(Bit#(data_sz))
    readRspFIFO <- mkSizedFIFO(1);

  // utility function to slice an address
  function Tuple2#(`IIDX_T, `OFFSET_T) craftInternalIndex(idx_t idx);
    return tuple2(truncateLSB(pack(idx)), truncate(pack(idx)));
  endfunction

  // First stage of the read
  rule read_stage0;
    // look at current read request and read the data
    match {.idx, .offset, .read_width} = readReqFIFO.first();
    Bit#(data_sz) val = mem.sub(idx);
    // isolate the relevant subset of the data element
    let bitOffset = offset << valueOf(TLog#(BitsPerByte));
    let bitReadWidth = read_width << valueOf(TLog#(BitsPerByte));
    val = (val >> bitOffset) & ~(~0 << bitReadWidth);
    // compute how much bytes are left to read
    `OFFSET_LARGE_T avail_width = fromInteger(valueOf(TDiv#(data_sz, BitsPerByte))) - zeroExtend(offset);
    `OFFSET_LARGE_T remaining_width = (avail_width >= read_width) ? 0 : read_width - avail_width;
    $display("simple mem @%0t -- read_width=%0d, data_w=%0d, offset=%0d, avail_width=%0d, remaining_width=%0d",$time,read_width,fromInteger(valueOf(TDiv#(data_sz, BitsPerByte))),offset,avail_width,remaining_width);
    // check for read being over or not
    if (remaining_width > 0) begin
      readNextFIFO.enq(tuple4(val, idx + 1, remaining_width, avail_width));
      $display("simple mem @%0t -- read stage 0 -- (cross boundary) idx 0x%0x, offset %0d, read %0d byte(s)", $time, idx, offset, avail_width);
    end else begin
      readRspFIFO.enq(val);
      $display("simple mem @%0t -- read stage 0 -- idx: 0x%0x, offset: %0d", $time, idx, offset);
    end
  endrule

  // Second stage of the read when crossing an element boundary
  rule read_stage1;
    // consume request from the first stage and perform lookup
    match {.val0, .idx, .width, .shift} = readNextFIFO.first();
    readNextFIFO.deq();
    Bit#(data_sz) val1 = mem.sub(idx);
    // isolate the relevant subset of the data element
    val1 = val1 & ~(~0 << (width << valueOf(TLog#(BitsPerByte))));
    // position it appropriately to merge with previously read value
    val1 = val1 << (shift << valueOf(TLog#(BitsPerByte)));
    // craft and return the read value
    readRspFIFO.enq(val0 | val1);
    $display("simple mem @%0t -- read stage 1 -- idx 0x%0x, read %0d byte(s)", $time, idx, width);
  endrule

  method Action sendReq (MemReq#(idx_t, data_t) req);
    case (req) matches
      tagged ReadReq .r: begin
        match{.idx, .offset} = craftInternalIndex(r.addr);
        let tmp = unwrapBI(r.byteWidth);
        `OFFSET_LARGE_T width = (tmp == 0) ? fromInteger(valueOf(TExp#(offset_sz))) : zeroExtend(pack(tmp));
        readReqFIFO.enq(tuple3(idx, offset, width));
      end
      tagged WriteReq .w: begin
        //match {.idx, .offset} = craftInternalIndex(w.addr);
        //mem.upd(idx, w.data);
        //$display("simple mem -- write addr 0x%0x (idx: 0x%0x, offset: %0d) with data 0x%0x", w.addr, idx, offset, w.data);
      end
    endcase
  endmethod

  method ActionValue#(MemRsp#(data_t)) getRsp ();
    MemRsp#(data_t) rsp = tagged ReadRsp unpack(readRspFIFO.first());
    readReqFIFO.deq();
    readRspFIFO.deq();
    $display("simple mem @%0t -- ", $time, fshow(rsp));
    return rsp;
  endmethod

endmodule

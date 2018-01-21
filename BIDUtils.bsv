// 2018, Alexandre Joannou, University of Cambridge

import Vector :: *;
import RegFile :: *;
import FIFO :: *;
import SpecialFIFOs :: *;
import Printf :: *;

// Nice friendly list constructor lifted from Bluecheck's sources:
// https://github.com/CTSRD-CHERI/bluecheck.git
////////////////////////////////////////////////////////////////////////////////

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

// Architectural state helpers
////////////////////////////////////////////////////////////////////////////////

// Read-only register
module mkROReg#(parameter a v) (Reg#(a));
  method Action _write (a _) = action endaction;
  method a _read() = v;
endmodule

// Register file with read-only 0 register (set to 0)
module mkRegFileZ (Vector#(n, Reg#(a)))
provisos (Bits#(a, a_sz), Literal#(a));
  Reg#(a) r0 <- mkROReg(0);
  Vector#(TSub#(n, 1), Reg#(a)) rf <- replicateM(mkReg(0));
  return cons(r0,rf);
endmodule

// Combinational primitives
////////////////////////////////////////////////////////////////////////////////

// signed comparison functions
function Bool signedLT (Bit#(n) a, Bit#(n) b);
  Int#(n) sa = unpack(a);
  Int#(n) sb = unpack(b);
  return sa < sb;
endfunction
function Bool signedGT (Bit#(n) a, Bit#(n) b);
  Int#(n) sa = unpack(a);
  Int#(n) sb = unpack(b);
  return sa > sb;
endfunction
function Bool signedGE (Bit#(n) a, Bit#(n) b);
  Int#(n) sa = unpack(a);
  Int#(n) sb = unpack(b);
  return sa >= sb;
endfunction

// arithmetic right shift
function Bit#(n) arithRightShift (Bit#(n) a, Bit#(m) b);
  Int#(n) sa = unpack(a);
  return pack(sa >> b);
endfunction

// Type to hold an n-bit value initialized by a literal starting
// at 1 and up to 2^n rather than 0 to 2^n-1
////////////////////////////////////////////////////////////////////////////////

typedef struct {
  Bit#(n) val;
} BitPO#(numeric type n);

instance Literal#(BitPO#(n));
  function BitPO#(n) fromInteger (Integer x);
    if (x > 0 && x < valueOf(TExp#(n)))
      return BitPO { val: fromInteger(x) };
    else if (x == valueOf(TExp#(n)))
      return BitPO { val: 0 };
    else return error(sprintf("Trying to initialize a BitPO#(%0d) with literal %0d. The range of valid values is %0d to %0d.",valueOf(n),x,1,valueOf(TExp#(n))));
  endfunction
  function Bool inLiteralRange (BitPO#(n) _, Integer x);
    return (x > 0 && x <= valueOf(TExp#(n)));
  endfunction
endinstance

function Bit#(TAdd#(n,1)) readBitPO (BitPO#(n) x);
  return (x.val == 0) ? fromInteger(valueOf(TExp#(n))) : zeroExtend(x.val);
endfunction

////////////////
// Simple Mem //
////////////////////////////////////////////////////////////////////////////////

typedef 8 BitsPerByte;


// Memory request
typedef union tagged {
`define ACCESS_W_T BitPO#(TLog#(TDiv#(SizeOf#(data_t), BitsPerByte)))
  struct {
    idx_t addr;
    `ACCESS_W_T numBytes;
  } ReadReq;
  struct {
    idx_t addr;
    `ACCESS_W_T numBytes;
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
  Add#(x, TAdd#(TLog#(TDiv#(data_sz, BitsPerByte)),1), offset_large_sz),
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
        /*
        XXX this crashes the bluespec compiler
        match{.idx, .offset} = craftInternalIndex(r.addr);
        readReqFIFO.enq(tuple3(idx, offset, readAccessByteWidth(r.numBytes)));
        */
        match{.idx, .offset} = craftInternalIndex(r.addr);
        readReqFIFO.enq(tuple3(idx, offset, zeroExtend(readBitPO(r.numBytes))));
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

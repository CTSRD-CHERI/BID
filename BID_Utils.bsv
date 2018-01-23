// 2018, Alexandre Joannou, University of Cambridge

import Vector :: *;
import RegFile :: *;
import FIFO :: *;
import SpecialFIFOs :: *;

import BID_Interface :: *;

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

////////////////
// Simple Mem //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSimpleMem#(Integer size) (Mem#(idx_t, data_t))
provisos(
  // type sizes
  Bits#(idx_t, idx_sz),
  Bits#(data_t, data_sz),
  Div#(data_sz, BitsPerByte, data_byte_sz),
  Mul#(BitsPerByte, data_byte_sz, data_sz),
  Log#(data_byte_sz, offset_sz),
  Add#(iidx_sz, offset_sz, idx_sz),
  // show
  FShow#(idx_t),
  FShow#(data_t)
);

`define BYTE Bit#(BitsPerByte)
`define DATAVEC Vector#(data_byte_sz, Bit#(BitsPerByte))

  Vector#(data_byte_sz, RegFile#(Bit#(iidx_sz), `BYTE)) mem <- replicateM(mkRegFile(0, fromInteger(size/valueOf(TMul#(data_byte_sz,data_byte_sz)) - 1)));
  FIFO#(`DATAVEC) readRspFIFO <- mkSizedFIFO(1);

  // Interface
  //////////////////////////////////////////////////////////////////////////////

  method Action sendReq (MemReq#(idx_t, data_t) req);
    $display("simple mem @%0t -- ", $time, fshow(req));
    case (req) matches
      tagged ReadReq .r: begin
        // get internal index and byte offset
        Bit#(iidx_sz) idx = truncateLSB(pack(r.addr));
        Bit#(offset_sz) offset = truncate(pack(r.addr));
        // retrieve data and rotate it appropriatly (dealing with unaligned accesses)
        function getData(i) = mem[i].sub((fromInteger(i) < offset) ? idx + 1 : idx);
        `DATAVEC data = genWith(getData);
        Bit#(TAdd#(offset_sz, 1)) rotateAmnt = fromInteger(valueOf(data_byte_sz)) - zeroExtend(offset);
        $display("before rotate by %0d = 0x%0x", rotateAmnt, data);
        data = rotateBy(data, unpack(truncate(rotateAmnt)));
        // mask usefull subset of data and return
        $display("before mask = 0x%0x",data);
        function maskData (i) = (fromInteger(i) < readBitPO(r.numBytes)) ? data[i] : 0;
        readRspFIFO.enq(genWith(maskData));
        $display("simple mem @%0t -- reading 0x%0x @ 0x%0x", $time, data, r.addr);
      end
      tagged WriteReq .w: begin
        // get internal index and byte offset
        Bit#(iidx_sz) idx = truncateLSB(pack(w.addr));
        Bit#(offset_sz) offset = truncate(pack(w.addr));
        // prepare new data and be
        `DATAVEC new_data = unpack(pack(w.data));
        Vector#(data_byte_sz, Bit#(1)) be = unpack(w.byteEnable);
        new_data = rotateBy(new_data, unpack(offset));
        be = rotateBy(be, unpack(offset));
        for (Integer i = 0; i < valueOf(data_byte_sz); i = i + 1) begin
          if (unpack(be[i]))
            mem[i].upd((fromInteger(i) < offset) ? idx + 1 : idx, new_data[i]);
        end
        $display("simple mem @%0t -- writing 0x%0x @ 0x%0x", $time, pack(new_data), w.addr);
      end
    endcase
  endmethod

  method ActionValue#(MemRsp#(data_t)) getRsp ();
    MemRsp#(data_t) rsp = tagged ReadRsp unpack(pack(readRspFIFO.first()));
    readRspFIFO.deq();
    $display("simple mem @%0t -- ", $time, fshow(rsp));
    return rsp;
  endmethod

endmodule

// Memory module
// size expressed in bytes
module mkMem#(Integer size) (Mem#(idx_t, data_t))
provisos(
  // type sizes
  Bits#(idx_t, idx_sz),
  Bits#(data_t, data_sz),
  Div#(data_sz, BitsPerByte, data_byte_sz),
  Mul#(data_byte_sz, BitsPerByte, data_sz),
  Log#(data_byte_sz, offset_sz),
  Add#(offset_sz, 1, offset_large_sz),
  Add#(offset_sz, iidx_sz, idx_sz),
  // assertion with interface type
  Add#(x, TAdd#(TLog#(data_byte_sz),1), offset_large_sz),
  Add#(x, TAdd#(TLog#(TDiv#(data_sz, BitsPerByte)),1), offset_large_sz),
  // other properties
  Literal#(idx_t),
  FShow#(data_t)
);

`define OFFSET_T Bit#(offset_sz)
`define OFFSET_LARGE_T Bit#(offset_large_sz)
`define IIDX_T Bit#(iidx_sz)
`define BE_T Bit#(data_byte_sz)

  // XXX
  // TODO implement serialization of requests
  // XXX

  // RegFile to store actual values
  RegFile#(`IIDX_T, Bit#(data_sz)) mem <- mkRegFile(0, fromInteger(size/valueOf(data_byte_sz) - 1));

  // Read request FIFOs
  FIFO#(Tuple3#(`IIDX_T, `OFFSET_T, `OFFSET_LARGE_T))
    readReqFIFO <- mkBypassFIFO;
  FIFO#(Tuple4#(Bit#(data_sz), `IIDX_T, `OFFSET_LARGE_T, `OFFSET_LARGE_T))
    readNextFIFO <- mkSizedFIFO(1);
  FIFO#(Bit#(data_sz))
    readRspFIFO <- mkSizedFIFO(1);

  // Write request FIFOs
  FIFO#(Tuple4#(`IIDX_T, `OFFSET_T, `BE_T, data_t))
    writeReqFIFO <- mkBypassFIFO;
  FIFO#(Tuple3#(`IIDX_T, Bit#(data_sz), Bit#(data_sz)))
    writeNextFIFO <- mkSizedFIFO(1);

  // utility function to slice an address
  function Tuple2#(`IIDX_T, `OFFSET_T) craftInternalIndex(idx_t idx);
    return tuple2(truncateLSB(pack(idx)), truncate(pack(idx)));
  endfunction

  // Read
  //////////////////////////////////////////////////////////////////////////////

  // First stage of a read request
  rule read_stage0;
    // look at current read request and read the data
    match {.idx, .offset, .read_width} = readReqFIFO.first();
    Bit#(data_sz) val = mem.sub(idx);
    // isolate the relevant subset of the data element
    let bitOffset = offset << valueOf(TLog#(BitsPerByte));
    let bitReadWidth = read_width << valueOf(TLog#(BitsPerByte));
    val = (val >> bitOffset) & ~(~0 << bitReadWidth);
    // compute how much bytes are left to read
    `OFFSET_LARGE_T avail_width = fromInteger(valueOf(data_byte_sz)) - zeroExtend(offset);
    `OFFSET_LARGE_T remaining_width = (avail_width >= read_width) ? 0 : read_width - avail_width;
    $display("mem @%0t -- read_width=%0d, data_w=%0d, offset=%0d, avail_width=%0d, remaining_width=%0d",$time,read_width,fromInteger(valueOf(data_byte_sz)),offset,avail_width,remaining_width);
    // check for read being over or not
    if (remaining_width > 0) begin
      readNextFIFO.enq(tuple4(val, idx + 1, remaining_width, avail_width));
      $display("mem @%0t -- read stage 0 -- (cross boundary) idx 0x%0x, offset %0d, read %0d byte(s)", $time, idx, offset, avail_width);
    end else begin
      readRspFIFO.enq(val);
      $display("mem @%0t -- read stage 0 -- idx: 0x%0x, offset: %0d", $time, idx, offset);
    end
  endrule

  // Second stage of a read request when crossing an element boundary
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
    $display("mem @%0t -- read stage 1 -- idx 0x%0x, read %0d byte(s)", $time, idx, width);
  endrule

  // Write
  //////////////////////////////////////////////////////////////////////////////

  // First stage of a write request
  rule write_stage0;
    match {.idx, .offset, .be, .data} = writeReqFIFO.first();
    // read old value
    Bit#(data_sz) old_val = mem.sub(idx);
    // prepare bit mask
    Vector#(data_byte_sz, Bit#(1)) beMask = unpack(be);
    Vector#(data_byte_sz, Bit#(BitsPerByte)) bitMask = unpack(0);
    for (Integer i = 0; i < valueOf(data_byte_sz); i = i + 1) begin
      bitMask[i] = (be[i] == 1'b1) ? ~0 : 0;
    end
    // create bitOffset
    let bitOffset = offset << valueOf(TLog#(BitsPerByte));
    // merge old data and new data
    Bit#(data_sz) new_data = pack(data) & pack(bitMask);
    Bit#(data_sz) new_val = (new_data << bitOffset) | (old_val & ~(pack(bitMask) << bitOffset));
    mem.upd(idx, new_val);
    $display("mem @%0t -- write stage 0 -- wrote 0x%0x @idx 0x%0x", $time, new_val, idx);
    // Check if there are valid Byte enable in the next memory element
    `OFFSET_LARGE_T byteShift = fromInteger(valueOf(data_byte_sz)) - zeroExtend(offset);
    let bitShift = byteShift << valueOf(TLog#(BitsPerByte));
    Bit#(data_byte_sz) more_be = be >> byteShift;
    Bit#(data_sz) more_data = new_data >> bitShift;
    Bit#(data_sz) more_bitMask = pack(bitMask) >> bitShift;
    if (more_be != 0) begin
      writeNextFIFO.enq(tuple3(idx + 1, more_bitMask, more_data));
    end else begin
      writeReqFIFO.deq();
    end
  endrule

  // Second stage of a write request when crossing an element boundary
  rule write_stage1;
    // consume request from the first stage and perform lookup
    match {.idx, .bitMask, .data} = writeNextFIFO.first();
    writeNextFIFO.deq();
    Bit#(data_sz) old_val = mem.sub(idx);
    // merge old data and new data
    Bit#(data_sz) new_val = (data & bitMask) | (old_val & ~bitMask);
    mem.upd(idx, new_val);
    $display("mem @%0t -- write stage 1 -- wrote 0x%0x @idx 0x%0x", $time, new_val, idx);
    // consume write request
    writeReqFIFO.deq();
  endrule

  // Interface
  //////////////////////////////////////////////////////////////////////////////

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
        match {.idx, .offset} = craftInternalIndex(w.addr);
        writeReqFIFO.enq(tuple4(idx, offset, w.byteEnable, w.data));
      end
    endcase
  endmethod

  method ActionValue#(MemRsp#(data_t)) getRsp ();
    MemRsp#(data_t) rsp = tagged ReadRsp unpack(readRspFIFO.first());
    readReqFIFO.deq();
    readRspFIFO.deq();
    $display("mem @%0t -- ", $time, fshow(rsp));
    return rsp;
  endmethod

endmodule

///////////////////////////////
// Simple instruction Stream //
////////////////////////////////////////////////////////////////////////////////

// XXX hex format example in test-program.hex

`ifdef MAX_ISTREAM_LENGTH
typedef TLog#(MAX_ISTREAM_LENGTH) IStreamIdxSz;
`else
typedef 12 IStreamIdxSz;
`endif

// size expressed in bytes
module mkInstStream#(String file, Integer size) (InstStream#(n))
provisos (
  Mul#(byte_sz, BitsPerByte, n)
);

  RegFile#(Bit#(IStreamIdxSz), Bit#(n)) mem <- mkRegFileLoad(file, 0, fromInteger(size/valueOf(byte_sz) - 1));
  Reg#(Bit#(IStreamIdxSz)) counter <- mkReg(0);

  rule checkInst;
    $display("instr stream @%0t -- inst %0d = 0x%0x", $time, counter, mem.sub(counter));
  endrule

  method Bit#(n) peekInst() = mem.sub(counter);
  method Action nextInst() = action counter <= counter + 1; endaction;

endmodule

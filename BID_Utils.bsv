// 2018, Alexandre Joannou, University of Cambridge

import Vector :: *;
import List :: *;
import RegFile :: *;
import BRAMCore :: *;
import FIFO :: *;

import BID_Interface :: *;
import BID_SimUtils :: *;

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

////////////////////////
// Simple data memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSimpleDMem#(Integer size) (DMem#(addr_t, data_t))
provisos(
  // type sizes
  Bits#(addr_t, addr_sz),
  Bits#(data_t, data_sz),
  Div#(data_sz, BitsPerByte, data_byte_sz),
  Mul#(BitsPerByte, data_byte_sz, data_sz),
  Log#(data_byte_sz, offset_sz),
  Add#(idx_sz, offset_sz, addr_sz),
  // show
  FShow#(addr_t),
  FShow#(data_t)
);

`define BYTE Bit#(BitsPerByte)
`define DATAVEC Vector#(data_byte_sz, Bit#(BitsPerByte))

  Vector#(data_byte_sz, RegFile#(Bit#(idx_sz), `BYTE)) mem <- replicateM(mkRegFile(0, fromInteger(size/valueOf(TMul#(data_byte_sz,data_byte_sz)) - 1)));
  FIFO#(`DATAVEC) readRspFIFO <- mkFIFO1;

  // Interface
  //////////////////////////////////////////////////////////////////////////////

  method Action sendReq (DMemReq#(addr_t, data_t) req);
    printTLogPlusArgs("BID_Utils", $format("simple mem ", fshow(req)));
    case (req) matches
      tagged ReadReq .r: begin
        // get internal index and byte offset
        Bit#(idx_sz) idx = truncateLSB(pack(r.addr));
        Bit#(offset_sz) offset = truncate(pack(r.addr));
        // retrieve data and rotate it appropriatly (dealing with unaligned accesses)
        function getData(i) = mem[i].sub((fromInteger(i) < offset) ? idx + 1 : idx);
        `DATAVEC data = genWith(getData);
        Bit#(TAdd#(offset_sz, 1)) rotateAmnt = fromInteger(valueOf(data_byte_sz)) - zeroExtend(offset);
        data = rotateBy(data, unpack(truncate(rotateAmnt)));
        // mask usefull subset of data and return
        function maskData (i) = (fromInteger(i) < readBitPO(r.numBytes)) ? data[i] : 0;
        readRspFIFO.enq(genWith(maskData));
        printTLogPlusArgs("BID_Utils", $format("simple mem -- reading 0x%0x @ 0x%0x", data, r.addr));
      end
      tagged WriteReq .w: begin
        // get internal index and byte offset
        Bit#(idx_sz) idx = truncateLSB(pack(w.addr));
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
        printTLogPlusArgs("BID_Utils", $format("simple mem -- writing 0x%0x @ 0x%0x", pack(new_data), w.addr));
      end
    endcase
  endmethod

  method ActionValue#(DMemRsp#(data_t)) getRsp ();
    DMemRsp#(data_t) rsp = tagged ReadRsp unpack(pack(readRspFIFO.first()));
    readRspFIFO.deq();
    printTLogPlusArgs("BID_Utils", $format("simple mem -- ", fshow(rsp)));
    return rsp;
  endmethod

endmodule

///////////////////////////////
// Simple instruction memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSimpleIMem#(Integer size, String file) (IMem#(addr_t, inst_t))
provisos(
  Bits#(addr_t, addr_sz),
  Bits#(inst_t, inst_sz),
  Div#(inst_sz, BitsPerByte, inst_byte_sz),
  Add#(idx_sz, TLog#(inst_byte_sz), addr_sz)
);

  BRAM_PORT#(Bit#(idx_sz), inst_t) mem <- mkBRAMCore1Load(size/valueOf(inst_byte_sz), False, file, False);

  method Action fetchInst (addr_t addr) = mem.put(False, truncateLSB(pack(addr)), ?);

  method inst_t nextInst = mem.read;

endmodule

////////////////////////////////////////////////////////////
// Simple un-pipelined shared data and instruction memory //
////////////////////////////////////////////////////////////////////////////////

typedef enum {READY, UNALIGNED_0, UNALIGNED_1, FINISH} SharedMemState deriving (Bits, Eq, FShow);
// size expressed in bytes
module mkSharedMem#(Integer size, String file) (Mem#(addr_t, inst_t, data_t))
provisos(
  // type sizes
  Bits#(addr_t, addr_sz), Bits#(inst_t, inst_sz), Bits#(data_t, data_sz),
  Div#(inst_sz, BitsPerByte, inst_byte_sz), Div#(data_sz, BitsPerByte, data_byte_sz),
  Max#(inst_sz, data_sz, chunk_sz),
  Div#(chunk_sz, chunk_byte_sz, BitsPerByte), Mul#(BitsPerByte, chunk_byte_sz, chunk_sz),
  Add#(idx_sz, TLog#(chunk_byte_sz), addr_sz),
  Add#(ofst_sz, idx_sz, addr_sz),
  Mul#(inst_sz, inst_per_chunk, chunk_sz),
  Add#(a__, TLog#(inst_per_chunk), addr_sz), // for the inst addr truncation
  // XXX only support data_sz >= inst_sz, so currently chunk_sz==data_sz
  Log#(data_byte_sz, ofst_sz),
  Log#(TAdd#(1, TDiv#(data_sz, 8)), TAdd#(TLog#(data_byte_sz), 1)),
  Add#(b__, ofst_sz, TAdd#(TLog#(data_byte_sz), 1)),
  Add#(c__, data_byte_sz, chunk_byte_sz), // for the write enable zeroExtend
  Add#(d__, data_sz, chunk_sz), // for the data zeroExtend
  Div#(data_sz, BitsPerByte, data_byte_sz),
  Log#(TDiv#(data_sz, BitsPerByte), TLog#(data_byte_sz)), // XXX why is this need when data_byte_sz is already defined ?
  Add#(e__, TDiv#(data_sz, BitsPerByte), chunk_byte_sz), // XXX
  Add#(f__, inst_sz, chunk_sz), // for the truncation when returning an inst
  // Literal instances
  Literal#(addr_t), Literal#(inst_t), Literal#(data_t),
  // FShow instances
  FShow#(addr_t), FShow#(inst_t), FShow#(data_t)
);

  // helper functions
  //////////////////////////////////////////////////////////////////////////////

  // internal request "unpacked" representation
`define IN_REQ Tuple7#(\
      Bool,\
      Bit#(TAdd#(TLog#(data_byte_sz),1)),\
      Bit#(idx_sz),\
      Bit#(ofst_sz),\
      Bit#(chunk_byte_sz),\
      Bit#(chunk_sz),\
      Bit#(TAdd#(ofst_sz, 1)))

  function `IN_REQ unpackReq(DMemReq#(addr_t, data_t) req);
    Bool isRead = True;
    Bit#(TAdd#(TLog#(data_byte_sz),1)) numBytes = 0;
    Bit#(idx_sz) idx = ?;
    Bit#(ofst_sz) byteOffset = ?;
    Bit#(chunk_byte_sz) writeen = 0;
    Bit#(chunk_sz) data = ?;
    case (req) matches
      tagged ReadReq .r: begin // read request
        numBytes = readBitPO(r.numBytes);
        idx = truncateLSB(pack(r.addr));
        byteOffset = truncate(pack(r.addr));
      end
      tagged WriteReq .w: begin // write request
        isRead = False;
        numBytes = pack(fromInteger(valueOf(data_byte_sz)) - countZerosMSB(w.byteEnable));
        idx = truncateLSB(pack(w.addr));
        byteOffset = truncate(pack(w.addr));
        writeen = zeroExtend(w.byteEnable);
        data = zeroExtend(pack(w.data));
      end
    endcase
    Bit#(TAdd#(ofst_sz, 1)) avail  = fromInteger(valueOf(chunk_byte_sz)) - zeroExtend(byteOffset);
    Bit#(TAdd#(ofst_sz, 1)) remain = (avail >= numBytes) ? 0 : numBytes - avail;
    return tuple7(isRead, numBytes, idx, byteOffset, writeen, data, remain);
  endfunction

  // shifts and masks helpers
  function Bit#(TAdd#(TLog#(data_byte_sz), 1)) bytesBelow (Bit#(ofst_sz) o) =
    zeroExtend(o);
  function Bit#(data_byte_sz) byteMaskBelow (Bit#(ofst_sz) o) = ~((~0) << bytesBelow(o));
  function Bit#(TAdd#(TLog#(data_byte_sz), 1)) bytesAbove (Bit#(ofst_sz) o) =
    fromInteger(valueOf(data_byte_sz)) - zeroExtend(o);
  function Bit#(data_byte_sz) byteMaskAbove (Bit#(ofst_sz) o) = ~byteMaskBelow(o);
  function Bit#(TAdd#(TLog#(data_byte_sz), 4)) bitsBelow (Bit#(ofst_sz) o) =
    zeroExtend(bytesBelow(o)) << valueOf(TLog#(BitsPerByte));
  function Bit#(data_sz) bitMaskBelow (Bit#(ofst_sz) o) = ~((~0) << bitsBelow(o));
  function Bit#(TAdd#(TLog#(data_byte_sz), 4)) bitsAbove (Bit#(ofst_sz) o) =
    zeroExtend(bytesAbove(o)) << valueOf(TLog#(BitsPerByte));
  function Bit#(data_sz) bitMaskAbove (Bit#(ofst_sz) o) = ~bitMaskBelow(o);
  function Bit#(TAdd#(TLog#(data_byte_sz), 4)) largeBitsBelow (Bit#(TAdd#(TLog#(data_byte_sz), 1)) o) =
    zeroExtend(o) << valueOf(TLog#(BitsPerByte));

  // local state
  //////////////////////////////////////////////////////////////////////////////
  Reg#(SharedMemState) state <- mkReg(READY);
  // double port BRAM core
  BRAM_DUAL_PORT_BE#(Bit#(idx_sz), Bit#(chunk_sz), chunk_byte_sz)
    mem <- mkBRAMCore2BELoad(size/valueOf(chunk_byte_sz), False, file, False);
  Bit#(chunk_sz) dataA = mem.a.read();
  Bit#(chunk_sz) dataB = mem.b.read();
  // data response/control  FIFO
  Reg#(`IN_REQ) pendingReq <- mkRegU;
  // instruction offset within memory chunk
  Reg#(Bit#(TLog#(inst_per_chunk))) instOffset <- mkReg(0);

  // rule debug state
  rule debug_state;
    Fmt str = $format("shared mem -- ", fshow(state)) +
              $format(" -- port A data: 0x%0x", dataA) +
              $format(" -- port B data: 0x%0x", dataB);
    printTLogPlusArgs("BID_Utils", str);
  endrule
  rule debug_ifetch;
    Vector#(inst_per_chunk, Bit#(inst_sz)) insts = unpack(dataB);
    printTLogPlusArgs("BID_Utils", $format("shared mem (inst) -- reading ",fshow(insts),", selecting 0x%0x @ idx %0d", insts[instOffset], instOffset));
  endrule

  // rule for unaligned accesses behaviour
  //////////////////////////////////////////////////////////////////////////////
  rule unaligned_access (state == UNALIGNED_0);
    // read internal request
    match {.isRead,.numBytes,.idx,.byteOffset,.writeen,.data,.remain} = pendingReq;
    // derive shift values
    if (isRead) begin // READ
      pendingReq <= tuple7(isRead,numBytes,idx,byteOffset,writeen,dataA,remain);
      state <= UNALIGNED_1;
    end else begin // WRITE
      writeen = writeen >> bytesAbove(byteOffset);
      data = data >> bitsAbove(byteOffset);
      state <= READY;
    end
    mem.a.put(writeen, idx + 1, data);
  endrule

  // data interface (port a)
  //////////////////////////////////////////////////////////////////////////////
  interface DMem data;
    method Action sendReq (DMemReq#(addr_t, data_t) req) if (state == READY);
      printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- ", fshow(req)));
      // "unpack" the request
      `IN_REQ inReq = unpackReq(req);
      match {.isRead,.numBytes,.idx,.byteOffset,.writeen,.data,.remain} = inReq;
      // perform the BRAMCore access
      mem.a.put(writeen << bytesBelow(byteOffset), idx, data << bitsBelow(byteOffset));
      // set the pending req register
      pendingReq <= tuple7(isRead,numBytes,idx,byteOffset,writeen,(isRead) ? 0 : data,remain);
      // check for alignment issues
      if (remain > 0) begin
        state <= UNALIGNED_0;
        printTLogPlusArgs("BID_Utils","shared mem (data) -- un-aligned access crossing memory word boundary (extra cycle required)");
      end else if (isRead) state <= FINISH; // request done when aligned access
    endmethod
    method ActionValue#(DMemRsp#(data_t)) getRsp if (state == FINISH || state == UNALIGNED_1);
      // read internal request
      match {.isRead,.numBytes,.idx,.byteOffset,.writeen,.data,.remain} = pendingReq;
      // prepare response data
      Bit#(data_sz) rsp_data;
      if (state == FINISH) begin // single cycle access (aligned or un-aligned)
        let shiftAmnt = (byteOffset == 0) ? 0 : bitsBelow(byteOffset);
        rsp_data  = (truncate(dataA) & bitMaskAbove(byteOffset)) >> shiftAmnt;
        printTLogPlusArgs("BID_Utils", "shared mem (data)-- aligned access response");
        printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- dataA 0x%0x, bitMaskAbove(byteOffset) 0x%0x, shiftAmnt %0d, rsp_data 0x%0x", dataA, bitMaskAbove(byteOffset), shiftAmnt, rsp_data));
      end else begin // merge with already read data
        Bit#(data_sz) lowData = (truncate(data)  & bitMaskAbove(byteOffset)) >> bitsAbove(byteOffset);
        Bit#(data_sz) hiData  = (truncate(dataA) & bitMaskBelow(byteOffset)) << bitsBelow(byteOffset);
        rsp_data = hiData | lowData;
        printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- un-aligned access response (byteOffset = %0d)", byteOffset));
        printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- data 0x%0x, lowData 0x%0x, bitMaskAbove(byteOffset) 0x%0x, bitsAbove(byteOffset) %0d", data, lowData, bitMaskAbove(byteOffset), bitsAbove(byteOffset)));
        printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- dataA 0x%0x, hiData 0x%0x, bitMaskBelow(byteOffset) 0x%0x, bitsBelow(byteOffset) %0d", dataA, hiData, bitMaskBelow(byteOffset), bitsBelow(byteOffset)));
      end
      // prepare response
      Bit#(data_sz) mask = ~((~0) << largeBitsBelow(numBytes));
      DMemRsp#(data_t) rsp = tagged ReadRsp unpack(truncate(rsp_data) & mask);
      printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- reading 0x%0x @idx 0x%0x, return mask 0x%0x (from numBytes=%0d)", rsp_data, idx, mask, numBytes));
      printTLogPlusArgs("BID_Utils", $format("shared mem (data) -- ", fshow(rsp)));
      state <= READY;
      return rsp;
    endmethod
  endinterface

  // instruction interface (port b)
  //////////////////////////////////////////////////////////////////////////////
  interface IMem inst;
    method Action fetchInst (addr_t addr);
      Bit#(TLog#(inst_per_chunk)) iOfst = truncate(pack(addr)>>valueOf(TLog#(inst_byte_sz)));
      printTLogPlusArgs("BID_Utils", $format("shared mem (inst) -- fetching @ 0x%0x (instOffset %0d)", addr, iOfst));
      instOffset <= iOfst;
      mem.b.put(0, truncateLSB(pack(addr)), ?);
    endmethod
    method inst_t nextInst ();
      Vector#(inst_per_chunk, Bit#(inst_sz)) insts = unpack(dataB);
      return unpack(insts[instOffset]);
    endmethod
  endinterface

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
    printTLogPlusArgs("BID_Utils", $format("instr stream -- inst %0d = 0x%0x", counter, mem.sub(counter)));
  endrule

  method Bit#(n) peekInst() = mem.sub(counter);
  method Action nextInst() = action counter <= counter + 1; endaction;

endmodule

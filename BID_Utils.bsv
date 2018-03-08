// 2018, Alexandre Joannou, University of Cambridge

import Vector :: *;
import List :: *;
import RegFile :: *;
import BRAMCore :: *;
import FIFO :: *;
import SpecialFIFOs :: *;

import BID_Interface :: *;
import BID_Utils_UnalignedMem :: *;
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

interface PC#(type a);
  method Action _write(a x);
  method a _read();
  method a next();
endinterface
module mkPC#(a startVal) (PC#(a)) provisos(Bits#(a, n));
  Reg#(a) r[2] <- mkCReg(2, startVal);
  method Action _write(a x) = action r[0] <= x; endaction;
  method a _read() = r[0];
  method a next() = r[1];
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

///////////////////
// Simple memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSimpleMem#(Integer size) (Mem#(addr_t, data_t))
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

  method Action sendReq (MemReq#(addr_t, data_t) req);
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

  method ActionValue#(MemRsp#(data_t)) getRsp ();
    MemRsp#(data_t) rsp = tagged ReadRsp unpack(pack(readRspFIFO.first()));
    readRspFIFO.deq();
    printTLogPlusArgs("BID_Utils", $format("simple mem -- ", fshow(rsp)));
    return rsp;
  endmethod

endmodule

///////////////////////////////
// Simple instruction memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSimpleIMem#(Integer size, String file, addr_t pc) (IMem#(inst_t))
provisos(
  Bits#(addr_t, addr_sz),
  Bits#(inst_t, inst_sz),
  Div#(inst_sz, BitsPerByte, inst_byte_sz),
  Add#(idx_sz, TLog#(inst_byte_sz), addr_sz)
);

  BRAM_PORT#(Bit#(idx_sz), inst_t) mem <- mkBRAMCore1Load(size/valueOf(inst_byte_sz), False, file, False);
  FIFO#(Bit#(0)) pendingReq <- mkPipelineFIFO;

  method Action reqNext () = action
    mem.put(False, truncateLSB(pack(pc)), ?);
    pendingReq.enq(?);
  endaction;

  method ActionValue#(inst_t) get () = actionvalue
    pendingReq.deq();
    return mem.read;
  endactionvalue;

endmodule

////////////////////////////////////////
// Shared data and instruction memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSharedMem2#(Integer size, String file) (Mem2#(addr_t, t0, t1))
provisos(
  Bits#(addr_t, addr_sz), Bits#(t0, t0_sz), Bits#(t1, t1_sz),
  Max#(t0_sz, t1_sz, chunk_sz), Div#(chunk_sz, BitsPerByte, chunk_byte_sz),
  Add#(idx_sz, TLog#(chunk_byte_sz), addr_sz),
  // port0 size relationships
  Add#(a__, TDiv#(t0_sz, BitsPerByte), chunk_byte_sz),
  Add#(b__, t0_sz, chunk_sz),
  Add#(c__, TLog#(TDiv#(t0_sz, BitsPerByte)), TAdd#(TLog#(chunk_byte_sz), 1)),
  Add#(d__, TLog#(TDiv#(t0_sz, BitsPerByte)), TLog#(chunk_byte_sz)),
  Log#(TAdd#(1, TDiv#(t0_sz, BitsPerByte)), TAdd#(TLog#(TDiv#(t0_sz, BitsPerByte)), 1)),
  // port1 size relationships
  Add#(e__, TDiv#(t1_sz, BitsPerByte), chunk_byte_sz),
  Add#(f__, t1_sz, chunk_sz),
  Add#(g__, TLog#(TDiv#(t1_sz, BitsPerByte)), TAdd#(TLog#(chunk_byte_sz), 1)),
  Add#(h__, TLog#(TDiv#(t1_sz, BitsPerByte)), TLog#(chunk_byte_sz)),
  Log#(TAdd#(1, TDiv#(t1_sz, BitsPerByte)), TAdd#(TLog#(TDiv#(t1_sz, BitsPerByte)), 1)),
  // address size relationships
  Add#(i__, TLog#(TDiv#(t1_sz, BitsPerByte)), addr_sz),
  Add#(j__, TLog#(TDiv#(t0_sz, BitsPerByte)), addr_sz),
  // chunk size relashionships
  Mul#(TDiv#(chunk_sz, chunk_byte_sz), chunk_byte_sz, chunk_sz),
  // FShow instances
  FShow#(addr_t), FShow#(t0), FShow#(t1)
);

  // double port BRAM core
  BRAM_DUAL_PORT_BE#(Bit#(idx_sz), Bit#(chunk_sz), chunk_byte_sz)
    mem <- mkBRAMCore2BELoad(size/valueOf(chunk_byte_sz), False, file, False);
  Mem#(addr_t, t0) p0Ifc <- mkPortCtrl("port0", mem.a);
  Mem#(addr_t, t1) p1Ifc <- mkPortCtrl("port1", mem.b);
  // interface
  interface p0 = p0Ifc;
  interface p1 = p1Ifc;

endmodule

module mkFullMem#(Integer size, String file, addr_t pc) (FullMem#(addr_t, inst_t, data_t))
provisos(
  Bits#(addr_t, addr_sz), Bits#(inst_t, inst_sz), Bits#(data_t, data_sz),
  Max#(inst_sz, data_sz, chunk_sz), Div#(chunk_sz, BitsPerByte, chunk_byte_sz),
  Add#(idx_sz, TLog#(chunk_byte_sz), addr_sz),
  // instruction size relationships
  Add#(a__, TDiv#(inst_sz, BitsPerByte), chunk_byte_sz),
  Add#(b__, inst_sz, chunk_sz),
  Add#(c__, TLog#(TDiv#(inst_sz, BitsPerByte)), TAdd#(TLog#(chunk_byte_sz), 1)),
  Add#(d__, TLog#(TDiv#(inst_sz, BitsPerByte)), TLog#(chunk_byte_sz)),
  Log#(TAdd#(1, TDiv#(inst_sz, BitsPerByte)), TAdd#(TLog#(TDiv#(inst_sz, BitsPerByte)), 1)),
  // data size relationships
  Add#(e__, TDiv#(data_sz, BitsPerByte), chunk_byte_sz),
  Add#(f__, data_sz, chunk_sz),
  Add#(g__, TLog#(TDiv#(data_sz, BitsPerByte)), TAdd#(TLog#(chunk_byte_sz), 1)),
  Add#(h__, TLog#(TDiv#(data_sz, BitsPerByte)), TLog#(chunk_byte_sz)),
  Log#(TAdd#(1, TDiv#(data_sz, BitsPerByte)), TAdd#(TLog#(TDiv#(data_sz, BitsPerByte)), 1)),
  // address size relationships
  Add#(i__, TLog#(TDiv#(data_sz, BitsPerByte)), addr_sz),
  Add#(j__, TLog#(TDiv#(inst_sz, BitsPerByte)), addr_sz),
  // chunk size relashionships
  Mul#(TDiv#(chunk_sz, chunk_byte_sz), chunk_byte_sz, chunk_sz),
  // FShow instances
  FShow#(addr_t), FShow#(inst_t), FShow#(data_t)
);

  Mem2#(addr_t, inst_t, data_t) mem <- mkSharedMem2(size, file);
  interface IMem inst;
    method Action reqNext () =  mem.p0.sendReq(tagged ReadReq {
      addr: pc,
      numBytes: fromInteger(valueOf(TDiv#(SizeOf#(inst_t), BitsPerByte)))
    });
    method ActionValue#(inst_t) get ();
      let rsp <- mem.p0.getRsp();
      return case (rsp) matches
        tagged ReadRsp .val: val;
        default: ?;
      endcase;
    endmethod
  endinterface
  interface data = mem.p1;

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

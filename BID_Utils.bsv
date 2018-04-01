// 2018, Alexandre Joannou, University of Cambridge

import Vector :: *;
import List :: *;
import RegFile :: *;
import FIFO :: *;
import SpecialFIFOs :: *;

import BID_Interface :: *;
import BID_Utils_UnalignedMem :: *;
import BID_SimUtils :: *;
import BID_Utils_BRAM :: *;

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

// Bypassable Register
module mkBypassReg#(parameter a v) (Reg#(a)) provisos(Bits#(a, a_sz));
  Reg#(a) r[2] <- mkCReg(2, v);
  method Action _write(a x) = action r[0] <= x; endaction;
  method a _read() = r[1];
endmodule

module mkBypassRegU (Reg#(a)) provisos(Bits#(a, a_sz));
  Reg#(a) r[2] <- mkCRegU(2);
  method Action _write(a x) = action r[0] <= x; endaction;
  method a _read() = r[1];
endmodule

// PC register with "beginning of the cycle" + "next" interfaces
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

////////////////////////////////////////
// Shared data and instruction memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes

import "BDPI" mem_create = function ActionValue#(Bit#(64)) mem_create(st s)
                             provisos (Bits#(st, sw));
import "BDPI" mem_init   = function Action mem_init(Bit#(64) m, String f, Bit#(64) o);
import "BDPI" mem_read   = function dt mem_read(Bit#(64) m, at a, st s)
                             provisos (Bits#(dt, dw), Bits#(at, aw), Bits#(st, sw));
import "BDPI" mem_write  = function Action mem_write(Bit#(64) m, at a, st s, bet be, dt d)
                             provisos (Bits#(at, aw), Bits#(st, sw), Bits#(bet, bew), Bits#(dt, dw));
module mkSimSharedMem2#(Integer size, String file) (Mem2#(addr_t, t0, t1))
provisos (Bits#(addr_t, addr_sz), Bits#(t0, t0_sz), Bits#(t1, t1_sz));

  Reg#(Bool) isInitialized <- mkReg(False);
  Reg#(Bit#(64)) mem_ptr <- mkRegU;

  rule do_init (!isInitialized);
    let tmp <- mem_create(fromInteger(size));
    mem_init(tmp, file, fromInteger(0));
    mem_ptr <= tmp;
    isInitialized <= True;
  endrule

  FIFO#(MemRsp#(t0)) rsp0 <- mkPipelineFIFO;
  FIFO#(MemRsp#(t1)) rsp1 <- mkPipelineFIFO;

  interface Mem p0;
    method Action sendReq (MemReq#(addr_t, t0) req) if (isInitialized);
      case (req) matches
        tagged ReadReq .r: rsp0.enq(ReadRsp(mem_read(mem_ptr, r.addr, readBitPO(r.numBytes))));
        tagged WriteReq .w: mem_write(mem_ptr, w.addr, fromInteger(valueOf(TDiv#(SizeOf#(t0), 8))), w.byteEnable, w.data);
      endcase
    endmethod
    method ActionValue#(MemRsp#(t0)) getRsp if (isInitialized) = actionvalue rsp0.deq; return rsp0.first; endactionvalue;
  endinterface

  interface Mem p1;
    method Action sendReq (MemReq#(addr_t, t1) req) if (isInitialized);
      case (req) matches
        tagged ReadReq .r: rsp1.enq(ReadRsp(mem_read(mem_ptr, r.addr, readBitPO(r.numBytes))));
        tagged WriteReq .w: mem_write(mem_ptr, w.addr, fromInteger(valueOf(TDiv#(SizeOf#(t1), 8))), w.byteEnable, w.data);
      endcase
    endmethod
    method ActionValue#(MemRsp#(t1)) getRsp if (isInitialized) = actionvalue rsp1.deq; return rsp1.first; endactionvalue;
  endinterface

endmodule

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
  if (genC) begin
    Mem2#(addr_t, t0, t1) mem <- mkSimSharedMem2(size, file);
    interface p0 = mem.p0;
    interface p1 = mem.p1;
  end else begin
    // BRAM2
    BRAM2#(idx_sz, chunk_sz, idx_sz, chunk_sz)
      m <- mkAlteraBRAM2(size/valueOf(chunk_byte_sz), file);
    Mem#(addr_t, t0) p0Ifc <- mkPortCtrl("port0", m.p0);
    Mem#(addr_t, t1) p1Ifc <- mkPortCtrl("port1", m.p1);
    // interface
    interface p0 = p0Ifc;
    interface p1 = p1Ifc;
  end
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

// 2018, Alexandre Joannou, University of Cambridge

import Vector :: *;
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

///////////////////////////////////////////////
// Simple shared data and instruction memory //
////////////////////////////////////////////////////////////////////////////////

// size expressed in bytes
module mkSharedMem#(Integer size, String file) (Mem#(addr_t, inst_t, data_t))
provisos(
  // Literal instances
  Literal#(inst_t),
  Literal#(data_t)
);

  interface DMem data;
    method Action sendReq (DMemReq#(addr_t, data_t) req);
      //printTLogPlusArgs("BID_Utils", $format("shared mem -- ", fshow(req)));
    endmethod
    method ActionValue#(DMemRsp#(data_t)) getRsp ();
      //printTLogPlusArgs("BID_Utils", $format("shared mem -- getRsp called"));
      //return unpack(0);
      return tagged ReadRsp 0;
    endmethod
  endinterface

  interface IMem inst;
    method Action fetchInst (addr_t addr);
      //printTLogPlusArgs("BID_Utils", $format("shared mem -- fetchInst @ 0x%0x", addr));
    endmethod
    method inst_t nextInst ();
      return 0;
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

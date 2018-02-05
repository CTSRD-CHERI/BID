// 2018, Alexandre Joannou, University of Cambridge

import Printf :: *;

/////////////////////
// Interface types //
////////////////////////////////////////////////////////////////////////////////

// Type to hold an n-bit value initialized by a literal starting
// at 1 and up to 2^n rather than 0 to 2^n-1
typedef struct {
  Bit#(n) val;
} BitPO#(numeric type n) deriving (Bits);

function Bit#(TAdd#(n,1)) readBitPO (BitPO#(n) x);
  return (x.val == 0) ? fromInteger(valueOf(TExp#(n))) : zeroExtend(x.val);
endfunction

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

instance FShow#(BitPO#(n));
  function Fmt fshow(BitPO#(n) x);
    return $format("%0d", readBitPO(x));
  endfunction
endinstance

// How many bits per byte
typedef 8 BitsPerByte;

//////////////////////////////////
// Instruction Stream interface //
//////////////////////////////////

interface InstStream#(numeric type n);
  method Bit#(n) peekInst();
  method Action nextInst();
endinterface

//////////////////////////////////
// Instruction memory interface //
//////////////////////////////////

interface IMem#(type addr_t, type inst_t);
  method Action fetchInst (addr_t addr);
  method inst_t nextInst ();
endinterface

///////////////////////////
// Data memory interface //
///////////////////////////

// Mem request
typedef union tagged {
`define DATA_BYTES TDiv#(SizeOf#(data_t), BitsPerByte)
  struct {
    addr_t addr;
    BitPO#(TLog#(`DATA_BYTES)) numBytes;
  } ReadReq;
  struct {
    addr_t addr;
    Bit#(`DATA_BYTES) byteEnable;
    data_t data;
  } WriteReq;
} DMemReq#(type addr_t, type data_t) deriving (FShow);

// Mem response
typedef union tagged {
  data_t ReadRsp;
  void Failure;
} DMemRsp#(type data_t) deriving (Bits, FShow);

// Mem interface
interface DMem#(type addr_t, type data_t);
  method Action sendReq (DMemReq#(addr_t, data_t) req);
  method ActionValue#(DMemRsp#(data_t)) getRsp ();
endinterface

///////////////////////////
// Full memory interface //
///////////////////////////

interface Mem#(type addr_t, type inst_t, type data_t);
  interface DMem#(addr_t, data_t) data;
  interface IMem#(addr_t, inst_t) inst;
endinterface

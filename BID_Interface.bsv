// 2018, Alexandre Joannou, University of Cambridge

import Printf :: *;

///////////////////////////
// Simulator state types //
////////////////////////////////////////////////////////////////////////////////

typeclass ArchState#(type a);
  module initArchState(a);
  function Fmt lightReport (a s);
  function Fmt fullReport (a s);
endtypeclass

typeclass World#(type a);
  module initWorld(a);
endtypeclass

/////////////////////
// Interface types //
////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////
// Instruction Stream interface //
//////////////////////////////////

interface InstStream#(numeric type n);
  method Bit#(n) peekInst();
  method Action nextInst();
endinterface

//////////////////////
// Memory interface //
//////////////////////

// Type to hold an n-bit value initialized by a literal starting
// at 1 and up to 2^n rather than 0 to 2^n-1
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

// How many bits per byte
typedef 8 BitsPerByte;

// Mem request
typedef union tagged {
`define DATA_BYTES TDiv#(SizeOf#(data_t), BitsPerByte)
  struct {
    idx_t addr;
    BitPO#(TLog#(`DATA_BYTES)) numBytes;
  } ReadReq;
  struct {
    idx_t addr;
    Bit#(`DATA_BYTES) byteEnable;
    data_t data;
  } WriteReq;
} MemReq#(type idx_t, type data_t);

// Mem response
typedef union tagged {
  data_t ReadRsp;
  void Failure;
} MemRsp#(type data_t) deriving (Bits, FShow);

// Mem interface
interface Mem#(type idx_t, type data_t);
  method Action sendReq (MemReq#(idx_t, data_t) req);
  method ActionValue#(MemRsp#(data_t)) getRsp ();
endinterface

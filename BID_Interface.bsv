/*-
 * Copyright (c) 2018 Alexandre Joannou
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

import Printf :: *;
import List :: *;

import BID_BasicTypes :: *;

//////////////////////////
// Virtualize interface //
//////////////////////////

typeclass Virtualizable#(type a);
  module virtualize#(a x, Integer n)(Array#(a));
endtypeclass

instance Virtualizable#(Reg#(a));
  module virtualize#(Reg#(a) r, Integer n)(Array#(Reg#(a)));

    // static priority
    Wire#(Bool) canWrite[n] <- mkDCWire(n, True);

    // interface
    Reg#(a) ifc[n];

    for (Integer i = 0; i < n; i = i + 1) begin
      ifc[i] = interface Reg#(a);
        method _write(x) if (canWrite[i]) = action
          if (i < n-1) canWrite[i+1] <= False;
          r <= x;
        endaction;
        method _read = r._read;
      endinterface;
    end

    return ifc;
  endmodule

endinstance

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

interface IMem#(type inst_t);
  method Action reqNext ();
  method ActionValue#(inst_t) get ();
endinterface

///////////////////////////
// Data memory interface //
///////////////////////////

// Mem request
typedef union tagged {
`define DATA_BYTES TDiv#(SizeOf#(content_t), BitsPerByte)
  struct {
    addr_t addr;
    BitPO#(TLog#(`DATA_BYTES)) numBytes;
  } ReadReq;
  struct {
    addr_t addr;
    Bit#(`DATA_BYTES) byteEnable;
    content_t data;
  } WriteReq;
} MemReq#(type addr_t, type content_t) deriving (FShow);

// Mem response
typedef union tagged {
  content_t ReadRsp;
  void Failure;
} MemRsp#(type content_t) deriving (Bits, FShow);

// Mem interface
interface Mem#(type addr_t, type content_t);
  method Action sendReq (MemReq#(addr_t, content_t) req);
  method ActionValue#(MemRsp#(content_t)) getRsp ();
endinterface
typedef Mem DMem;

// virtualizable instance for Mem, with static priority
instance Virtualizable#(Mem#(a,b));
  module virtualize#(Mem#(a,b) mem, Integer n)(Array#(Mem#(a,b)));

    // static priority
    Wire#(Bool) canSendReq[n]  <- mkDCWire(n, True);
    List#(Array#(Reg#(Bool))) canGetRsp <- replicateM(n, mkCReg(2, False));
    Reg#(Bool) pendingReq[2]   <- mkCReg(2, False);

    // interface
    Mem#(a,b) ifc[n];

    for (Integer i = 0; i < n; i = i + 1) begin
      ifc[i] = interface Mem#(a,b);
        method sendReq(x) if (canSendReq[i] && !pendingReq[1]) = action
          if (i < n-1) canSendReq[i+1] <= False;
          canGetRsp[i][0] <= True;
          pendingReq[1] <= True;
          mem.sendReq(x);
        endaction;
        method getRsp if (canGetRsp[i][1]) = actionvalue
          pendingReq[0] <= False;
          canGetRsp[i][1] <= False;
          let rsp <- mem.getRsp;
          return rsp;
        endactionvalue;
      endinterface;
    end

    return ifc;

  endmodule
endinstance

interface Mem2#(type addr_t, type t0, type t1);
  interface Mem#(addr_t, t0) p0;
  interface Mem#(addr_t, t1) p1;
endinterface

///////////////////////////
// Full memory interface //
///////////////////////////

interface FullMem#(type addr_t, type inst_t, type data_t);
  interface DMem#(addr_t, data_t) data;
  interface IMem#(inst_t) inst;
endinterface

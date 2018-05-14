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

import Vector :: *;
import List :: *;
import RegFile :: *;
import FIFO :: *;
import SpecialFIFOs :: *;

import BID_Interface :: *;
import BID_SimUtils :: *;
import BID_Utils_BRAM :: *;

// size expressed in bytes
module mkPortCtrl#(
  String name,
  BRAM#(idx_sz, chunk_sz ) mem
) (Mem#(addr_t, content_t)) provisos(
  Bits#(addr_t, addr_sz), Bits#(content_t, content_sz),
  Div#(chunk_sz, BitsPerByte, chunk_byte_sz),
  Div#(content_sz, BitsPerByte, content_byte_sz),
  Div#(chunk_sz, content_sz, content_per_chunk),
  Log#(content_byte_sz, ofst_sz), Log#(chunk_byte_sz, chunk_ofst_sz),
  Add#(a__, content_sz, chunk_sz), // content must be smaller than or same size as chunk
  Add#(b__, chunk_ofst_sz, addr_sz), // chunk offset must be smaller than addr
  Add#(c__, TDiv#(content_sz, 8), chunk_byte_sz), // writeen must be zero extended
  Add#(d__, TAdd#(TLog#(TDiv#(content_sz, 8)), 1), TAdd#(chunk_ofst_sz, 1)), // read of the req BitPO must be zero extended
  Add#(e__, idx_sz, addr_sz), // bram idx must be smaller than addr
  Add#(f__, TAdd#(TLog#(content_byte_sz), 1), TAdd#(chunk_ofst_sz, 1)), // must zeroExtend the countZeroMSB of req writeen
  Add#(g__, ofst_sz, TAdd#(chunk_ofst_sz, 1)), // offset must be smaller than offset of chunk + 1
  // for some reason required at the readBitPo call and when asigning numBytes on writes
  Log#(TDiv#(content_sz, BitsPerByte), TLog#(content_byte_sz)),
  Log#(TAdd#(1, TDiv#(content_sz, BitsPerByte)), TAdd#(TLog#(content_byte_sz), 1)), 
  // FShow instances
  FShow#(addr_t), FShow#(content_t)
);

  // helper functions
  //////////////////////////////////////////////////////////////////////////////

  // internal request "unpacked" representation
`define IN_REQ Tuple7#(\
      Bool,\
      Bit#(TAdd#(chunk_ofst_sz,1)),\
      Bit#(idx_sz),\
      Bit#(chunk_ofst_sz),\
      Bit#(chunk_byte_sz),\
      Bit#(chunk_sz),\
      Bit#(TAdd#(TLog#(chunk_byte_sz), 1)))

  function `IN_REQ unpackReq(MemReq#(addr_t, content_t) req);
    Bool isRead = True;
    Bit#(TAdd#(chunk_ofst_sz,1)) numBytes = 0;
    Bit#(idx_sz) idx = ?;
    Bit#(chunk_ofst_sz) byteOffset = ?;
    Bit#(chunk_byte_sz) writeen = 0;
    Bit#(chunk_sz) data = ?;
    case (req) matches
      tagged ReadReq .r: begin // read request
        numBytes = zeroExtend(readBitPO(r.numBytes));
        idx = truncateLSB(pack(r.addr));
        byteOffset = truncate(pack(r.addr));
      end
      tagged WriteReq .w: begin // write request
        isRead = False;
        numBytes = pack(fromInteger(valueOf(content_byte_sz)) - zeroExtend(countZerosMSB(w.byteEnable)));
        idx = truncateLSB(pack(w.addr));
        byteOffset = truncate(pack(w.addr));
        writeen = zeroExtend(w.byteEnable);
        data = zeroExtend(pack(w.data));
      end
    endcase
    Bit#(TAdd#(chunk_ofst_sz, 1)) avail  = fromInteger(valueOf(chunk_byte_sz)) - zeroExtend(byteOffset);
    Bit#(TAdd#(chunk_ofst_sz, 1)) remain = (avail >= numBytes) ? 0 : numBytes - avail;
    return tuple7(isRead, numBytes, idx, byteOffset, writeen, data, remain);
  endfunction

  // shifts and masks helpers
  function Bit#(TAdd#(chunk_ofst_sz, 1)) bytesBelow (Bit#(chunk_ofst_sz) o) =
    zeroExtend(o);
  function Bit#(chunk_byte_sz) byteMaskBelow (Bit#(chunk_ofst_sz) o) = ~((~0) << bytesBelow(o));
  function Bit#(TAdd#(chunk_ofst_sz, 1)) bytesAbove (Bit#(chunk_ofst_sz) o) =
    fromInteger(valueOf(chunk_byte_sz)) - zeroExtend(o);
  function Bit#(chunk_byte_sz) byteMaskAbove (Bit#(chunk_ofst_sz) o) = ~byteMaskBelow(o);
  function Bit#(TAdd#(chunk_ofst_sz, 4)) bitsBelow (Bit#(chunk_ofst_sz) o) =
    zeroExtend(bytesBelow(o)) << valueOf(TLog#(BitsPerByte));
  function Bit#(chunk_sz) bitMaskBelow (Bit#(chunk_ofst_sz) o) = ~((~0) << bitsBelow(o));
  function Bit#(TAdd#(chunk_ofst_sz, 4)) bitsAbove (Bit#(chunk_ofst_sz) o) =
    zeroExtend(bytesAbove(o)) << valueOf(TLog#(BitsPerByte));
  function Bit#(chunk_sz) bitMaskAbove (Bit#(chunk_ofst_sz) o) = ~bitMaskBelow(o);
  function Bit#(TAdd#(chunk_ofst_sz, 4)) largeBitsBelow (Bit#(TAdd#(chunk_ofst_sz, 1)) o) =
    zeroExtend(o) << valueOf(TLog#(BitsPerByte));

  // local state
  //////////////////////////////////////////////////////////////////////////////
  Reg#(Bool) cross_boundary[2] <- mkCReg(2,False);
  Reg#(Bool) req_done <- mkRegU;
  Reg#(Maybe#(Tuple2#(Bit#(idx_sz), Bit#(chunk_sz)))) prev_lookup[2] <- mkCReg(2, tagged Invalid);
  Wire#(Tuple2#(Bit#(idx_sz), Bit#(chunk_sz))) prevLookupUpdt <- mkWire;
  Wire#(Tuple3#(Bit#(chunk_byte_sz), Bit#(idx_sz), Bit#(chunk_sz))) memLookup <- mkWire;
  // data response/control pipeline FIFOF
  FIFO#(`IN_REQ) pendingReq <- mkPipelineFIFO;

  // rule debug
  rule debug;
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- cross_boundary: ", fshow(cross_boundary[0]), ", req_done: ", fshow(req_done), ", prev_lookup[0]: ", fshow(prev_lookup[0])));
  endrule

  // rule sending the mem module put request
  rule mem_lookup;
    match {.writeen, .idx, .data} = memLookup;
    mem.put(writeen, idx, data);
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- sending mem.put(0x%0x,0x%0x,0x%0x)", writeen, idx, data));
  endrule

  // rule updating the prev_lookup
  rule update_prev_lookup;
    match {.idx, .data} = prevLookupUpdt;
    prev_lookup[0] <= Valid(prevLookupUpdt);
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- updating prev_lookup(0x%0x,0x%0x)", idx, data));
  endrule

  // rule for cross-boundary accesses behaviour
  //////////////////////////////////////////////////////////////////////////////
  PulseWire cross_boundary_access_fire <- mkPulseWire;
  rule cross_boundary_access (cross_boundary[0] && !req_done);
    cross_boundary_access_fire.send();
    // read internal request
    match {.isRead,.numBytes,.idx,.byteOffset,.writeen,.data,.remain} = pendingReq.first();
    // derive shift values
    if (isRead) begin // READ
      prevLookupUpdt <= tuple2(idx, mem.peek);
      req_done <= True; // signal end of request
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- done read"));
    end else begin // WRITE
      writeen = writeen >> bytesAbove(byteOffset);
      data = data >> bitsAbove(byteOffset);
      // retire the request
      cross_boundary[0] <= False;
      pendingReq.deq();
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- done write"));
    end
    memLookup <= tuple3(writeen, idx + 1, data);
  endrule

  // interface
  //////////////////////////////////////////////////////////////////////////////
  method Action sendReq (MemReq#(addr_t, content_t) req) if (!cross_boundary[1] && !cross_boundary_access_fire); // XXX possibly test for not full of pipeline fifo ?
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- ", fshow(req)));
    // "unpack" the request
    `IN_REQ inReq = unpackReq(req);
    match {.isRead,.numBytes,.idx,.byteOffset,.writeen,.data,.remain} = inReq;
    // check for cross boundary access
    Bool isCrossBoundary = remain > 0;
    Bool isSingleCycle = !isCrossBoundary;
    // prepare mem put request
    let req_writeen = writeen << bytesBelow(byteOffset);
    let req_idx = idx;
    let req_data = data << bitsBelow(byteOffset);
    // check previous lookup for match and alter the mem request / single cycle accordingly
    match {.pidx, .pdata} = fromMaybe(?, prev_lookup[1]);
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- isRead: ", fshow(isRead),", isCrossBoundary: ", fshow(isCrossBoundary),", pidx: 0x%0x, idx: 0x%0x", pidx, idx));
    if (isValid(prev_lookup[1]) && (pidx == idx) && isRead && isCrossBoundary) begin
      req_idx = idx + 1;
      isSingleCycle = True;
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- use prev_lookup @idx 0x%0x to avoid extra lookup", idx));
    end
    // on reads or cross boundary accesses, enqueue a pending request
    if (isRead || isCrossBoundary) pendingReq.enq(tuple7(isRead,numBytes,idx,byteOffset,writeen,(isRead) ? 0 : data,remain));
    // set control registers
    cross_boundary[1] <= isCrossBoundary;
    req_done <= isSingleCycle;
    // perform the BRAMCore access
    memLookup <= tuple3(req_writeen, req_idx, req_data);
  endmethod
  method ActionValue#(MemRsp#(content_t)) getRsp if (req_done);
    // read internal request
    match {.isRead,.numBytes,.idx,.byteOffset,.writeen,.data,.remain} = pendingReq.first();
    // prepare response data
    Bit#(chunk_sz) rsp_data = ?;
    if (cross_boundary[0]) begin // merge with previously looked up  data
      match {.pidx, .pdata} = fromMaybe(?, prev_lookup[0]);
      Bit#(chunk_sz) lowData = pdata;
      lowData = (lowData  & bitMaskAbove(byteOffset)) >> bitsBelow(byteOffset);
      Bit#(chunk_sz) hiData  = truncate(mem.peek);
      hiData  = (hiData & bitMaskBelow(byteOffset)) << bitsAbove(byteOffset);
      rsp_data = hiData | lowData;
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- un-aligned access response (byteOffset = %0d)", byteOffset));
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- lowData 0x%0x -- prev_lookup[0]", lowData, fshow(prev_lookup[0]),", bitMaskAbove(byteOffset) 0x%0x, bitsBelow(byteOffset) %0d", bitMaskAbove(byteOffset), bitsBelow(byteOffset)));
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- hiData 0x%0x -- mem.peek 0x%0x, bitMaskBelow(byteOffset) 0x%0x, bitsAbove(byteOffset) %0d", hiData, mem.peek, bitMaskBelow(byteOffset), bitsAbove(byteOffset)));
      cross_boundary[0] <= False; // Reset to allow sendReq to fire again
    end else begin // single cycle access (aligned or un-aligned)
      let shiftAmnt = (byteOffset == 0) ? 0 : bitsBelow(byteOffset);
      rsp_data  = (mem.peek & bitMaskAbove(byteOffset)) >> shiftAmnt;
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- single cycle response"));
      printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- rsp_data 0x%0x, mem.peek 0x%0x, bitMaskAbove(byteOffset) 0x%0x, shiftAmnt %0d", rsp_data, mem.peek, bitMaskAbove(byteOffset), shiftAmnt));
    end
    // updating prev_lookup
    prevLookupUpdt <= tuple2((cross_boundary[0]) ? idx + 1 : idx, mem.peek);
    // prepare response
    Bit#(content_sz) mask = ~((~0) << largeBitsBelow(numBytes));
    MemRsp#(content_t) rsp = tagged ReadRsp unpack(truncate(rsp_data) & mask);
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- reading 0x%0x @idx 0x%0x, return mask 0x%0x (from numBytes=%0d)", rsp_data, idx, mask, numBytes));
    printTLogPlusArgs("BID_Utils", $format("port controller (", fshow(name), ") -- ", fshow(rsp)));
    pendingReq.deq(); // retire request
    return rsp;
  endmethod

endmodule

#-
# Copyright (c) 2018 Alexandre Joannou
# All rights reserved.
#
# This software was developed by SRI International and the University of
# Cambridge Computer Laboratory (Department of Computer Science and
# Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
# DARPA SSITH research programme.
#
# @BERI_LICENSE_HEADER_START@
#
# Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
# license agreements.  See the NOTICE file distributed with this work for
# additional information regarding copyright ownership.  BERI licenses this
# file to you under the BERI Hardware-Software License, Version 1.0 (the
# "License"); you may not use this file except in compliance with the
# License.  You may obtain a copy of the License at:
#
#   http://www.beri-open-systems.org/legal/license-1-0.txt
#
# Unless required by applicable law or agreed to in writing, Work distributed
# under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations under the License.
#
# @BERI_LICENSE_HEADER_END@
#

# BSV compiler flags
RECIPEDIR = /home/aj443/devstuff/Recipe
BITPATDIR = /home/aj443/devstuff/BitPat
BSVPATH = +:$(RECIPEDIR):$(BITPATDIR)
BSC = bsc
BSCFLAGS = -p $(BSVPATH) -show-range-conflict
BSCFLAGS += -show-schedule -sched-dot
#BSCFLAGS += -show-rule-rel \* \*
ifdef NO_LOGS
BSCFLAGS += -D NO_LOGS
endif
# Bluespec is not compatible with gcc > 4.9
# This is actually problematic when using $test$plusargs
CC = gcc-4.9
CXX = g++-4.9

# Top level module
TOPFILE = Example.bsv
TOPMOD = bidExample

.PHONY: sim
sim: $(TOPMOD)

$(TOPMOD): *.bsv *.c
	$(BSC) $(BSCFLAGS) -sim -g $(TOPMOD) -u $(TOPFILE)
	CC=$(CC) CXX=$(CXX) $(BSC) $(BSCFLAGS) -sim -o $(TOPMOD) -e $(TOPMOD) *.c

verilog: *.bsv
	$(BSC) $(BSCFLAGS) -D NO_LOGS -verilog -g $(TOPMOD) -u $(TOPFILE)

.PHONY: clean
clean:
	rm -f *.sched *.dot *.cxx *.o *.h *.ba *.bo *.so *.ipinfo vpi_wrapper_*.c $(TOPMOD)

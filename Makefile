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
RECIPEDIR = Recipe
BITPATDIR = BitPat
BLUESTUFFDIR = BlueStuff
AXIDIR = $(BLUESTUFFDIR)/AXI
BLUEBASICSDIR = $(BLUESTUFFDIR)/BlueBasics
BLUEUTILSDIR = $(BLUESTUFFDIR)/BlueUtils
BSVPATH = +:$(RECIPEDIR):$(BITPATDIR):$(AXIDIR):$(BLUESTUFFDIR):$(BLUEBASICSDIR):$(BLUEUTILSDIR)
BSC = bsc
BSCFLAGS = -p $(BSVPATH)
ifdef NO_LOGS
BSCFLAGS += -D NO_LOGS
endif

# generated files directories
BUILDDIR = build
BDIR = $(BUILDDIR)/bdir
SIMDIR = $(BUILDDIR)/simdir

OUTPUTDIR = output
VDIR = $(OUTPUTDIR)/vdir
INFODIR = $(OUTPUTDIR)/info

BSCFLAGS += -bdir $(BDIR)
BSCFLAGS += -info-dir $(INFODIR)
BSCFLAGS += -show-schedule -sched-dot
BSCFLAGS += -show-range-conflict
#BSCFLAGS += -show-rule-rel \* \*
#BSCFLAGS += -steps-warn-interval n

# Bluespec is not compatible with gcc > 4.9
# This is actually problematic when using $test$plusargs
CC = gcc-4.8
CXX = g++-4.8

# Top level module
TOPFILE = Example.bsv
TOPMOD = bidExample

# Top level module
SIMTOPFILE = Example.bsv
SIMTOPMOD = bidExample
VERILOGTOPFILE = $(SIMTOPFILE)
VERILOGTOPMOD = $(SIMTOPMOD)


.PHONY: sim verilog

all: sim
sim: $(SIMTOPMOD)

$(SIMTOPMOD): *.bsv
	mkdir -p $(INFODIR) $(BDIR) $(SIMDIR) $(OUTPUTDIR)
	$(BSC) $(BSCFLAGS) -simdir $(SIMDIR) -sim -g $(SIMTOPMOD) -u $(SIMTOPFILE)
	CC=$(CC) CXX=$(CXX) $(BSC) $(BSCFLAGS) -simdir $(SIMDIR) -sim -o $(OUTPUTDIR)/$(SIMTOPMOD) -e $(SIMTOPMOD) $(BLUEUTILSDIR)/*.c

verilog: *.bsv
	mkdir -p $(INFODIR) $(BDIR) $(VDIR)
	$(BSC) $(BSCFLAGS) -vdir $(VDIR) -opt-undetermined-vals -unspecified-to X -D NO_LOGS -verilog -g $(VERILOGTOPMOD) -u $(VERILOGTOPFILE)

.PHONY: clean mrproper
clean:
	rm -rf $(BDIR) $(SIMDIR)
mrproper: clean
	rm -rf $(INFODIR) $(VDIR) $(OUTPUTDIR) $(BUILDDIR)

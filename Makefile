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

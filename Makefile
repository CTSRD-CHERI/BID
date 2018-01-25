# BSV compiler flags
BITPATDIR=/home/aj443/devstuff/BitPat
BSVPATH=+:$(BITPATDIR)
BSC = bsc
BSCFLAGS = -p $(BSVPATH) -check-assert

# Top level module
TOPFILE = Top.bsv
TOPMOD = top

.PHONY: sim
sim: $(TOPMOD)

$(TOPMOD): *.bsv *.c
	$(BSC) $(BSCFLAGS) -sim -g $(TOPMOD) -u $(TOPFILE)
	$(BSC) $(BSCFLAGS) -sim -o $(TOPMOD) -e $(TOPMOD) *.c

verilog: *.bsv
	$(BSC) $(BSCFLAGS) -verilog -g $(TOPMOD) -u $(TOPFILE)

.PHONY: clean
clean:
	rm -f *.cxx *.o *.h *.ba *.bo *.so *.ipinfo *.v vpi_wrapper_*.c $(TOPMOD)

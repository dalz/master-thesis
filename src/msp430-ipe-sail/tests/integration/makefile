.DEFAULT_GOAL := all
.PHONY: all cleanIntermediate
.SECONDARY:

compiler = msp430-gcc
compiler_arg = -mmcu=MSP430FG479

simulator_ref = msp430-run
simulator_self = ../../msp430

pythonFolder = pythonFiles

memevaluator = $(pythonFolder)/memevaluator.py
instevaluator = $(pythonFolder)/instevaluator.py
agragator = $(pythonFolder)/resultagregator.py

CSRC = c-testsuite
MSPC = _msp_c_files
MSPEXEC = _msp_exec_files
MSPRES = _msp_res_files
MEMTRACE = _mem_files
INSTRACE = _ins_files
REF = _ref_files
SELF = _self_files
TRACECOMPARERES = _res_files

#https://www.reddit.com/r/C_Programming/comments/u83pdl/comment/i5mr283/?utm_source=share&utm_medium=web3x&utm_name=web3xcss&utm_term=1&utm_content=share_button
SRCS=$(wildcard $(CSRC)/*.c)

#https://stackoverflow.com/questions/10276202/exclude-source-file-in-compilation-using-makefile
IGNORE = $(filter-out $(CSRC)/00162.c   $(CSRC)/00174.c  $(CSRC)/00195.c $(CSRC)/00200.c $(CSRC)/00204.c $(CSRC)/00205.c $(CSRC)/00216.c, $(SRCS))
#                      restrict unkown   collision        collision      arv argc         collision      collision        collision 

RESFILESINST=$(IGNORE:$(CSRC)/%.c=$(MSPRES)/$(INSTRACE)/$(TRACECOMPARERES)/%.out)
RESFILESMEM=$(IGNORE:$(CSRC)/%.c=$(MSPRES)/$(MEMTRACE)/$(TRACECOMPARERES)/%.out)
ALLRESFILES = $(RESFILESINST) $(RESFILESMEM)

all: res.csv

res.csv: $(ALLRESFILES) $(agragator)
	python3 $(agragator) $(MSPRES)/$(MEMTRACE)/$(TRACECOMPARERES)/ $(MSPRES)/$(INSTRACE)/$(TRACECOMPARERES)/ $@

$(MSPRES)/$(INSTRACE)/$(TRACECOMPARERES)/%.out: $(MSPRES)/$(INSTRACE)/$(REF)/%.out $(MSPRES)/$(INSTRACE)/$(SELF)/%.out $(instevaluator) $(MSPRES)/$(INSTRACE)/$(TRACECOMPARERES)/.f
	python3 $(instevaluator) $< $(word 2,$^) > $@

$(MSPRES)/$(MEMTRACE)/$(TRACECOMPARERES)/%.out: $(MSPRES)/$(MEMTRACE)/$(REF)/%.out $(MSPRES)/$(MEMTRACE)/$(SELF)/%.out $(memevaluator) $(MSPRES)/$(MEMTRACE)/$(TRACECOMPARERES)/.f
	python3 $(memevaluator) $< $(word 2,$^) > $@

$(MSPRES)/$(MEMTRACE)/$(REF)/%.out: $(MSPEXEC)/%.c $(MSPRES)/$(MEMTRACE)/$(REF)/.f
	- $(simulator_ref) --architecture msp430 --trace-memory $< 2> $@
	head -n -3 $@ > tmp
	mv tmp $@

$(MSPRES)/$(INSTRACE)/$(REF)/%.out: $(MSPEXEC)/%.c $(MSPRES)/$(INSTRACE)/$(REF)/.f
	- $(simulator_ref) --architecture msp430 --trace-insn $< 2> $@
	head -n -3 $@ > tmp
	mv tmp $@

$(MSPRES)/$(MEMTRACE)/$(SELF)/%.out: $(MSPEXEC)/%.c $(simulator_self) $(MSPRES)/$(MEMTRACE)/$(SELF)/.f
	- $(simulator_self) -v 0x000010 -e $< > $@

$(MSPRES)/$(INSTRACE)/$(SELF)/%.out: $(MSPEXEC)/%.c $(simulator_self) $(MSPRES)/$(INSTRACE)/$(SELF)/.f
	- $(simulator_self) -v 0x000002 -e $< > $@

$(MSPEXEC)/%.c: $(MSPC)/%.c $(MSPEXEC)/.f
	$(compiler) -L../../../../dep/msp430-gcc-support-files/include/ $< -o $@ $(compiler_arg)


$(MSPC)/%.c: $(CSRC)/%.c $(MSPC)/.f
	cp prerequisite.c $@
	sed "s/main/renamedmain/" $< >> $@
#often used as var names but are defined by the msp430 include
	sed -i "s/\bC\b/renamedC/g" $@
	sed -i "s/\bZ\b/renamedZ/g" $@
	sed -i "s/\bN\b/renamedN/g" $@
	sed -i "s/\bV\b/renamedV/g" $@

	cat new_main.c >> $@

%/.f:
	mkdir -p $(dir $@)
	touch $@

cleanIntermediate:
	rm -rf $(MSPC)
	rm -rf $(MSPEXEC)
	rm -rf $(MSPRES)

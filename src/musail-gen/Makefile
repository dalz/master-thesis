.PHONY: all

SAIL_SRCS := $(shell make -sC ../msp430-ipe-sail print-sail-srcs | sed -E 's#(^| )# ../msp430-ipe-sail/#g')

all:
	make -C ../msp430-ipe-sail
	sail --katamaran --katamaran-config configuration.lisp $(SAIL_SRCS)

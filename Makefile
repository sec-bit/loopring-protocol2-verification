COQ_VERSION=$(shell coqc --version | egrep -o 'version 8.[0-9]' | egrep -o '8.[0-9]')
COQ_MAKEFILE_FLAGS ?=

ifeq ($(COQ_VERSION), 8.8)
    COQ_MAKEFILE_FLAGS += -arg -w -arg -notation-overridden,-redundant-canonical-projection
endif

all: Makefile.coq
	make -f $<

Makefile.coq: _CoqProject
	coq_makefile $(COQ_MAKEFILE_FLAGS) -f $< -o $@

clean: Makefile.coq
	make -f $< clean
	rm -f $< $<.conf
	rm -f .*.aux

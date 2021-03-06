TOP=../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

outofmem-prep::
	'$(TEST_HC)' $(TEST_HC_OPTS) -v0 --make -fforce-recomp outofmem.hs -o outofmem

outofmem::
	@$(MAKE) outofmem-prep
	@ulimit -v 10000000 2>/dev/null; ./outofmem || echo "exit($$?)"

outofmem2-prep::
	'$(TEST_HC)' $(TEST_HC_OPTS) -v0 -rtsopts --make -fforce-recomp outofmem2.hs -o outofmem2

outofmem2::
	@$(MAKE) outofmem2-prep
	@ulimit -v 1000000 2>/dev/null; ./outofmem2 +RTS -M5m -RTS || echo "exit($$?)"

T2615-prep:
	$(RM) libfoo_T2615.so
	'$(TEST_HC)' $(TEST_HC_OPTS) -fPIC -c libfoo_T2615.c -o libfoo_T2615.o
	'$(TEST_HC)' $(TEST_HC_OPTS) -shared -no-auto-link-packages libfoo_T2615.o -o libfoo_T2615.so

.PHONY: T4059
T4059:
	$(RM) T4059_c.o T4059.o T4059.hi
	'$(TEST_HC)' $(TEST_HC_OPTS) -v0 --make T4059 T4059_c.c
	./T4059

exec_signals-prep:
	$(CC) -o exec_signals_child exec_signals_child.c
	$(CC) -o exec_signals_prepare exec_signals_prepare.c

.PHONY: T4850
T4850:
	$(RM) T4850.o T4850.hi T4850$(exeext)
	"$(TEST_HC)" $(TEST_HC_OPTS) -v0 -rtsopts -debug -threaded --make T4850
	./T4850 +RTS -s 2>&1 | grep TASKS | sed 's/^ *TASKS: *\([0-9]*\).*$$/\1/'

.PHONY: T5423
T5423:
	$(RM) T5423_cmm.o T5423.o T5423.hi T5423$(exeext)
	"$(TEST_HC)" $(TEST_HC_OPTS) -v0 -c T5423_cmm.cmm
	"$(TEST_HC)" $(TEST_HC_OPTS) -v0 -c T5423.hs
	"$(TEST_HC)" $(TEST_HC_OPTS) -v0 T5423.o T5423_cmm.o -o T5423$(exeext)
	./T5423

# Naming convention: 'T5423_' obj-way '_' obj-src
# obj-way ::= v | dyn
# obj-src ::= gcc // using __attribute__(constructor)
#           | asm // manually laid out sections
# $(0) = obj-src

define run_T5435_v
$(RM) T5435_load_v_$(1) T5435_v_$(1)$(exeext)
'$(TEST_HC)' $(TEST_HC_OPTS) -optc-D$(HostOS)_HOST_OS=1 -v0 -c T5435_$(1).c -o T5435_load_v_$(1).o
'$(TEST_HC)' $(TEST_HC_OPTS) -v0 T5435.hs -osuf main_v_$(1)_o -o T5435_v_$(1)$(exeext)
./T5435_v_$(1) v ./T5435_load_v_$(1).o
endef

define run_T5435_dyn
$(RM) T5435_load_dyn_$(1) T5435_dyn_$(1)$(exeext)
'$(TEST_HC)' $(filter-out -rtsopts, $(TEST_HC_OPTS)) -optc-D$(HostOS)_HOST_OS=1 -v0 -fPIC -shared -c T5435_$(1).c -osuf dyn_$(1)_o -o T5435_load_dyn_$(1)$(dllext)
'$(TEST_HC)' $(TEST_HC_OPTS) -v0 T5435.hs -osuf main_dyn_$(1)_o -o T5435_dyn_$(1)$(exeext)
./T5435_dyn_$(1) dyn ./T5435_load_dyn_$(1)$(dllext)
endef

.PHONY: T5435_v_gcc
T5435_v_gcc :
	$(call run_T5435_v,gcc)

.PHONY: T5435_v_asm
T5435_v_asm :
	$(call run_T5435_v,asm)

.PHONY: T5435_dyn_gcc
T5435_dyn_gcc :
	$(call run_T5435_dyn,gcc)

.PHONY: T5435_dyn_asm
T5435_dyn_asm :
	$(call run_T5435_dyn,asm)

T6006_setup :
	'$(TEST_HC)' $(TEST_HC_OPTS) -c T6006.hs

T8124_setup :
	'$(TEST_HC)' $(TEST_HC_OPTS) -c T8124.hs

ifeq "$(TARGETPLATFORM)" "i386-unknown-mingw32"
T7037_CONST = const
else
T7037_CONST =
endif
.PHONY: T7037
T7037:
	$(RM) 7037.o 7037.hi 7037$(exeext)
	"$(TEST_HC)" $(TEST_HC_OPTS) T7037.hs -v0
	"$(TEST_HC)" -optc-DT7037_CONST=$(T7037_CONST) $(filter-out -rtsopts, $(TEST_HC_OPTS)) T7037_main.c -v0 -o T7037_main -no-hs-main
	./T7037_main

T7040_ghci_setup :
	'$(TEST_HC)' $(TEST_HC_OPTS) $(ghciWayFlags) -c T7040_ghci_c.c

LOCAL_GHC_PKG = '$(GHC_PKG)' --no-user-package-db

BASE_DIR = $(shell $(LOCAL_GHC_PKG) field base library-dirs | sed 's/^[^:]*: *//')
BASE_LIB = $(shell $(LOCAL_GHC_PKG) field base hs-libraries | sed 's/^[^:]*: *//')
GHC_PRIM_DIR = $(shell $(LOCAL_GHC_PKG) field ghc-prim library-dirs | sed 's/^[^:]*: *//')
GHC_PRIM_LIB = $(shell $(LOCAL_GHC_PKG) field ghc-prim hs-libraries | sed 's/^[^:]*: *//')
# We need to get first library directory here in order to get rid of
# system gmp library directory installation when ghc is configured
# with --with-gmp-libraries=<dir> parameter
INTEGER_GMP_DIR = $(shell $(LOCAL_GHC_PKG) field integer-gmp library-dirs \
	| sed 's/^[^:]*: *//' | head -1)
INTEGER_GMP_LIB = $(shell $(LOCAL_GHC_PKG) field integer-gmp hs-libraries | sed 's/^.*: *//')

BASE        = $(BASE_DIR)/lib$(BASE_LIB).a
GHC_PRIM    = $(GHC_PRIM_DIR)/lib$(GHC_PRIM_LIB).a
INTEGER_GMP = $(INTEGER_GMP_DIR)/lib$(INTEGER_GMP_LIB).a

.PHONY: linker_unload
linker_unload:
	$(RM) Test.o Test.hi
	"$(TEST_HC)" $(TEST_HC_OPTS) -c Test.hs -v0
	# -rtsopts causes a warning
	"$(TEST_HC)" $(filter-out -rtsopts, $(TEST_HC_OPTS)) linker_unload.c -o linker_unload -no-hs-main -optc-Werror -debug -optc-g
	./linker_unload $(BASE) $(GHC_PRIM) $(INTEGER_GMP)

# -----------------------------------------------------------------------------
# Testing failures in the RTS linker.  We should be able to repeatedly
# load bogus object files of various kinds without crashing and
# without any memory leaks.
#
# Check for memory leaks manually by running e.g.
#
# make linker_error1
# valgrind --leak-check=full --show-reachable=yes ./linker_error1 linker_error1_o.o

# linker_error1: not a valid object file

.PHONY: linker_error1
linker_error1:
	"$(TEST_HC)" -c linker_error.c -o linker_error1.o
	"$(TEST_HC)" linker_error1.o -o linker_error1 -no-hs-main -optc-g -debug
	./linker_error1 linker_error.c

# linker_error2: the object file has an unknown symbol (fails in
# resolveObjs())

.PHONY: linker_error2
linker_error2:
	"$(TEST_HC)" -c linker_error.c -o linker_error2.o
	"$(TEST_HC)" -c linker_error2.c -o linker_error2_o.o
	"$(TEST_HC)" linker_error2.o -o linker_error2 -no-hs-main -optc-g -debug
	./linker_error2 linker_error2_o.o

# linker_error3: the object file duplicates an existing symbol (fails
# in loadObj())

.PHONY: linker_error3
linker_error3:
	"$(TEST_HC)" -c linker_error.c -o linker_error3.o
	"$(TEST_HC)" -c linker_error3.c -o linker_error3_o.o
	"$(TEST_HC)" linker_error3.o -o linker_error3 -no-hs-main -optc-g -debug
	./linker_error3 linker_error3_o.o

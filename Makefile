all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

ifeq ($(USE_GIT_SUBMODULES),yes)

# This is what we have to do if we cannot rely on things installed via OPAM
Makefile.coq: Make
	$(COQBIN)coq_makefile -f Make -o Makefile.coq -R containers/theories Containers -R nfix/theories Nfix -R counting/theories Counting -I nfix/src -I containers/src -I counting/src

else

# This is what we do if we can rely on things installed via OPAM
Makefile.coq: Make
	$(COQBIN)coq_makefile -f Make -o Makefile.coq

endif


%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean

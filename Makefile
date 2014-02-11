#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile Vtrunk      ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile 
#

.DEFAULT_GOAL := all

# 
# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# TIMECMD set a command to log .v compilation time;
# TIMED if non empty, use the default time command as TIMECMD;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (user: %U mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

OCAMLLIBS?=-I ../Counting/src\
  -I ../Nfix/src\
  -I ../Containers/src\
  -I tests\
  -I src
COQLIBS?=-I ../Counting/src\
  -I ../Nfix/src\
  -I ../Containers/src\
  -I tests\
  -I src -R ../Counting/theories Counting\
  -R ../Nfix/theories Nfix\
  -R ../Containers/theories Containers\
  -R theories Ergo
COQDOCLIBS?=-R ../Counting/theories Counting\
  -R ../Nfix/theories Nfix\
  -R ../Containers/theories Containers\
  -R theories Ergo

##########################
#                        #
# Variables definitions. #
#                        #
##########################

CAMLP4OPTIONS=-loc loc
COQDOC=$(COQBIN)coqdoc -interpolate -utf8

OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8
COQC?=$(TIMER) "$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"
COQMKTOP?="$(COQBIN)coqmktop"

COQSRCLIBS?=-I "$(COQLIB)kernel" -I "$(COQLIB)lib" \
  -I "$(COQLIB)library" -I "$(COQLIB)parsing" -I "$(COQLIB)pretyping" \
  -I "$(COQLIB)interp" -I "$(COQLIB)printing" -I "$(COQLIB)intf" \
  -I "$(COQLIB)proofs" -I "$(COQLIB)tactics" -I "$(COQLIB)tools" \
  -I "$(COQLIB)toplevel" -I "$(COQLIB)grammar" \
  -I $(COQLIB)/plugins/Derive \
  -I $(COQLIB)/plugins/btauto \
  -I $(COQLIB)/plugins/cc \
  -I $(COQLIB)/plugins/decl_mode \
  -I $(COQLIB)/plugins/extraction \
  -I $(COQLIB)/plugins/firstorder \
  -I $(COQLIB)/plugins/fourier \
  -I $(COQLIB)/plugins/funind \
  -I $(COQLIB)/plugins/micromega \
  -I $(COQLIB)/plugins/nsatz \
  -I $(COQLIB)/plugins/omega \
  -I $(COQLIB)/plugins/quote \
  -I $(COQLIB)/plugins/romega \
  -I $(COQLIB)/plugins/rtauto \
  -I $(COQLIB)/plugins/setoid_ring \
  -I $(COQLIB)/plugins/syntax \
  -I $(COQLIB)/plugins/xml
ZFLAGS=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP4LIB)

CAMLC?=$(OCAMLC) -c -rectypes
CAMLOPTC?=$(OCAMLOPT) -c -rectypes
CAMLLINK?=$(OCAMLC) -rectypes
CAMLOPTLINK?=$(OCAMLOPT) -rectypes
GRAMMARS?=grammar.cma
ifeq ($(CAMLP4),camlp5)
CAMLP4EXTEND=pa_extend.cmo q_MLast.cmo pa_macro.cmo
else
CAMLP4EXTEND=
endif
PP?=-pp '"$(CAMLP4O)" -I "$(CAMLLIB)" -I . $(COQSRCLIBS) compat5.cmo \
  $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl'

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=tests/TestErgo.v\
  tests/Generators.v\
  tests/GeneratorsNG.v\
  tests/GeneratorsEq.v\
  tests/EinsteinEasy.v\
  tests/EinsteinEasy2.v\
  tests/Demo.v\
  tests/AltDemo.v\
  theories/Use.v\
  theories/Uf.v\
  theories/Theory.v\
  theories/TheoryArith.v\
  theories/Term.v\
  theories/TermUtils.v\
  theories/TacticLazy.v\
  theories/SemLazy.v\
  theories/Semantics.v\
  theories/Sat.v\
  theories/SatCaml.v\
  theories/Rational.v\
  theories/ModelsRingExt.v\
  theories/LLazy.v\
  theories/Literal.v\
  theories/Lexico.v\
  theories/Index.v\
  theories/FoldProps.v\
  theories/Ergo.v\
  theories/Env.v\
  theories/EnvLazy.v\
  theories/Dpll.v\
  theories/DoubleNegUtils.v\
  theories/DistrNeg.v\
  theories/Diff.v\
  theories/DiagProd.v\
  theories/CPolynoms.v\
  theories/Cnf.v\
  theories/CNFLazy.v\
  theories/CNFLazyN.v\
  theories/CNFLazyCommon.v\
  theories/CCX.v\
  theories/AltErgo.v\
  theories/AllInstances.v\
  theories/Adequation.v

-include $(addsuffix .d,$(VFILES))
.SECONDARY: $(addsuffix .d,$(VFILES))

VO=vo
VOFILES:=$(VFILES:.v=.$(VO))
VOFILESINC=$(filter $(wildcard tests/*),$(VOFILES)) 
VOFILES4=$(patsubst theories/%,%,$(filter theories/%,$(VOFILES)))
GLOBFILES:=$(VFILES:.v=.glob)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
ML4FILES:=src/ergo.ml4

-include $(addsuffix .d,$(ML4FILES))
.SECONDARY: $(addsuffix .d,$(ML4FILES))

MLFILES:=src/ergo_plugin_mod.ml\
  src/arith.ml

-include $(addsuffix .d,$(MLFILES))
.SECONDARY: $(addsuffix .d,$(MLFILES))

MLLIBFILES:=src/ergo_plugin.mllib

-include $(addsuffix .d,$(MLLIBFILES))
.SECONDARY: $(addsuffix .d,$(MLLIBFILES))

MLIFILES:=src/ergo.mli

-include $(addsuffix .d,$(MLIFILES))
.SECONDARY: $(addsuffix .d,$(MLIFILES))

ALLCMOFILES:=$(ML4FILES:.ml4=.cmo) $(MLFILES:.ml=.cmo)
CMOFILES=$(filter-out $(addsuffix .cmo,$(foreach lib,$(MLLIBFILES:.mllib=_MLLIB_DEPENDENCIES) $(MLPACKFILES:.mlpack=_MLPACK_DEPENDENCIES),$($(lib)))),$(ALLCMOFILES))
CMOFILESINC=$(filter $(wildcard src/*),$(CMOFILES)) 
CMXFILES=$(CMOFILES:.cmo=.cmx)
OFILES=$(CMXFILES:.cmx=.o)
CMAFILES:=$(MLLIBFILES:.mllib=.cma)
CMAFILESINC=$(filter $(wildcard src/*),$(CMAFILES)) 
CMXAFILES:=$(CMAFILES:.cma=.cmxa)
CMIFILES=$(sort $(ALLCMOFILES:.cmo=.cmi) $(MLIFILES:.mli=.cmi))
CMIFILESINC=$(filter $(wildcard src/*),$(CMIFILES)) 
CMXSFILES=$(CMXFILES:.cmx=.cmxs) $(CMXAFILES:.cmxa=.cmxs)
CMXSFILESINC=$(filter $(wildcard src/*),$(CMXSFILES)) 
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) $(CMOFILES) $(CMAFILES) $(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES)) 

mlihtml: $(MLIFILES:.mli=.cmi)
	 mkdir $@ || rm -rf $@/*
	$(OCAMLDOC) -html -rectypes -d $@ -m A $(ZDEBUG) $(ZFLAGS) $(^:.cmi=.mli)

all-mli.tex: $(MLIFILES:.mli=.cmi)
	$(OCAMLDOC) -latex -rectypes -o $@ -m A $(ZDEBUG) $(ZFLAGS) $(^:.cmi=.mli)

quick:
	$(MAKE) -f $(firstword $(MAKEFILE_LIST)) all VO=vi
checkproofs:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vi-checking $(J) $(VOFILES:%.vo=%.vi)
gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all opt byte archclean clean install uninstall_me.sh uninstall userinstall depend html validate

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install-natdynlink:
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Ergo; \
	for i in $(CMXSFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Ergo/`basename $$i`; \
	done
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Containers; \
	for i in $(CMXSFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Containers/`basename $$i`; \
	done
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Nfix; \
	for i in $(CMXSFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Nfix/`basename $$i`; \
	done
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Counting; \
	for i in $(CMXSFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Counting/`basename $$i`; \
	done

install:$(if $(HASNATDYNLINK_OR_EMPTY),install-natdynlink)
	cd "theories" && for i in $(VOFILES4); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Ergo/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Ergo/$$i; \
	done
	for i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Ergo/`basename $$i`; \
	done
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Containers; \
	for i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Containers/`basename $$i`; \
	done
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Nfix; \
	for i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Nfix/`basename $$i`; \
	done
	install -d "$(DSTROOT)"$(COQLIBINSTALL)/Counting; \
	for i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Counting/`basename $$i`; \
	done

install-doc:
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/html
	for i in html/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/$$i;\
	done
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/mlihtml
	for i in mlihtml/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/$$i;\
	done

uninstall_me.sh:
	echo '#!/bin/sh' > $@ 
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Ergo && \\\nfor i in $(CMXSFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Ergo" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Containers && \\\nfor i in $(CMXSFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Containers" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Nfix && \\\nfor i in $(CMXSFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Nfix" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Counting && \\\nfor i in $(CMXSFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Counting" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Ergo && rm -f $(VOFILES4) && \\\nfor i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Ergo" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Containers && \\\nfor i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Containers" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Nfix && \\\nfor i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Nfix" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Counting && \\\nfor i in $(CMAFILESINC) $(CMIFILESINC) $(CMOFILESINC) $(VOFILESINC); do rm -f "`basename "$$i"`"; done && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Counting" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT) \\\n' >> "$@"
	printf '&& rm -f $(shell find "html" -maxdepth 1 -and -type f -print)\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL) && find $(INSTALLDEFAULTROOT)/html -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT) \\\n' >> "$@"
	printf '&& rm -f $(shell find "mlihtml" -maxdepth 1 -and -type f -print)\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL) && find $(INSTALLDEFAULTROOT)/mlihtml -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	chmod +x $@

uninstall: uninstall_me.sh
	sh $<

clean:
	rm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)
	rm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)
	rm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))
	rm -f $(VOFILES) $(VOFILES:.vo=.vi) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml uninstall_me.sh

archclean:
	rm -f *.cmx *.o

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

Makefile: Make
	mv -f $@ $@.bak
	"$(COQBIN)coq_makefile" -f $< -o $@


###################
#                 #
# Implicit rules. #
#                 #
###################

%.cmi: %.mli
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<

%.mli.d: %.mli
	$(OCAMLDEP) -slash $(OCAMLLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.cmo: %.ml4
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<

%.cmx: %.ml4
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<

%.ml4.d: %.ml4
	$(COQDEP) $(OCAMLLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.cmo: %.ml
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<

%.cmx: %.ml
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $<

%.ml.d: %.ml
	$(OCAMLDEP) -slash $(OCAMLLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.cmxs: %.cmxa
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -linkall -shared -o $@ $<

%.cmxs: %.cmx
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $<

%.cma: | %.mllib
	$(CAMLLINK) $(ZDEBUG) $(ZFLAGS) -a -o $@ $^

%.cmxa: | %.mllib
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -a -o $@ $^

%.mllib.d: %.mllib
	$(COQDEP) $(COQLIBS) -c "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -quick $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING


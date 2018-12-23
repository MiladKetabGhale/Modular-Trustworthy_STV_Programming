%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

move: 
	mv Anu.hs ANUnion/Lib.hs; mv Vic.hs VictoriaSTV/Lib.hs; mv Act.hs ActSTV/Lib.hs

clear:
	-rm ANUnion/*.hs VictoriaSTV/*.hs ActSTV/*.hs

phony: ;

.PHONY: all clean phony

CMO=lexer.cmo parser.cmo checker.cmo main.cmo 
GENERATED=lexer.ml parser.ml parser.mli 
BIN=msmts
FLAGS=-annot -g

all: $(BIN)
	./$(BIN) test.cnfuf

$(BIN): $(CMO)
	ocamlc $(FLAGS) -o $(BIN) $(CMO)

.SUFFIXES: .mli .ml .cmi .cmo .mll .mly

.mli.cmi:
	ocamlc $(FLAGS) -c  $<

.ml.cmo:
	ocamlc $(FLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	menhir -v $<

.mly.mli:
	menhir -v $<

clean:
	rm -f *.cm[io] *.o *.annot *~ $(BIN) $(GENERATED)
	rm -f parser.output parser.automaton parser.conflicts

.depend depend:$(GENERATED)
	rm -f .depend
	ocamldep *.ml *.mli > .depend

include .depend

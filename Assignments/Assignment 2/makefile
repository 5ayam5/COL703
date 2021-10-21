tableau: lexer.lex.sml parser.yacc.* AST.sml binder.sml proptableau.sml tableau.mlb
	mlton tableau.mlb

run_tableau: tableau
	./tableau

load: lexer.lex.sml parser.yacc.*
	rlwrap sml loader.sml

lexer.lex.sml: lexer.lex
	mllex lexer.lex

parser.yacc.*: parser.yacc
	mlyacc parser.yacc

clean:
	rm -f lexer.lex.* parser.yacc.* tableau
	find . -name '*.out' -delete

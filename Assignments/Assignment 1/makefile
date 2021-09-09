flasl2ast: lexer.lex.sml parser.yacc.* AST.sml binder.sml flasl2ast.sml flasl2ast.mlb
	mlton flasl2ast.mlb

load: lexer.lex.sml parser.yacc.*
	rlwrap sml loader.sml

lexer.lex.sml: lexer.lex
	mllex lexer.lex

parser.yacc.*: parser.yacc
	mlyacc parser.yacc

clean:
	rm -f lexer.lex.* parser.yacc.* flasl2ast ast2flasl

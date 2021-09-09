structure Tokens = Tokens
    exception ScanError
    type pos = int
    (* Position in file *)
    type svalue = Tokens.svalue
    type ('a,'b) token = ('a,'b) Tokens.token
    type lexresult = (svalue,pos) token
    type lexarg = string
    type arg = lexarg

    val line = ref 1;
    val col = ref 0;
    val eolpos = ref 0;
    val eof = fn _ => Tokens.EOF(!line, !col);
    fun error (e, line, col) = TextIO.output(TextIO.stdErr, "Unknown token:" ^ (Int.toString line) ^ ":" ^ (Int.toString col) ^ ":" ^ e ^ "\n");
    fun updateLine (text, pos) = if String.sub (text, size text - 1) = #"\n" then (line := (!line) + 1; eolpos := pos + size text) else ();

%%
%header (functor FLASLLexFun(structure Tokens:FLASL_TOKENS));
alpha = [-!#-'*-,/-~];
ws = [\ \t];
%%
(\r\n)|\n   => (line := (!line) + 1; eolpos := yypos + size yytext; lex());
{ws}+       => (lex());
"."         => (col := yypos - (!eolpos); Tokens.TERM(!line, !col));
"IF"        => (col := yypos - (!eolpos); Tokens.IF(!line, !col));
"THEN"      => (col := yypos - (!eolpos); Tokens.THEN(!line, !col));
"ELSE"      => (col := yypos - (!eolpos); Tokens.ELSE(!line, !col));
"NOT"       => (col := yypos - (!eolpos); Tokens.NOT(!line, !col));
"("         => (col := yypos - (!eolpos); Tokens.LPAREN(!line, !col));
")"         => (col := yypos - (!eolpos); Tokens.RPAREN(!line, !col));
"AND"       => (col := yypos - (!eolpos); Tokens.AND(!line, !col));
"OR"        => (col := yypos - (!eolpos); Tokens.OR(!line, !col));
"IFF"       => (col := yypos - (!eolpos); Tokens.IFF(!line, !col));
"THEREFORE" => (col := yypos - (!eolpos); Tokens.THEREFORE(!line, !col));
"\""        => (col := yypos - (!eolpos); Tokens.QUOTE(!line, !col));
{alpha}+    => (col := yypos - (!eolpos); Tokens.WORD(yytext, !line, !col));
.           => (col := yypos - (!eolpos); error(yytext, !line, !col); raise LexError);

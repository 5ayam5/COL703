%%
%name FLASL
%term
    EOF | TERM | NOT | AND | OR | IF | THEN | IFF | ELSE | THEREFORE | QUOTE | WORD of string | LPAREN | RPAREN
%nonterm
    words of string | atom of string | InputFile of AST.Argument | program of AST.Argument | proplist of AST.Prop list | prop of AST.Prop | propt of AST.Prop
%pos int

%start InputFile

%eop EOF
%noshift EOF

%right IFF
%right THEN ELSE
%left IF
%left OR
%left AND
%right NOT

%verbose

%%
    InputFile:  program (program)

    program:    proplist THEREFORE propt (AST.HENCE (proplist, propt))

    proplist:   proplist propt (proplist@[propt])
    |           ([])

    propt:      prop TERM (prop)

    prop:       LPAREN prop RPAREN (prop)
    |           atom (AST.ATOM atom)
    |           NOT prop (AST.NOT prop)
    |           prop AND prop (AST.AND (prop1, prop2))
    |           prop OR prop (AST.OR (prop1, prop2))
    |           IF prop THEN prop (AST.COND (prop1, prop2))
    |           prop IF prop (AST.COND (prop2, prop1))
    |           prop IFF prop (AST.BIC (prop1, prop2))
    |           IF prop THEN prop ELSE prop (AST.ITE (prop1, prop2, prop3))

    atom:       QUOTE words QUOTE (words)
    |           QUOTE QUOTE ("")

    words:      words WORD (words ^ " " ^ WORD)
    |           WORD (WORD)

structure FLASLLrVals = FLASLLrValsFun(structure Token = LrParser.Token);
structure FLASLLex = FLASLLexFun(structure Tokens = FLASLLrVals.Tokens);
structure FLASLParser =
    Join(structure LrParser = LrParser
        structure ParserData = FLASLLrVals.ParserData
        structure Lex = FLASLLex);

fun parseAndLex (inp: string) =
        let
            fun invoke lexstream =
                    let
                        fun print_error (s, line, col) =
                                TextIO.output(TextIO.stdErr, "Syntax Error:" ^ (Int.toString line) ^ ":" ^ (Int.toString col) ^ ":" ^ s ^ "\n");
                    in
                        FLASLParser.parse(0,lexstream,print_error,())
                    end

            fun stringToLexer str =
                    let
                        val done = ref false
                        val lexer =  FLASLParser.makeLexer (fn _ => if (!done) then "" else (done := true; str))
                    in
                        lexer
                    end 
        
            fun parse lexer =
                    let
                        val dummyEOF = FLASLLrVals.Tokens.EOF(0,0)
                        val (result, lexer) = invoke lexer
                        val (nextToken, lexer) = FLASLParser.Stream.get lexer
                    in
                        if FLASLParser.sameToken(nextToken, dummyEOF) then result
                        else (print("Warning: Unconsumed input \n"); result)
                    end

        in
            (parse o stringToLexer) inp
        end

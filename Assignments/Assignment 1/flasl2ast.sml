fun flasl2ast () =
let
  fun writeProp (prop, write) =
    case prop of
         AST.ATOM s             => write ("\\\"" ^ s ^ "\\\"")
       | AST.NOT p              => (write "("; write("NOT "); writeProp (p, write);
                                    write ")")
       | AST.AND (p1, p2)       => (write "("; writeProp (p1, write); write (" AND ");
                                    writeProp (p2, write); write ")")
       | AST.OR (p1, p2)        => (write "("; writeProp (p1, write); write (" OR ");
                                    writeProp (p2, write); write ")")
       | AST.COND (p1, p2)      => (write "("; writeProp (p2, write); write (" IF ");
                                    writeProp (p1, write); write ")")
       | AST.BIC (p1, p2)       => (write "("; writeProp (p1, write); write (" IFF ");
                                    writeProp (p2, write); write ")")
       | AST.ITE (p1, p2, p3)   => (write "(IF "; writeProp (p1, write); write
                                    " THEN "; writeProp (p2, write); write " ELSE ";
                                    writeProp (p3, write); write ")")
  
  fun writeList (nil, write)    = ()
  |   writeList (h::t, write) = (writeProp (h, write); write ". "; writeList (t, write))


  val fileName = case CommandLine.arguments() of h::t => h | nil => "arg-inp.flasl"
  val inputStream = TextIO.openIn fileName
  val str = TextIO.input inputStream
  val _ = TextIO.closeIn inputStream

  val ast = parseAndLex str
  val file = TextIO.openOut "arg.sml"
  val write = fn s => TextIO.output (file, s)
  val _ =
    case ast of
         AST.HENCE (argList, res) => (write ("val arg = \"");
                                      writeList (argList, write);
                                      write "THEREFORE "; writeProp (res, write);
                                      write ".\";")
  val _ = TextIO.closeOut file
in
  ()
end
handle ParseError => raise AST.Atom_exception

val _ = flasl2ast ();

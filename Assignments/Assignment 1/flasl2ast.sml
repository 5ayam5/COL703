fun flasl2ast () =
let
  fun writeProp (prop, write) =
    case prop of
         AST.ATOM s             => write ("AST.ATOM \"" ^ s ^ "\"")
       | AST.NOT p              => (write "AST.NOT (";
                                    writeProp (p, write);
                                    write ")")

       | AST.AND (p1, p2)       => (write "AST.AND (";
                                    writeProp (p1, write);
                                    write ", ";
                                    writeProp (p2, write);
                                    write ")")

       | AST.OR (p1, p2)        => (write "AST.OR (";
                                    writeProp (p1, write);
                                    write ", ";
                                    writeProp (p2, write);
                                    write ")")

       | AST.COND (p1, p2)      => (write "AST.COND (";
                                    writeProp (p1, write);
                                    write ", ";
                                    writeProp (p2, write);
                                    write ")")

       | AST.BIC (p1, p2)       => (write "AST.BIC (";
                                    writeProp (p1, write);
                                    write ", ";
                                    writeProp (p2, write);
                                    write ")")

       | AST.ITE (p1, p2, p3)   => (write "AST.ITE (";
                                    writeProp (p1, write);
                                    write ", ";
                                    writeProp (p2, write);
                                    write ", ";
                                    writeProp (p3, write);
                                    write ")")
  
  fun writeList (nil, write)    = ()
    | writeList (h::nil, write) = writeProp (h, write)
    | writeList (h::t, write) = (writeProp (h, write); write ", "; writeList (t, write))


  val fileName = case CommandLine.arguments() of h::t => h | nil => "arg-inp.flasl"
  val inputStream = TextIO.openIn fileName
  val str = TextIO.input inputStream
  val _ = TextIO.closeIn inputStream

  val ast = parseAndLex str
  val file = TextIO.openOut "arg.sml"
  val write = fn s => TextIO.output (file, s)
  val _ =
    case ast of
         AST.HENCE (argList, res) => (write "val arg = AST.HENCE ([";
                                      writeList (argList, write);
                                      write "], ";
                                      writeProp (res, write);
                                      write ");")
  val _ = TextIO.closeOut file
in
  ()
end
handle ParseError => raise AST.Atom_exception

val _ = flasl2ast ();

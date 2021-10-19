fun updateAtomAndValidate (propList, atomList, prop) =
let
  val negProp = case prop of
                       AST.ATOM s => AST.NOT prop
                     | AST.NOT np => np
  val neg = List.exists (fn x => x = negProp) atomList
  val pos = List.exists (fn x => x = prop) atomList
in
  if neg then []
  else validate (propList, if pos then atomList else prop::atomList)
end

and branch (propList, p1, p2, atomList) =
let
  val ret1 = validate (p1::propList, atomList)
  val ret2 = validate (p2::propList, atomList)
in
  if ret1 = [] then ret2 else ret1
end

and validate ([], atomList) = atomList
  | validate (prop::propList, atomList) =
  case prop of
       AST.ATOM s   => updateAtomAndValidate (propList, atomList, prop)
     | AST.NOT np   => (case np of
                           AST.ATOM s           => updateAtomAndValidate
                                                   (propList, atomList, prop)
                         | AST.NOT p            => validate (p::propList,
                                                   atomList)
                         | AST.AND (p1, p2)     => branch (propList, AST.NOT p1,
                                                   AST.NOT p2, atomList)
                         | AST.OR (p1, p2)      => validate (AST.NOT p1::AST.NOT
                                                   p2::propList, atomList)
                         | AST.COND (p1, p2)    => validate (p1::AST.NOT
                                                   p2::propList, atomList)
                         | AST.BIC (p1, p2)     => branch (propList,
                                                   AST.AND (p1, AST.NOT p2),
                                                   AST.AND (AST.NOT p1, p2),
                                                   atomList)
                         | AST.ITE (p1, p2, p3) => validate (
                                                   AST.NOT (AST.AND (p1, p2))::
                                                   AST.NOT (AST.AND
                                                            (AST.NOT p1, p3))
                                                   ::propList, atomList))
     | AST.AND (p1, p2)     => validate (p1::p2::propList, atomList)
     | AST.OR (p1, p2)      => branch (propList, p1, p2, atomList)
     | AST.COND (p1, p2)    => branch (propList, AST.NOT p1, p2, atomList)
     | AST.BIC (p1, p2)     => branch (propList, AST.AND (p1, p2), AST.AND
                               (AST.NOT p1, AST.NOT p2), atomList)
     | AST.ITE (p1, p2, p3) => branch (propList, AST.AND (p1, p2), AST.AND
                               (AST.NOT p1, p3), atomList)

fun getPropList () =
let
  val fileName = case CommandLine.arguments() of h::t => h | [] =>
                 "arg-inp.flasl"
  val _ = if String.extract (fileName, size fileName - 6, NONE) <> ".flasl"
          then raise AST.Atom_exception else ()
  val inputStream = TextIO.openIn fileName
  val str = TextIO.input inputStream
  val _ = TextIO.closeIn inputStream
in
    (String.substring (fileName, 0, size fileName - 6) ^ ".out",
    case parseAndLex str of AST.HENCE (propList, conc) => AST.NOT
                                                          conc::propList)
end

fun outputFalsifying (outStream, [])    = ()
  | outputFalsifying (outStream, h::t)  =
  (case h of
       AST.ATOM s => TextIO.output (outStream, s ^ ": true\n")
     | AST.NOT p  => case p of AST.ATOM s => TextIO.output (outStream,
                                                            s ^ ": false\n");
  outputFalsifying (outStream, t))

fun tableau () =
let
  val (fileName, propList) = getPropList ()
  val valid = validate (propList, [])
  val outStream = TextIO.openOut fileName
in
  (case valid of
       []   => TextIO.output (outStream,
                              "The given argument is logically valid!\n")
     | h::t => (TextIO.output (outStream,
                               "The given argument is logically invalid!\n");
                outputFalsifying (outStream, valid));
  TextIO.closeOut outStream)
end

val _ = tableau ();

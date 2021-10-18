fun updateAtomList (atomList, prop) =
let
  val checkProp = case prop of
                       AST.ATOM s => AST.NOT prop
                     | AST.NOT np => np
  val newAtomList = List.filter (fn x => x <> checkProp) atomList
in
  if length atomList = length newAtomList then prop::atomList else newAtomList
end

fun branch (propList, p1, p2, atomList) =
let
  val ret1 = validate (p1::propList, atomList)
  val ret2 = validate (p2::propList, atomList)
in
  if ret1 = [] then ret2 else ret1
end

and validate ([], atomList) = atomList
  | validate (prop::propList, atomList) =
  case prop of
       AST.ATOM s   => validate (propList, updateAtomList (atomList, prop))
     | AST.NOT np   => (case np of
                           AST.ATOM s           => validate (propList,
                                                   updateAtomList (atomList,
                                                   prop))
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

fun tableau () =
let
  val fileName = case CommandLine.arguments() of h::t => h | nil => "arg-inp.flasl"
  val inputStream = TextIO.openIn fileName
  val str = TextIO.input inputStream
  val _ = TextIO.closeIn inputStream
  val propList = case parseAndLex str of
                 AST.HENCE (propList, conc) => AST.NOT conc::propList
  val valid = validate (propList, [])
in
  valid
end

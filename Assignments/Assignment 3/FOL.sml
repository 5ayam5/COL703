Control.Print.printLength := 1000; (* set printing parameters so that *)
Control.Print.printDepth := 1000; (* we’ll see all details *)
Control.Print.stringDepth := 1000; (* and strings *)

structure FOL =
struct
  datatype term = VAR of string
                | FUN of string * term list
                | CONST of string (* for generated constants only *)
  datatype Pred = FF (* special constant for closing a tableau path *)
                | ATOM of string * term list
                | NOT of Pred
                | AND of Pred * Pred
                | OR of Pred * Pred
                | COND of Pred * Pred
                | BIC of Pred * Pred
                | ITE of Pred * Pred * Pred
                | ALL of term * Pred
                | EX of term * Pred
  datatype Argument = HENCE of Pred list * Pred
  datatype Tableau = Null | Node of Pred * Tableau * Tableau

  exception NotVAR (* Binding term in a quantified formula is not a variable *)
  exception NotWFT (* term is not well-formed *)
  exception NotWFP (* predicate is not well-formed *)
  exception NotWFA (* argument is not well-formed *)
  exception NotClosed (* a formula is not closed *)

  val newSymbol = ref 0
  val vertices = ref []: (int * Pred) list ref
  val edges = ref []: (int * int) list ref

  fun termToString (VAR s) = s
    | termToString (FUN (s, t)) = s ^ "(" ^ (String.concatWith "," (List.map termToString t)) ^ ")"
    | termToString (CONST s) = s

  fun predToString p =
    case p of
      FF => "\\bot "
    | ATOM (s, l) => s ^ "(" ^ (String.concatWith "," (List.map termToString l)) ^ ")"
    | NOT p => "\\neg " ^ predToString p
    | AND (p, q) => "(" ^ predToString p ^ "\\wedge " ^ predToString q ^ ")"
    | OR (p, q) => "(" ^ predToString p ^ "\\vee " ^ predToString q ^ ")"
    | COND (p, q) => "(" ^ predToString p ^ "\\to " ^ predToString q ^ ")"
    | BIC (p, q) => "(" ^ predToString p ^ "\\leftrightarrow " ^ predToString q ^ ")"
    | ITE (p, q, r) => "ITE(" ^ predToString p ^ "," ^ predToString q ^ "," ^ predToString r ^ ")"
    | ALL (VAR x, p) => "\\forall " ^ x ^ "\\left[" ^ predToString p ^ "\\right]"
    | EX (VAR x, p) => "\\exists " ^ x ^ "\\left[" ^ predToString p ^ "\\right]"
    | _ => raise NotVAR

  fun isolate [] = []
    | isolate (x::xs) = x::isolate(List.filter (fn y => y <> x) xs)

  fun getNewSymbol () =
    let
      val symbol = Int.toString (!newSymbol)
    in
      (newSymbol := !newSymbol + 1; symbol)
    end

  fun substituteTermInTerm (x, t, tNew) =
    case x of
      VAR s => if x = t then tNew else x
    | FUN (s, l) => FUN (s, List.map (fn y => substituteTermInTerm (y, t, tNew)) l)
    | CONST s => x
  
  fun substituteTerm (p, t, tNew) =
    case p of
      FF => p
    | ATOM (s, l) => ATOM (s, List.map (fn x => substituteTermInTerm (x, t, tNew)) l)
    | NOT p1 => NOT (substituteTerm (p1, t, tNew))
    | AND (p1, p2) => AND (substituteTerm (p1, t, tNew), substituteTerm (p2, t, tNew))
    | OR (p1, p2) => OR (substituteTerm (p1, t, tNew), substituteTerm (p2, t, tNew))
    | COND (p1, p2) => COND (substituteTerm (p1, t, tNew), substituteTerm (p2, t, tNew))
    | BIC (p1, p2) => BIC (substituteTerm (p1, t, tNew), substituteTerm (p2, t, tNew))
    | ITE (p1, p2, p3) => ITE (substituteTerm (p1, t, tNew), substituteTerm (p2, t, tNew), substituteTerm (p3, t, tNew))
    | ALL (t1, p1) => if t1 <> t then ALL (t1, substituteTerm (p1, t, tNew)) else p
    | EX (t1, p1) => if t1 <> t then EX (t1, substituteTerm (p1, t, tNew)) else p

  fun appendNode (Node (p, Null, Null), (t1, t2)) = Node (p, t1, t2)
    | appendNode (Node (p, left, right), expanded) = Node (p, appendNode (left, expanded), appendNode (right, expanded))
    | appendNode (Null, _) = Null

  fun extractTerms (h::t) =
      (case h of
        FUN (s, l) => h::(extractTerms (l)@extractTerms (t))
      | CONST s => h::extractTerms (t)
      | VAR x => raise NotClosed)
    | extractTerms [] = []

  fun expandNegPred p =
    case p of
      FF => raise NotWFP
    | ATOM (s, l) => (Node (NOT p, Null, Null), Null)
    | NOT p1 => expandPred p1
    | AND (p1, p2) => expandPred (OR (NOT p1, NOT p2))
    | OR (p1, p2) => expandPred (AND (NOT p1, NOT p2))
    | COND (p1, p2) => expandPred (AND (p1, NOT p2))
    | BIC (p1, p2) => expandPred (OR (AND (p1, NOT p2), AND (NOT p1, p2)))
    | ITE (p1, p2, p3) => expandPred (AND (OR (NOT p1, NOT p2), OR (p1, NOT p3)))
    | ALL (t, p) => expandPred (EX (t, NOT p))
    | EX (t, p) => expandPred (ALL (t, NOT p))

  and expandPred p =
    case p of
      FF => (Node (p, Null, Null), Null)
    | ATOM (s, l) => (Node (p, Null, Null), Null)
    | NOT p1 => expandNegPred p1
    | AND (p1, p2) => (Node (p1, Node (p2, Null, Null), Null), Null)
    | OR (p1, p2) => (Node (p1, Null, Null), Node (p2, Null, Null))
    | COND (p1, p2) => (Node (NOT p1, Null, Null), Node (p2, Null, Null))
    | BIC (p1, p2) => (Node (AND (p1, p2), Null, Null), Node (AND (NOT p1, NOT p2), Null, Null))
    | ITE (p1, p2, p3) => (Node (AND (p1, p2), Null, Null), Node (AND (NOT p1, p3), Null, Null))
    | ALL (t, p1) => (Node (p, Null, Null), Null)
    | EX (t, p1) => (Node (substituteTerm (p1, t, CONST (getNewSymbol ())), Null, Null), Null)
  
  and expandTableau (Node (p, left, right)) =
    let
      val expanded_p = expandPred p
    in
      case expanded_p of
        (Node (p1, left1, right1), Null) => (if p1 = p then Node (p, expandTableau left, expandTableau right)
                                          else case appendNode (Node (p, left, right), expanded_p) of
                                                  Node (p1, left1, right1) => Node (p1, expandTableau left1, expandTableau right1))
      | (t1, t2) => case appendNode (Node (p, left, right), expanded_p) of
                      Node (p1, left1, right1) => Node (p1, expandTableau left1, expandTableau right1)
    end
    | expandTableau Null = Null

  and solveTableau (Node (p, left, right), foralls, atoms, terms, _) =
      (case p of
        FF => Node (p, left, right)
      | ATOM (s, l) => if List.exists (fn x => x = NOT p) atoms then appendNode (Node (p, left, right), (Node (FF, Null, Null), Null))
                      else if List.exists (fn x => x = p) atoms then Node (p, solveTableau (left, foralls, atoms, terms, left = Null), solveTableau (right, foralls, atoms, terms, false))
                      else
                        let
                          val newTerms = isolate (extractTerms(l)@terms)
                        in
                          Node (p, solveTableau (left, foralls, p::atoms, newTerms, left = Null), solveTableau (right, foralls, p::atoms, newTerms, false))
                        end
      | NOT (ATOM (s, l)) => if List.exists (fn x => x = ATOM (s, l)) atoms then appendNode (Node (p, left, right), (Node (FF, Null, Null), Null))
                          else if List.exists (fn x => x = p) atoms then Node (p, solveTableau (left, foralls, atoms, terms, left = Null), solveTableau (right, foralls, atoms, terms, false))
                          else
                            let
                              val newTerms = isolate (extractTerms(l)@terms)
                            in
                              Node (p, solveTableau (left, foralls, p::atoms, newTerms, left = Null), solveTableau (right, foralls, p::atoms, newTerms, false))
                            end
      | ALL (t, p1) => Node (p, solveTableau (left, (p1, t, [])::foralls, atoms, terms, left = Null), solveTableau (right, (p1, t, [])::foralls, atoms, terms, false))
      | _ => Node (p, solveTableau (left, foralls, atoms, terms, left = Null), solveTableau (right, foralls, atoms, terms, false)))
    | solveTableau (Null, (p, z, l)::t, atoms, terms, true) =
      let
        val pendingTerms = List.filter (fn x => not (List.exists (fn y => y = x) l)) terms
      in
        case pendingTerms of
          [] => solveTableau (Null, t@[(p, z, l)], atoms, terms, true)
        | t1::ts => solveTableau (expandTableau (Node (substituteTerm (p, z, t1), Null, Null)), (p, z, t1::l)::t, atoms, terms, false)
      end
    | solveTableau (Null, _, atoms, terms, _) = Null

  fun constructTableau (h::t, Node (p, Null, Null)) =
    Node (p, constructTableau (t, Node (h, Null, Null)), Null)
    | constructTableau (nil, Node (p, Null, Null)) = Node (p, Null, Null)

  fun isClosed (Node (p, left, right)) =
      (case p of
        FF => true
      | _ => isClosed left andalso (right = Null orelse isClosed right))
    | isClosed Null = false

  fun infiniteLoop () = infiniteLoop ()

  fun addVerticesAndEdges (Node (p, left, right), pid, id) =
    let
      val _ = vertices := (!vertices)@[(id, p)]
      val _ = edges := (!edges)@[(pid, id)]
      val lid = addVerticesAndEdges (left, id, id + 1)
      val rid = addVerticesAndEdges (right, id, lid)
    in
      rid
    end
    | addVerticesAndEdges (Null, _, id) = id

  fun writeToDot () =
    let
      val outStream = TextIO.openOut "tableau.dot"
      val write = fn s => TextIO.output (outStream, s)
      val _ = write "digraph G {\n"
      val _ = write "nodesep = 0.5;\n"
      val _ = write "ranksep = 0.5;\n"
      val _ = write "node [shape = plaintext];\n"
      val _ = List.map (fn (id, p) => write ("  " ^ Int.toString id ^ " [texlbl=\"\\underline{" ^ Int.toString id ^ ". $" ^ predToString p ^ "$}\"];\n")) (!vertices)
      val _ = write "subgraph dir {\n"
      val _ = List.map (fn (pid, id) => if pid <> 0 then write ("  " ^ Int.toString pid ^ " -> " ^ Int.toString id ^ ";\n") else ()) (!edges)
      val _ = write "}}\n"
      val _ = TextIO.closeOut outStream
    in
      ()
    end

  fun mktableau (HENCE(l, p)) = (* outputs file "tableau.dot" in dot format *)
  let
    val tableau = constructTableau (l, Node (NOT p, Null, Null))
    val expandedTableau = expandTableau tableau
    val solvedTableau = solveTableau (expandedTableau, [], [], [], false)
    val _ = addVerticesAndEdges (solvedTableau, 0, 1)
  in
    if isClosed solvedTableau then writeToDot () else infiniteLoop ()
  end
end

open FOL;

val a = mktableau (HENCE ([ATOM ("p", [FUN ("c", [])]), ATOM ("q", [FUN ("d", [])]), BIC (ATOM ("a", []), ATOM ("r", [FUN ("y", [])]))], ATOM ("p", [FUN ("c", [])])))
(* val b = mktableau (HENCE ([ATOM ("p", [FUN ("c", [])])], ATOM ("p", [FUN ("c", [])]))) *)
(* val c = mktableau (HENCE ([AND (ATOM ("a", []), ATOM ("r", [FUN ("y", [])]))], ATOM ("p", [FUN ("c", [])]))) *)
(* val d = mktableau (HENCE ([ALL (VAR "x", AND (ATOM ("p", [VAR "x"]), NOT (ATOM ("p", [FUN ("b", [])]))))], ATOM ("p", [FUN ("c", [])]))) *)
(* val e = mktableau (HENCE ([ALL (VAR "x", AND (ATOM ("p", [VAR "x"]), NOT (ATOM ("p", [FUN ("b", [])]))))], ATOM ("q", [FUN ("c", [])]))) *)
(* val f = mktableau (HENCE ([EX (VAR "x", NOT (ATOM ("p", [FUN ("f", [FUN ("g", [VAR "x"])])])))], NOT (ALL (VAR "y", ATOM("p", [VAR "y"]))))) *)

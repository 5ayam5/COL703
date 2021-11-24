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
  datatype Tableau = Null | Node of int * Tableau * Tableau
  datatype PredTableau = PNull | PNode of Pred * PredTableau * PredTableau * int

  exception NotVAR (* Binding term in a quantified formula is not a variable *)
  exception NotWFT (* term is not well-formed *)
  exception NotWFP (* predicate is not well-formed *)
  exception NotWFA (* argument is not well-formed *)
  exception NotClosed (* a formula is not closed *)

  val newSymbol = ref ~1
  val formulaNumber = ref 0
  val vertices = ref []: (int * Pred) list ref
  val treeEdges = ref []: (int * int) list ref
  val backEdges = ref []: (int * int) list ref
  val redEdges = ref []: (int * int) list ref

  fun init () =
    let
      val _ = newSymbol := ~1
      val _ = formulaNumber := 0
      val _ = vertices := []
      val _ = treeEdges := []
      val _ = backEdges := []
      val _ = redEdges := []
    in ()
    end

  fun getPredicate id =
    case List.find (fn (i, _) => i = id) (!vertices) of
      SOME (_, p) => p

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
      val _ = newSymbol := !newSymbol + 1
    in
      Int.toString (!newSymbol)
    end

  fun getNewFormula () = 
    let
      val _ = formulaNumber := !formulaNumber + 1
    in
      !formulaNumber
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

  fun predTableauToIntTableau (PNode (p, left, right, pid)) =
    let
      val id = getNewFormula ()
      val _ = vertices := (id, p)::(!vertices)
      val _ = if pid <> ~1 then backEdges := (id, pid)::(!backEdges) else ()
    in
      Node (id, predTableauToIntTableau left, predTableauToIntTableau right)
    end
    | predTableauToIntTableau PNull = Null

  fun appendNode (Node (p, Null, Null), (t1, t2)) = Node (p, predTableauToIntTableau t1, predTableauToIntTableau t2)
    | appendNode (Node (p, left, right), expanded) = Node (p, appendNode (left, expanded), appendNode (right, expanded))
    | appendNode (Null, _) = Null

  fun extractTerms (h::t, p) =
      (case h of
        FUN (s, l) => (h, p)::(extractTerms (l, p)@extractTerms (t, p))
      | CONST s => (h, p)::extractTerms (t, p)
      | VAR x => raise NotClosed)
    | extractTerms ([], p) = []

  fun makeBranchingNode (p1, p2, par) = (PNode (p1, PNull, PNull, par), PNode (p2, PNull, PNull, par))

  fun makeSingleNode (p1, par) = (PNode (p1, PNull, PNull, par), PNull)

  fun makeElongationNode (p1, p2, par) = (PNode (p1, PNode (p2, PNull, PNull, par), PNull, par), PNull)

  fun expandNegPred (p, par) =
    case p of
      FF => raise NotWFP
    | ATOM (s, l) => (PNode (NOT p, PNull, PNull, par), PNull)
    | NOT p1 => makeSingleNode (p1, par)
    | AND (p1, p2) => makeBranchingNode (NOT p1, NOT p2, par)
    | OR (p1, p2) => makeElongationNode (NOT p1, NOT p2, par)
    | COND (p1, p2) => makeElongationNode (p1, NOT p2, par)
    | BIC (p1, p2) => makeBranchingNode (AND (p1, NOT p2), AND (NOT p1, p2), par)
    | ITE (p1, p2, p3) => makeElongationNode (OR (NOT p1, NOT p2), OR (p1, NOT p3), par)
    | ALL (t, p) => makeSingleNode (EX (t, NOT p), par)
    | EX (t, p) => makeSingleNode (ALL (t, NOT p), par)

  and expandPred p =
    case getPredicate p of
      FF => (PNode (FF, PNull, PNull, ~1), PNull)
    | ATOM (s, l) => (PNode (ATOM (s, l), PNull, PNull, ~1), PNull)
    | NOT p1 => expandNegPred (p1, p)
    | AND (p1, p2) => makeElongationNode (p1, p2, p)
    | OR (p1, p2) => makeBranchingNode (p1, p2, p)
    | COND (p1, p2) => makeBranchingNode (NOT p1, p2, p)
    | BIC (p1, p2) => makeBranchingNode (AND (p1, p2), AND (NOT p1, NOT p2), p)
    | ITE (p1, p2, p3) => makeBranchingNode (AND (p1, p2), AND (NOT p1, p3), p)
    | ALL (t, p1) => (PNode (ALL (t, p1), PNull, PNull, ~1), PNull)
    | EX (t, p1) => makeSingleNode (substituteTerm (p1, t, CONST ("c" ^ getNewSymbol ())), p)
  
  and expandTableau (Node (p, left, right)) =
    let
      val expanded_p = expandPred p
    in
      case expanded_p of
        (PNode (p1, left1, right1, par), PNull) => (if p1 = getPredicate p then Node (p, expandTableau left, expandTableau right)
                                          else case appendNode (Node (p, left, right), expanded_p) of
                                                  Node (p1, left1, right1) => Node (p1, expandTableau left1, expandTableau right1))
      | _ => case appendNode (Node (p, left, right), expanded_p) of
              Node (p1, left1, right1) => Node (p1, expandTableau left1, expandTableau right1)
    end
    | expandTableau Null = Null

  and solveTableau (Node (p, left, right), foralls, atoms, terms, _) =
      (case getPredicate p of
        FF => Node (p, left, right)
      | ATOM (s, l) => if List.exists (fn x => getPredicate x = NOT (ATOM (s, l))) atoms then
                        let
                          val SOME par = List.find (fn x => getPredicate x = NOT (ATOM (s, l))) atoms
                          val _ = redEdges := (p, par)::(!redEdges)
                        in
                          appendNode (Node (p, left, right), (PNode (FF, PNull, PNull, ~1), PNull))
                        end
                      else if List.exists (fn x => getPredicate x = ATOM (s, l)) atoms then Node (p, solveTableau (left, foralls, atoms, terms, left = Null), solveTableau (right, foralls, atoms, terms, false))
                      else
                        let
                          val newTerms = isolate (extractTerms(l, p)@terms)
                        in
                          Node (p, solveTableau (left, foralls, p::atoms, newTerms, left = Null), solveTableau (right, foralls, p::atoms, newTerms, false))
                        end
      | NOT (ATOM (s, l)) => if List.exists (fn x => getPredicate x = ATOM (s, l)) atoms then
                        let
                          val SOME par = List.find (fn x => getPredicate x = ATOM (s, l)) atoms
                          val _ = redEdges := (p, par)::(!redEdges)
                        in
                          appendNode (Node (p, left, right), (PNode (FF, PNull, PNull, ~1), PNull))
                        end
                          else if List.exists (fn x => getPredicate x = NOT (ATOM (s, l))) atoms then Node (p, solveTableau (left, foralls, atoms, terms, left = Null), solveTableau (right, foralls, atoms, terms, false))
                          else
                            let
                              val newTerms = isolate (extractTerms(l, p)@terms)
                            in
                              Node (p, solveTableau (left, foralls, p::atoms, newTerms, left = Null), solveTableau (right, foralls, p::atoms, newTerms, false))
                            end
      | ALL (t, p1) => Node (p, solveTableau (left, (p, p1, t, [])::foralls, atoms, terms, left = Null), solveTableau (right, (p, p1, t, [])::foralls, atoms, terms, false))
      | _ => Node (p, solveTableau (left, foralls, atoms, terms, left = Null), solveTableau (right, foralls, atoms, terms, false)))
    | solveTableau (Null, (id, p, z, l)::t, atoms, terms, true) =
      let
        val pendingTerms = List.filter (fn (x, _) => not (List.exists (fn y => y = x) l)) terms
      in
        case pendingTerms of
          [] => solveTableau (Null, t@[(id, p, z, l)], atoms, terms, true)
        | (t1, tid)::ts =>
          let
            val id1 = getNewFormula ()
            val _ = vertices := (id1, substituteTerm (p, z, t1))::(!vertices)
            val _ = backEdges := (id1, id)::(!backEdges)
          in
            solveTableau (expandTableau (Node (id1, Null, Null)), (id, p, z, t1::l)::t, atoms, terms, false)
          end
      end
    | solveTableau (Null, _, atoms, terms, _) = Null

  fun constructTableau (h::t, Node (pid, Null, Null)) =
    let
      val id = getNewFormula()
      val _ = vertices := (id, h)::(!vertices)
    in
      Node (pid, constructTableau (t, Node (id, Null, Null)), Null)
    end
    | constructTableau (nil, Node (p, Null, Null)) = Node (p, Null, Null)

  fun isClosed (Node (p, left, right)) =
      (case getPredicate p of
        FF => true
      | _ => isClosed left andalso (right = Null orelse isClosed right))
    | isClosed Null = false

  fun infiniteLoop () = infiniteLoop ()

  fun makeTreeEdges (Node (p, left, right), pid) = (treeEdges := (pid, p)::(!treeEdges); makeTreeEdges (left, p); makeTreeEdges (right, p))
    | makeTreeEdges (Null, pid) = ()

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
      val _ = List.map (fn (pid, id) => if pid <> 0 then write ("  " ^ Int.toString pid ^ " -> " ^ Int.toString id ^ ";\n") else ()) (!treeEdges)
      val _ = write "}\n"
      val _ = write "subgraph ancestor {\n"
      val _ = write "edge [color=blue, style=dashed]\n"
      val _ = List.map (fn (pid, id) => write ("  " ^ Int.toString pid ^ " -> " ^ Int.toString id ^ ";\n")) (!backEdges)
      val _ = write "}\n"
      val _ = write "subgraph undir {\n"
      val _ = write "edge [color=red, dir=none]\n"
      val _ = List.map (fn (pid, id) => write ("  " ^ Int.toString pid ^ " -> " ^ Int.toString id ^ ";\n")) (!redEdges)
      val _ = write "}\n"
      val _ = write "}\n"
      val _ = TextIO.closeOut outStream
    in
      ()
    end

  fun mktableau (HENCE(l, p)) = (* outputs file "tableau.dot" in dot format *)
  let
    val _ = init ()
    val rootid = getNewFormula()
    val _ = vertices := (rootid, NOT p)::(!vertices)
    val tableau = constructTableau (l, Node (rootid, Null, Null))
    val expandedTableau = expandTableau tableau
    val solvedTableau = solveTableau (expandedTableau, [], [], [], false)
    val _ = vertices := List.rev (!vertices)
    val _ = makeTreeEdges (solvedTableau, rootid - 1)
  in
    if isClosed solvedTableau then writeToDot () else infiniteLoop ()
  end
end

open FOL;

(* val a = mktableau (HENCE ([ATOM ("p", [FUN ("c", [])]), ATOM ("q", [FUN ("d", [])]), BIC (ATOM ("a", []), ATOM ("r", [FUN ("y", [])]))], ATOM ("p", [FUN ("c", [])]))) *)
(* val b = mktableau (HENCE ([ATOM ("p", [FUN ("c", [])])], ATOM ("p", [FUN ("c", [])]))) *)
(* val c = mktableau (HENCE ([AND (ATOM ("a", []), ATOM ("r", [FUN ("y", [])]))], ATOM ("p", [FUN ("c", [])]))) *)
(* val d = mktableau (HENCE ([ALL (VAR "x", AND (ATOM ("p", [VAR "x"]), NOT (ATOM ("p", [FUN ("b", [])]))))], ATOM ("p", [FUN ("c", [])]))) *)
(* val e = mktableau (HENCE ([ALL (VAR "x", AND (ATOM ("p", [VAR "x"]), NOT (ATOM ("p", [FUN ("b", [])]))))], ATOM ("q", [FUN ("c", [])]))) *)
(* val f = mktableau (HENCE ([EX (VAR "x", NOT (ATOM ("p", [FUN ("f", [FUN ("g", [VAR "x"])])])))], NOT (ALL (VAR "y", ATOM("p", [VAR "y"]))))) *)

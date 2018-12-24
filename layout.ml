type ident = Ident of string;;
type label = Lab of string;;

type nonce = Nonce of int;;
type bt = LRecord of (label * bt) list | LInt | LTrue | LFalse | LFun | LStar | LEmpty;;
type t =  T of bt * (bt list);;
type tau = Tau of (t * nonce) list;;

(* Use TaggedMatch, TaggedFunction instead of Match and Function in TaggedClause and tagged_expr, which is used in typechecker.  *)
type body = Int of int | True | False | Closure of body * env | Function of ident * expr | Record of (label * ident) list | Amb of body list | Empty
          | Var of ident | Appl of ident * ident | Proj of ident * label
          | Plus of ident * ident | Minus of ident * ident | LessThan of ident * ident | Equals of ident * ident
          | And of ident * ident | Or of ident * ident | Not of ident
          | Match of ident * (pattern * expr) list
          | TaggedFunction of ident * tagged_expr | TaggedMatch of ident * (pattern * tagged_expr) list
          | TaggedClosure of body * tagged_env
and env = (ident * body) list
and tagged_env = (ident * (body * nonce)) list
and clause = Clause of ident * body
and tagged_clause = TaggedClause of ident * tau * body
and expr = clause list
and tagged_expr = tagged_clause list
and pattern = PRecord of (label * pattern) list | PInt | PTrue | PFalse | PFun | PStar;;

exception BodyNotMatched;;
exception ClauseNotMatched;;
exception ForkFailed;;
exception WrongFormatOfDataFlow;;

let rec untag_program (program:tagged_expr) =
  match program with
  | TaggedClause (x, t, TaggedFunction (xx, e))::tl -> Clause (x, Function (xx, untag_program e))::(untag_program tl)
  | TaggedClause (x, t, TaggedMatch (xx, pa))::tl ->
    let rec untag_pattern pa =
      (match pa with
       | (p, e)::ttll -> (p, untag_program e)::(untag_pattern ttll)
       | _ ->[])
    in Clause (x, Match (xx, untag_pattern pa))::(untag_program tl)
  | TaggedClause (x, t, b)::tl -> Clause (x, b)::(untag_program tl)
  | _ -> [];;

let rec tag_program (program: expr) tags =
  let rec find_tau tags x =
    match tags with
    | (Ident x1, tau)::tl -> if x = x1 then Tau tau else find_tau tl x
    | _ -> Tau [(T(LStar, []), Nonce (-1))]
  in match program with
  | Clause (Ident x1, Function (x2, e))::tl -> TaggedClause (Ident x1, find_tau tags x1, TaggedFunction (x2, tag_program e tags))::(tag_program tl tags)
  | Clause (Ident x1, Match (x2, pa))::tl ->
    let rec tag_pattern pa =
      (match pa with
       | (p, e)::ttll -> (p, tag_program e tags)::(tag_pattern ttll)
       | _ -> [])
    in TaggedClause (Ident x1, find_tau tags x1, TaggedMatch (x2, tag_pattern pa))::(tag_program tl tags)
  | Clause (Ident x1, b)::tl -> TaggedClause (Ident x1, find_tau tags x1, b)::(tag_program tl tags)
  | _ -> [];;

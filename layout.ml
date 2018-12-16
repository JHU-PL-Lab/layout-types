type ident = Ident of string;;
type label = Lab of string;;

type nonce = Nonce of int;;
type bt = LRecord of (label * bt) list | LInt | LTrue | LFalse | LFun | LStar | LEmpty;;
type t =  T of bt * (bt list);;
type tau = Tau of (t * nonce) list;;

type body = Int of int | True | False | Closure of body * env | Function of ident * expr | Record of (label * ident) list | OrVal of body list | Empty
          | Var of ident | Appl of ident * ident | Proj of ident * label
          | Plus of ident * ident | Minus of ident * ident | LessThan of ident * ident | Equals of ident * ident
          | And of ident * ident | Or of ident * ident | Not of ident
          | Match of ident * (pattern * expr) list
          | TaggedFunction of ident * tagged_expr | TaggedMatch of ident * (pattern * tagged_expr) list
and env = (ident * body) list
and clause = Clause of ident * body
and tagged_clause = TaggedClause of ident * tau * body
and expr = clause list
and tagged_expr = tagged_clause list
and pattern = PRecord of (label * pattern) list | PInt | PTrue | PFalse | PFun | PStar;;

let rec untag_program (program:tagged_expr) =
  match program with
  | TaggedClause (x, t, TaggedFunction (xx, e))::tl -> Clause (x, Function (xx, untag_program e))::(untag_program tl)
  | TaggedClause (x, t, TaggedMatch (xx, pa))::tl ->
    let rec untag_pattern pa =
      (match pa with
       | (p, e)::tl -> (p, untag_program e)::(untag_pattern tl)
       | _ ->[])
    in Clause (x, Match (xx, untag_pattern pa))::(untag_program tl)
  | TaggedClause (x, t, b)::tl -> Clause (x, b)::(untag_program tl)
  | _ -> [];;

type ident = Ident of string;;
type label = Lab of string;;

type body = Int of int | True | False | Closure of body * env | Function of ident * expr | Record of (label * ident) list
          | Var of ident | Appl of ident * ident | Proj of ident * label
          | Plus of ident * ident | Minus of ident * ident | LessThan of ident * ident | Equals of ident * ident
          | And of ident * ident | Or of ident * ident | Not of ident
          | Match of ident * (pattern * expr) list
and env = (ident * body) list
and clause = Clause of ident * body
and expr = clause list
and pattern = PRecord of (label * pattern) list | PInt | PTrue | PFalse | PFun | PStar;;

exception VariableNotFound;;
exception IncorrectType of string;;
exception BodyNotMatched;;
exception ClauseNotMatched;;
exception InvalidPatternMatch;;
exception PatternNotMatched;;

let global_env = ref [];;

let rec find_var x envir =
   match envir with
    | (Ident x1, b)::tl -> if x = x1 then b else find_var x tl
    | _ -> raise VariableNotFound;;

let rec get_record_val r l =
  match r with
  | (Lab lab, Ident x)::tl -> if l =lab then x else get_record_val tl l
  | _ -> raise (IncorrectType "Record has wrong format");;

let rec pattern_match x (p:pattern) (ev:env) =
    match (find_var x ev, p) with
     | (Int n, PInt) -> true
     | (True, PTrue) -> true
     | (False, PFalse) -> true
     | (Closure(Function (x1, e1), eevv), PFun) -> true
     | (_, PStar) -> true
     | (Closure(Record r1, eevv), PRecord p1) ->
       let rec iterate_record r pp =
          (match (r,pp) with
            | ((Lab l1, Ident x1)::tl, (Lab l2, p2)) -> if l1 = l2 then (pattern_match x1 p2 eevv) else (iterate_record tl pp)
            | _ -> raise InvalidPatternMatch) in
       (let rec iterate_record_pattern r p1 =
          match p1 with
          | hd::tl -> if (iterate_record r hd) then iterate_record_pattern r tl else false
          | _ -> true
        in iterate_record_pattern r1 p1)
     |  _ -> false;;

let rec eval_body (b:body) (ev:env) (flowfrom: ident)=
    match b with
      | Int n -> Int n
      | True -> True
      | False -> False
      | Var (Ident x) -> global_env := (flowfrom, Var (Ident x))::!global_env; find_var x ev
      | Function (x1, e1) -> Closure (b, ev)
      | Record rc -> Closure (b, ev)
      | Plus (Ident x1, Ident x2) ->
        (match (find_var x1 ev, find_var x2 ev) with
         | (Int i1, Int i2) -> Int (i1+i2)
         | _ -> raise (IncorrectType "Plus operation has non-int operands"))
      | Minus (Ident x1, Ident x2) ->
        (match (find_var x1 ev, find_var x2 ev) with
         | (Int i1, Int i2) -> Int (i1-i2)
         | _ -> raise (IncorrectType "Minus operation has non-int operands"))
      | Not (Ident x1) ->
        (match find_var x1 ev with
         | True -> False
         | False -> True
         | _ -> raise (IncorrectType "Not operation has non-boolean operands"))
      | And (Ident x1, Ident x2) ->
        (match (find_var x1 ev, find_var x2 ev) with
         | (True, False) -> False
         | (True, True) -> True
         | (False, True) -> False
         | (False, False) -> False
         | _ -> raise (IncorrectType "And operation has non-boolean operands"))
      | Or (Ident x1, Ident x2) ->
        (match (find_var x1 ev, find_var x2 ev) with
         | (True, False) -> True
         | (True, True) -> True
         | (False, True) -> True
         | (False, False) -> False
         | _ -> raise (IncorrectType "Not operation has non-boolean operands"))
      | Equals (Ident x1, Ident x2) ->
        (match (find_var x1 ev, find_var x2 ev) with
         | (Int i1, Int i2) -> if i1 = i2 then True else False
         | _ -> raise (IncorrectType "Equals operation has non-int operands"))
      | Appl (Ident x1, Ident x2) ->
        (match (find_var x1 ev, find_var x2 ev) with
         | (Closure (Function (xx, ee), eevv), v) -> global_env := (xx, Var (Ident x2)):: !global_env; eval_clauses ee ((xx, v)::eevv)
         | _ -> raise (IncorrectType "Function application operation has non-function operands"))
      | Proj (Ident x1, Lab l1) ->
        (match (find_var x1 ev) with
         | Closure (Record r, eevv)-> find_var (get_record_val r l1) eevv
         | _ -> raise (IncorrectType "Projection operation has non-record operands"))
      | Match (Ident x1, p) ->
        (let rec match_pattern x1 p =
           (match p with
            | (pp, ee)::tl -> if (pattern_match x1 pp ev) then eval_clauses ee ev else match_pattern x1 tl
            | _ -> raise PatternNotMatched)
        in match_pattern x1 p)
      | _ -> raise BodyNotMatched
and eval_clauses (clauses:expr) (ev:env)=
  match clauses with
  | Clause (Ident x, b)::[] -> let res = eval_body b ev (Ident x) in (global_env := (Ident x, res) :: !global_env; res)
  | Clause (Ident x, b)::tl -> let res = eval_body b ev (Ident x) in (global_env := (Ident x, res) :: !global_env; eval_clauses tl ((Ident x, res)::ev))
  | _ -> raise ClauseNotMatched;;

(* let res = eval_clauses tl ((Ident x, eval_body b ev (Ident x))::ev) in (global_env := (Ident x, res) :: !global_env; res) *)

let eval clauses = global_env:= []; (eval_clauses clauses [], global_env);;

(*
x1 = 1
x2 = 2
x3 = x1+x2
should return 3
global_env = {x1->1, x2->2, x3->3}
*)
let in1 = [Clause (Ident "x1", Int 1); Clause (Ident "x2", Int 2); Clause (Ident "x3", Plus (Ident "x1", Ident "x2"))];;
let out1 = eval in1;;

(*
x1 = 1
x2 = Fun y -> {
        xx = 2
        xx2 = xx+y
      }
x3 = x2 x1
same as: (Fun y -> y+2) 1
should return 3
global_env = {x1->1, x2->Fun..., x3 ->3, xx->2, xx2-> 3, y -> x1}    x2 here is a closure!
*)
let in2 = [Clause(Ident "x1", Int 1); Clause(Ident "x2", Function (Ident "y", [Clause(Ident "xx", Int 2); Clause(Ident "xx2", Plus (Ident "xx", Ident "y"))])); Clause (Ident "x3", Appl(Ident "x2", Ident "x1"))];;
let out2 = eval in2;;

(*
x1 = 1
x2 = {a:x1}
x3 = x2.a
should return 1
global_env = {x1->1, x2->Closure({a:x1}, [x1->1]), x3->1}
*)
let in3 = [Clause(Ident "x1", Int 1); Clause(Ident "x2", Record [(Lab "a", Ident "x1")]); Clause (Ident "x3", Proj (Ident "x2", Lab "a"))];;
let out3 = eval in3;;

(*
x1 = 1
x2 = Match x1 with
      | PInt -> {
            x3 = 2
        }
should return 2
global_env = {x1->1, x3->2, x2->2}
*)
let in4 = [Clause(Ident "x1", Int 1); Clause (Ident "x2", Match (Ident "x1", [(PInt, [Clause (Ident "x3", Int 2)])]))];;
let out4 = eval in4;;
global_env;;

(*
x1 = 1
x2 = {a:x1}
x3 = Match x2 with
    {a:PInt} -> {
              x4 = 4
          }
should return 4
global_env = {x1->1, x2 -> Closure({a:x1}, [x1->1]), x3->4, x4->4}
*)
let in5 = [Clause(Ident "x1", Int 1); Clause (Ident "x2", Record [(Lab "a", Ident "x1")]); Clause (Ident "x3", Match (Ident "x2", [PRecord [(Lab "a", PInt)],[Clause (Ident "x4", Int 4)]]))];;
let out5 = eval in5;;
global_env;;

(*
x1 = 1
x2 = 2
x3 = {a:x1, b: x2}
x4 = Match x3 with
      | {a:PInt} -> {x5 = 4}
should return 4
global_env = {x1->1, x2->1, x3->Closure({a:x1, b:x2}, [x1->1, x2->1]), x4->4, x5->4}
*)
let in6 = [Clause(Ident "x1", Int 1); Clause(Ident "x2", Int 2); Clause (Ident "x3", Record [(Lab "a", Ident "x1");(Lab "b", Ident "x2")]); Clause (Ident "x4", Match (Ident "x3", [PRecord [(Lab "a", PInt)],[Clause (Ident "x5", Int 4)]]))];;
let out6 = eval in6;;

(*
x1 = 1
x2 = x1
should return 1
global_env = {x1->1, x2->1, x2->x1}
*)
let in7 = [Clause(Ident "x1", Int 1); Clause(Ident "x2", Var (Ident "x1"))];;
let out7 = eval in7;;

(*
x1 = 1;
x2 = 2;
x3 = {a:x1, b:x2}
x4 = 3
x5 = {c:x3, d: x4}
x6 = Match x5 with
  | {c:{a:PInt, b:PTrue}} -> x7=7
  | PStar -> x8 = 8
*)

let in8 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Int 2);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Int 3);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PTrue)])], [Clause (Ident "x7", Int 7)]);
                                                   (PStar, [Clause (Ident "x8", Int 8)])]))];;
let out8 = eval in8;;

(*
x1 = Fun f ->
    y = Fun x -> {
                x2 = 0;
                x3 = Equals (x, x2)
                x4 = Match x3 with
                | PTrue -> 0
                | PFalse -> {
                        x5 = f f
                        x11 = 1;
                        x6 = x-x11;
                        x7 = x5 x6
                        x8 = x + x7
                        }
          }
x9 = x1 x1
x10 = 6
x12 = x9 x10

should return 21
*)

let in9 = [Clause (Ident "x1", Function (Ident "f",
                                         [Clause (Ident "y", Function (Ident "x",
                                                                       [Clause (Ident "x2", Int 0);
                                                                        Clause (Ident "x3", Equals (Ident "x", Ident "x2"));
                                                                        Clause (Ident "x4", Match (Ident "x3",
                                                                                                   [(PTrue, [Clause (Ident "xx", Int 0)]);
                                                                                                    (PFalse, [Clause (Ident "x5", Appl (Ident "f", Ident "f"));
                                                                                                              Clause (Ident "x11", Int 1);
                                                                                                              Clause (Ident "x6", Minus (Ident "x", Ident "x11"));
                                                                                                              Clause (Ident "x7", Appl (Ident "x5", Ident "x6"));
                                                                                                              Clause (Ident "x8", Plus (Ident "x", Ident "x7"))])]))]))]));
           Clause (Ident "x9", Appl (Ident "x1", Ident "x1"));
           Clause (Ident "x10", Int 6);
           Clause (Ident "x12", Appl (Ident "x9", Ident "x10"))];;

let out9 = eval in9;;

(*
tru = True;
fals = False;

f = fun bf -> (
  fr = Match bf with
      | PTrue ->
       x1 = fun bfm -> (
         bfmr = g tru;
       )
      | Pfalse ->
        x2 = fun bfa -> (
         bfar = bfa;
       );
);
g = fun bg -> (
  gr = Match bg with
      | PTrue ->
       x3 = fun bgm -> (
         bgmr = f fals;
       )
       | PFalse ->
          x4 = fun bga -> (
         bgar = bga;
       );
);
r = f tru; # => false *)

let in10 = [Clause (Ident "tru", True);
            Clause (Ident "fals", False);
            Clause (Ident "f", Function (Ident "bf", [Clause (Ident "fr", Match (Ident "bf",
                                                                                 [(PTrue, [Clause (Ident "x1", Function (Ident "bfm",
                                                                                                                         [Clause (Ident "bfmr", Appl (Ident "g", Ident "tru"))]))]);
                                                                                  (PFalse, [Clause (Ident "x2", Function (Ident "bfa",
                                                                                                                          [Clause (Ident "bfar", Var (Ident "bfa"))]))])]))]));
            Clause (Ident "g", Function (Ident "bg", [Clause (Ident "gr", Match (Ident "bg",
                                                                                 [(PTrue, [Clause (Ident "x3", Function (Ident "bgm",
                                                                                                                         [Clause (Ident "bgmr", Appl (Ident "f", Ident "fals"))]))]);
                                                                                  (PFalse, [Clause (Ident "x4", Function (Ident "bga",
                                                                                                                          [Clause (Ident "bgar", Var (Ident "bga"))]))])]))]));
            Clause (Ident "r", Appl (Ident "f", Ident "tru"))];;
let out10 = eval in10;;

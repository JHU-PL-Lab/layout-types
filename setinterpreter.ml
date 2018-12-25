open Layout;;

let dataflow = ref [];;

let rec find_var x envir =
  match envir with
  | (Ident x1, b)::tl -> if x = x1 then b else find_var x tl
  | _ -> Empty;;

let rec get_record_val r l =
  match r with
  | (Lab lab, Ident x)::tl -> if l =lab then x else get_record_val tl l
  | _ -> "No Matching Label";;

(* Returns true if given environment ev, the variable x matches the pattern p
   See commit 31a09f, Definition 1.1*)
let rec pattern_match x (p:pattern) (ev:env) =
  match (find_var x ev, p) with
  | (Int _, PInt) -> true
  | (True, PTrue) -> true
  | (False, PFalse) -> true
  | (Closure(Function _, _), PFun) -> true
  | (Closure(Record r1, eevv), PRecord p1) ->
    let rec iterate_record r pp =
      (match (r,pp) with
       | ((Lab l1, Ident x1)::tl, (Lab l2, p2)) -> if l1 = l2 then (pattern_match x1 p2 eevv) else (iterate_record tl pp)
       | _ -> false) in
    (let rec iterate_record_pattern r p1 =
       match p1 with
       | hd::tl -> if (iterate_record r hd) then iterate_record_pattern r tl else false
       | _ -> true
     in iterate_record_pattern r1 p1)
  | (_, PStar) -> true
  |  _ -> false;;

(* Get the last variable in the list e
   Used to get dataflow *)
let rec get_last_variable_from_expr e =
  match e with
  | Clause (Ident x, _)::[] -> x
  | _::tl -> get_last_variable_from_expr tl
  | _ -> raise ClauseNotMatched;;

(* Interpreter, also collect data flow
   See commit 31a09f, Definition 2.1 and Figure 4 *)
let rec eval_body (b:body) (ev:env) (flowto: ident)=
  match b with
  | Int n -> Int n
  | True -> True
  | False -> False
  | Amb a -> Amb a
  | Var (Ident x) -> dataflow := (flowto, Var (Ident x))::!dataflow; find_var x ev
  | Function _ -> Closure (b, ev)
  | Record _ -> Closure (b, ev)
  | Plus (Ident x1, Ident x2) ->
    (match (find_var x1 ev, find_var x2 ev) with
     | (Int i1, Int i2) -> Int (i1+i2)
     | _ -> Empty)
  | Minus (Ident x1, Ident x2) ->
    (match (find_var x1 ev, find_var x2 ev) with
     | (Int i1, Int i2) -> Int (i1-i2)
     | _ -> Empty)
  | Not (Ident x1) ->
    (match find_var x1 ev with
     | True -> False
     | False -> True
     | _ -> Empty)
  | And (Ident x1, Ident x2) ->
    (match (find_var x1 ev, find_var x2 ev) with
     | (True, False) -> False
     | (True, True) -> True
     | (False, True) -> False
     | (False, False) -> False
     | _ -> Empty)
  | Or (Ident x1, Ident x2) ->
    (match (find_var x1 ev, find_var x2 ev) with
     | (True, False) -> True
     | (True, True) -> True
     | (False, True) -> True
     | (False, False) -> False
     | _ -> Empty)
  | Equals (Ident x1, Ident x2) ->
    (match (find_var x1 ev, find_var x2 ev) with
     | (Int i1, Int i2) -> if i1 = i2 then True else False
     | _ -> Empty)
  | Appl (Ident x1, Ident x2) ->
    (match (find_var x1 ev, find_var x2 ev) with
     | (Closure (Function (xx, ee), eevv), v) ->
       dataflow := (xx, Var (Ident x2)):: !dataflow;
       dataflow := (flowto, Var (Ident (get_last_variable_from_expr ee))) :: !dataflow;
       eval_clauses ee ((xx, v)::eevv)
     | _ -> Empty)
  | Proj (Ident x1, Lab l1) ->
    (match (find_var x1 ev) with
     | Closure (Record r, eevv)-> let i = get_record_val r l1 in (dataflow := (flowto, Var (Ident i))::!dataflow;
                                                                  find_var i eevv)
     | _ -> Empty)
  | Match (Ident x1, p) ->
    (let rec match_pattern x1 p =
       (match p with
        | (pp, ee)::tl -> if (pattern_match x1 pp ev) then (dataflow := (flowto, Var (Ident (get_last_variable_from_expr ee)))::!dataflow;
                                                            eval_clauses ee ev)
          else match_pattern x1 tl
        | _ -> Empty)
     in match_pattern x1 p)
  | _ -> raise BodyNotMatched
and eval_clauses (clauses:expr) (ev:env)=
  match clauses with
  | Clause (Ident x, b)::[] -> let res = eval_body b ev (Ident x) in (match res with
    | Amb a -> Amb a
    | _ -> Amb [res])
  | Clause (Ident x, b)::tl ->
    let rec fork l =
      (match l with
       | hhdd::[] ->  eval_clauses tl ((Ident x, hhdd)::ev);
       | hhdd::ttll -> ((match (eval_clauses tl ((Ident x, hhdd)::ev),fork ttll) with
                         | (Amb a1,Amb a2) -> Amb (a1@a2)
                         | _ -> raise ForkFailed))
       | _ -> raise ClauseNotMatched)
    in (let res = eval_body b ev (Ident x) in
        match res with
        | Amb l -> fork l
        | _ -> eval_clauses tl ((Ident x, res)::ev))
  | _ -> raise ClauseNotMatched;;

let eval clauses = dataflow:= [];(eval_clauses clauses [], dataflow);;

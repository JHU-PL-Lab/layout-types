open Layout;;
open Setinterpreter;;
open Typechecker;;

(* Runtime tagged interpreter *)

(* Find the body and tag of a variable x in the environment envir *)
let rec find_tagged_var x envir =
  match envir with
  | (Ident x1, btag)::tl -> if x = x1 then btag else find_tagged_var x tl
  | _ -> (Empty, Nonce (-1));;

(* Get the entry in rou for program point x *)
let rec get_rou rou x =
  match rou with
  | (Ident xx, entry)::tl -> if x = xx then entry else get_rou tl x
  | _ -> [];;

(* Get the entry in the dispatch table delta for program point x *)
let rec get_delta delta x =
  match delta with
  | (Ident xx, entry)::tl -> if x = xx then entry else get_delta tl x
  | _ ->[];;

let get_nounce_from_rou nlist rou =
  let rec match_entry nlist entry =
    match (nlist, entry) with
    | ([],[]) -> true
    | (nc1::tl1, (Nonce nc2)::tl2) -> if nc1 = nc2 then match_entry tl1 tl2 else false
    | _ -> false
  in let rec iterate_rou nlist rou =
    match rou with
    | (entry, nc)::tl -> if match_entry nlist entry then Nonce nc else iterate_rou nlist rou
    | _ -> Nonce (-1)
  in iterate_rou nlist rou;;

  let get_matching_nounce typedec x tb =
    let rec iterate_tau tau tb =
      match tau with
      | (T (bt, []), Nonce nc)::tl -> if bt=tb then nc::(iterate_tau tl tb) else iterate_tau tl tb
      | hd::tl -> iterate_tau tl tb
      | _ -> []
    in iterate_tau (find_tau typedec x) tb;;

  let get_projection_nounce typedec x lab =
    let rec exists_lab lr lab=
      match lr with
      | (Lab l1, bt)::tl -> if l1 = lab then true else exists_lab tl lab
      | _ -> false
    in let rec iterate_tau tau lab =
         match tau with
         | (T (LRecord lr, []), Nonce nc)::tl -> if (exists_lab lr lab) then nc::(iterate_tau tl lab) else iterate_tau tl lab
         | hd::tl -> iterate_tau tl lab
         | _ -> []
    in iterate_tau (find_tau typedec x) lab;;

  let rec get_runtime_success_dispatch_table (program:tagged_expr) typedec=
    match program with
    | TaggedClause (Ident x, Tau tau, Plus (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LInt);(get_matching_nounce typedec x2 LInt)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, Minus (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LInt);(get_matching_nounce typedec x2 LInt)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, Not (Ident x1))::tl -> (Ident x, [(get_matching_nounce typedec x1 LTrue)@(get_matching_nounce typedec x1 LFalse)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, And (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LTrue)@(get_matching_nounce typedec x1 LFalse);(get_matching_nounce typedec x2 LTrue)@(get_matching_nounce typedec x2 LFalse)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, Or (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LTrue)@(get_matching_nounce typedec x1 LFalse);(get_matching_nounce typedec x2 LTrue)@(get_matching_nounce typedec x2 LFalse)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, Equals (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LInt);(get_matching_nounce typedec x2 LInt)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, Appl (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LFun)])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, Proj (Ident x1, Lab lab))::tl -> (Ident x, [get_projection_nounce typedec x1 lab])::(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, TaggedFunction (Ident x1, e))::tl -> (get_runtime_success_dispatch_table e typedec)@(get_runtime_success_dispatch_table tl typedec)
    | TaggedClause (Ident x, Tau tau, TaggedMatch (Ident x1, pe))::tl ->
      (let rec iterate_pattern_clause pe typedec=
         (match pe with
          | (p, e)::tl-> (get_runtime_success_dispatch_table e typedec)@(iterate_pattern_clause tl typedec)
          | _ -> [])
       in (iterate_pattern_clause pe typedec)@(get_runtime_success_dispatch_table tl typedec))
    | hd::tl -> get_runtime_success_dispatch_table tl typedec
    | _ -> [];;

(* use runtime success table to check whether exists any runtime error*)
let check_runtime_success rst x indices =
  let rec find_entry rst x =
    (match rst with
     | (Ident xx, entry)::tl -> if x = xx then entry else find_entry tl x
     | _ -> [])
  in let rec check_index l ind =
       (match l with
        | hd::tl -> if hd = ind then true else check_index tl ind
        | _ -> false)
  in let rec check_success entry indices =
       (match (entry, indices) with
        | (l1::tl1, ind2::tl2) -> if check_index l1 ind2 then check_success tl1 tl2 else false
        | _ -> true)
  in check_success (find_entry rst x) indices;;

let rec tagged_eval_body (b:body) tau ev flowto rou delta rst=
    match b with
      | Int n -> (match tau with
          | [(T (LInt, []), Nonce nc)]-> (Int n, Nonce nc)
          | _ -> (Empty, Nonce (-1)))
      | True -> (match tau with
          | [(T (LTrue, []), Nonce nc)] -> (True, Nonce nc)
          | _ -> (Empty, Nonce (-1)))
      | False -> (match tau with
          | [(T (LFalse, []), Nonce nc)] -> (False, Nonce nc)
          | _ -> (Empty, Nonce (-1)))
      | Var (Ident x) -> find_tagged_var x ev
      | TaggedFunction (x1, e1) -> (match tau with
          | [(T (LFun, []), Nonce nc)]-> (TaggedClosure (b, ev), Nonce nc)
          | _ -> (Empty, Nonce (-1)))
      | Record rc ->
        let rec get_record_field_nounce rc =
          match rc with
          | (lab, Ident x) :: tl ->
            (match find_tagged_var x ev with
             | (_ , Nonce nc) -> nc)::get_record_field_nounce tl
          | _ -> []
        in (TaggedClosure (b, ev), get_nounce_from_rou (get_record_field_nounce rc) (get_rou rou flowto))
      | Plus (Ident x1, Ident x2) ->
       (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((Int i1, Nonce nc1), (Int i2, Nonce nc2)) -> (match tau with
           | [(T (LInt, []), Nonce nc)]-> if (check_runtime_success rst flowto [nc1; nc2]) then (Int (i1+i2), Nonce nc) else (Empty, Nonce (-1))
           | _ -> (Empty, Nonce (-1)))
       | _ -> (Empty, Nonce (-1)))
    | Minus (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((Int i1, Nonce nc1), (Int i2, Nonce nc2)) -> (match tau with
           | [(T (LInt, []), Nonce nc)]-> if (check_runtime_success rst flowto [nc1; nc2]) then (Int (i1-i2), Nonce nc) else (Empty, Nonce (-1))
           | _ -> (Empty, Nonce (-1)))
       | _ -> (Empty, Nonce (-1)))
    | Not (Ident x1) ->
      (match (find_tagged_var x1 ev, tau) with
       | ((True, Nonce nc1), [(T (LFalse, []), Nonce nc)]) -> if (check_runtime_success rst flowto [nc1]) then (False, Nonce nc) else (Empty, Nonce (-1))
       | ((False, Nonce nc1), [(T (LTrue, []), Nonce nc)]) -> if (check_runtime_success rst flowto [nc1]) then (True, Nonce nc) else (Empty, Nonce (-1))
       | _ -> (Empty, Nonce (-1)))
    | And (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev, tau) with
       | ((True, Nonce nc1), (False, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (False, Nonce nc4) else (Empty, Nonce (-1))
       | ((True, Nonce nc1), (True, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (True, Nonce nc3) else (Empty, Nonce (-1))
       | ((False, Nonce nc1), (True, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (False, Nonce nc4) else (Empty, Nonce (-1))
       | ((False, Nonce nc1), (False, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (False, Nonce nc4) else (Empty, Nonce (-1))
       | _ -> (Empty, Nonce (-1)))
    | Or (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev, tau) with
       | ((True, Nonce nc1), (False, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (True, Nonce nc3) else (Empty, Nonce (-1))
       | ((True, Nonce nc1), (True, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (True, Nonce nc3) else (Empty, Nonce (-1))
       | ((False, Nonce nc1), (True, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (True, Nonce nc3) else (Empty, Nonce (-1))
       | ((False, Nonce nc1), (False, Nonce nc2), [(T (LTrue, []), Nonce nc3);(T (LFalse, []), Nonce nc4)]) -> if (check_runtime_success rst flowto [nc1;nc2]) then (False, Nonce nc4) else (Empty, Nonce (-1))
       | _ -> (Empty, Nonce (-1)))
    | Equals (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((Int i1, Nonce nc1), (Int i2, Nonce nc2)) -> if i1 = i2 && (check_runtime_success rst flowto [nc1;nc2]) then (match tau with
                                                                     | [(T (LTrue, []), Nonce nc)] -> (True, Nonce nc)
                                                                     | _ -> (Empty, Nonce (-1)))
                                                                else (match tau with
                                                                     | [(T (LFalse, []), Nonce nc)] -> (False, Nonce nc)
                                                                     | _ -> (Empty, Nonce (-1)))
       | _ -> (Empty, Nonce (-1)))
    | Appl (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((TaggedClosure (TaggedFunction (xx, ee), eevv), Nonce nc1), v) -> if (check_runtime_success rst flowto [nc1]) then (tagged_eval_clauses ee ((xx, v)::eevv) rou delta rst) else (Empty, Nonce (-1))
       | _ -> (Empty, Nonce (-1)))
    | Proj (Ident x1, Lab l1) ->
      (match (find_tagged_var x1 ev) with
       | (TaggedClosure (Record r, eevv), Nonce nc1)->if (check_runtime_success rst flowto [nc1]) then find_tagged_var (get_record_val r l1) eevv else (Empty, Nonce (-1))
       | _ -> (Empty, Nonce (-1)))
    | TaggedMatch (Ident x1, p) ->
      let rec find_clause_num delta nounce =
        match delta with
        | (n1, clause_num)::tl -> if nounce = n1 then clause_num else find_clause_num tl nounce
        | _ -> -1
      in let rec get_clause p num =
           match p with
           | (p1, e1)::tl -> if num = 1 then e1 else get_clause tl (num-1)
           | _ -> []
      in let (v, nounce) = find_tagged_var x1 ev
      in tagged_eval_clauses (get_clause p (find_clause_num (get_delta delta flowto) nounce)) ev rou delta rst
    | _ -> raise BodyNotMatched
and tagged_eval_clauses (clauses:tagged_expr) (ev:tagged_env) rou delta rst =
  match clauses with
  | TaggedClause (Ident x, Tau tau, b)::[] ->  tagged_eval_body b tau ev x rou delta rst
  | TaggedClause (Ident x,Tau tau, b)::tl -> let res = tagged_eval_body b tau ev x rou delta rst in tagged_eval_clauses tl ((Ident x, res)::ev) rou delta rst
  | _ -> raise ClauseNotMatched;;

let tagged_eval (clauses:tagged_expr) =
  let (_, rou, delta) = typecheck clauses
  in tagged_eval_clauses clauses [] rou delta (get_runtime_success_dispatch_table clauses (get_all_typedec clauses));;

(*
x1:Int = 1
x2:Int = 2
x3:Int = x1+x2

should return 3
sound = true
rou = []
delta = []
*)
let in1 = [TaggedClause (Ident "x1",Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2",Tau [( T (LInt, []), Nonce 2)], Int 2);
           TaggedClause (Ident "x3",Tau [( T (LInt, []), Nonce 3)], Plus (Ident "x1", Ident "x2"))];;
let res1 = tagged_eval in1;;

(*
x1:True = True
x2:False = False
x3:[True;False] = x1 && x2

should return False
*)
let in2 = [TaggedClause (Ident "x1",Tau [( T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x2",Tau [( T (LFalse, []), Nonce 2)], False);
           TaggedClause (Ident "x3",Tau [( T (LTrue, []), Nonce 3); ( T (LFalse, []), Nonce 4)], And (Ident "x1", Ident "x2"))];;
let res2 = tagged_eval in2;;

(*
x1:Int = 1
x2:Int = x1

should return 1
*)
let in3 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LInt, []), Nonce 2)], Var(Ident "x1"))];;
let res3 = tagged_eval in3;;

(*
x1:[(LInt-{}, Nonce 1)] = 1
x2:[(LTrue-{}, Nonce 2)] = True
x3 : [({a:Int; b: True}-{}, Nonce 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

should return 3
*)
let in4 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 5)], Int 3)])]))];;
let res4 = tagged_eval in4;;

(*
x1:Int = 1;
x2:True = true
x3:Record = {a:x1; b:x2}
x4:Int = x3.a *)

let in5 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
            TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 2)], True);
            TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
            TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], Proj (Ident "x3", Lab "a"))];;
let res5 = tagged_eval in5;;

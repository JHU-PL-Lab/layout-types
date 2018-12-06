type ident = Ident of string;;
type label = Lab of string;;

type ind = Ind of int;;
type bt = LRecord of (label * bt) list | LInt | LTrue | LFalse | LFun | LStar | LEmpty;;
type t =  T of bt * (bt list);;
type tau = Tau of (t * ind) list;;

type body = Int of int | True | False | Closure of body * env | Function of ident * expr | Record of (label * ident) list | OrVal of body list | Empty
          | Var of ident | Appl of ident * ident | Proj of ident * label
          | Plus of ident * ident | Minus of ident * ident | LessThan of ident * ident | Equals of ident * ident
          | And of ident * ident | Or of ident * ident | Not of ident
          | Match of ident * (pattern * expr) list
and env = (ident * body) list
and tagged_env = (ident * (body * ind)) list
and clause = Clause of ident * body
and expr = clause list
and pattern = PRecord of (label * pattern) list | PInt | PTrue | PFalse | PFun | PStar;;

exception BodyNotMatched;;
exception ClauseNotMatched;;
exception ForkFailed;;
exception CannotFindTau;;
exception TypeInferenceException;;

let global_env = ref [];;

let rec find_var x envir =
  match envir with
  | (Ident x1, b)::tl -> if x = x1 then b else find_var x tl
  | _ -> Empty;;

let rec get_record_val r l =
  match r with
  | (Lab lab, Ident x)::tl -> if l =lab then x else get_record_val tl l
  | _ -> "No Matching Label";;

let rec pattern_match x (p:pattern) (ev:env) =
  match (find_var x ev, p) with
  | (Int n, PInt) -> true
  | (True, PTrue) -> true
  | (False, PFalse) -> true
  | (Closure(Function (x1, e1), eevv), PFun) -> true
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

let rec get_last_variable_from_expr e =
  match e with
  | Clause (Ident x, b)::[] -> x
  | hd::tl -> get_last_variable_from_expr tl
  | _ -> raise ClauseNotMatched;;

let rec eval_body (b:body) (ev:env) (flowto: ident)=
  match b with
  | Int n -> Int n
  | True -> True
  | False -> False
  | OrVal o -> OrVal o
  | Var (Ident x) -> global_env := (flowto, Var (Ident x))::!global_env; find_var x ev
  | Function (x1, e1) -> Closure (b, ev)
  | Record rc -> Closure (b, ev)
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
       global_env := (xx, Var (Ident x2)):: !global_env;
       global_env := (flowto, Var (Ident (get_last_variable_from_expr ee))) :: !global_env;
       eval_clauses ee ((xx, v)::eevv)
     | _ -> Empty)
  | Proj (Ident x1, Lab l1) ->
    (match (find_var x1 ev) with
     | Closure (Record r, eevv)-> let i = get_record_val r l1 in (global_env := (flowto, Var (Ident i))::!global_env;
                                                                  find_var i eevv)
     | _ -> Empty)
  | Match (Ident x1, p) ->
    (let rec match_pattern x1 p =
       (match p with
        | (pp, ee)::tl -> if (pattern_match x1 pp ev) then (global_env := (flowto, Var (Ident (get_last_variable_from_expr ee)))::!global_env;
                                                            eval_clauses ee ev)
          else match_pattern x1 tl
        | _ -> Empty)
     in match_pattern x1 p)
  | _ -> raise BodyNotMatched
and eval_clauses (clauses:expr) (ev:env)=
  match clauses with
  | Clause (Ident x, b)::[] -> let res = eval_body b ev (Ident x) in (global_env := (Ident x, res) :: !global_env; match res with
    | OrVal o -> OrVal o
    | _ -> OrVal [res])
  | Clause (Ident x, b)::tl ->
    let rec fork l =
      (match l with
       | hhdd::[] -> global_env := (Ident x, hhdd) :: !global_env; eval_clauses tl ((Ident x, hhdd)::ev);
       | hhdd::ttll -> (global_env := (Ident x, hhdd) :: !global_env;
                        (match (eval_clauses tl ((Ident x, hhdd)::ev),fork ttll) with
                         | (OrVal o1,OrVal o2) -> OrVal (o1@o2)
                         | _ -> raise ForkFailed))
       | _ -> raise ClauseNotMatched)
    in (let res = eval_body b ev (Ident x) in
        match res with
        | OrVal l -> fork l
        | _ -> (global_env := (Ident x, res) :: !global_env; eval_clauses tl ((Ident x, res)::ev)))
  | _ -> raise ClauseNotMatched;;

let eval clauses = global_env:= [];(eval_clauses clauses [], global_env);;


(* Type inference *)
let fresh_nounce = ref 0;;

let get_fresh_nounce e = fresh_nounce := !fresh_nounce+1; let nounce = !fresh_nounce in nounce;;

let rec is_subtype_bt (bt1:bt) (bt2:bt) =
  match (bt1, bt2) with
  | (_ , LStar) -> true
  | (LInt, LInt) -> true
  | (LFalse, LFalse) -> true
  | (LTrue, LTrue) -> true
  | (LFun, LFun) -> true
  | (LRecord l1, LRecord l2) ->
    let rec iterate_record l1 e2 =
      match (l1,e2) with
      | ((Lab lab1, bt1)::tl,(Lab lab2, bt2)) -> if lab1 = lab2 then is_subtype_bt bt1 bt2 else iterate_record tl e2
      | _ -> false
    in (let rec check_record l1 l2 =
          match l2 with
          | e2::tl -> if iterate_record l1 e2 then check_record l1 tl else false
          | _ -> true in check_record l1 l2)
  | _ -> false;;

let rec conflict bt1 bt2 =
   (match (bt1,bt2) with
    | (LEmpty, _ ) -> true
    | (_, LEmpty ) -> true
    | (LStar, _ ) -> false
    | (_, LStar) -> false
    | (LInt, LInt) -> false
    | (LInt, _ )->true
    | (LTrue, LTrue) -> false
    | (LTrue, _ ) -> true
    | (LFalse, LFalse) -> false
    | (LFalse, _ ) -> true
    | (LFun, LFun) -> false
    | (LFun, _ ) -> true
    | (LRecord r1, LRecord r2) -> false
    | (LRecord r1, _ ) -> true
   );;

(* canonicalize *)
let canonicalize_t t =
  let is_empty_t bt neg =
    (match (bt, neg) with
     | (LEmpty, _ ) -> true
     | _ -> false)
  in let rec tb_is_subtype_neg bt neg =
       match neg with
       | neg1::tl -> if is_subtype_bt bt neg1 then true else tb_is_subtype_neg bt tl
       | _ -> false
  in let rec reform_neg neg bt all_neg num =
       match neg with
       | LEmpty::tl -> reform_neg tl bt all_neg (num+1)
       | neg1::tl ->
         let rec is_subtype_any_neg neg num1 =
            (match neg with
              | neg2::ttll -> if ((num != num1)&&(is_subtype_bt neg1 neg2)) then true else is_subtype_any_neg ttll (num1+1)
              | _ -> false)
         in if (conflict neg1 bt) || (is_subtype_any_neg all_neg 1) then reform_neg tl bt all_neg (num+1) else neg1::(reform_neg tl bt all_neg (num+1))
       | _ -> []
  in match t with
  | T (bt, neg) -> if ((tb_is_subtype_neg bt neg) || (is_empty_t bt neg)) then T (LEmpty, []) else T (bt, reform_neg neg bt neg 1);;

let canonicalize_tau tau =
  let rec iterate_tau tau =
    match tau with
    | (t, ind)::tl ->
      (match canonicalize_t t with
      | T (LEmpty, []) -> iterate_tau tl
      | t -> (t, ind)::(iterate_tau tl))
    | _ -> []
(* in iterate_tau tau;;  *)
  in let rec remove_duplicate_star tau has_star=
       match tau with
       | (T (LStar, []), ind)::tl -> if has_star then (remove_duplicate_star tl true) else (T (LStar, []), ind)::(remove_duplicate_star tl true)
       | hd::tl -> hd::(remove_duplicate_star tl has_star)
       | _ -> []
  in remove_duplicate_star (iterate_tau tau) false;;

(* intersect *)
let rec intersect_bt (bt1:bt) (bt2:bt) =
  match (bt1, bt2) with
  | (LStar, bt) -> bt
  | (bt, LStar) -> bt
  | (LInt, LInt) -> LInt
  | (LTrue, LTrue) -> LTrue
  | (LFalse, LFalse) -> LFalse
  | (LFun, LFun) -> LFun
  | (LRecord lr1, LRecord lr2) ->
    (let intersect_common lr1 lr2 =
       ( let rec find_field r lab =
           match r with
           | (Lab l2, bt)::tl -> if lab = l2 then bt else find_field tl lab
           | _ -> LEmpty
         in let rec iterate_r1 lr1 lr2 =
          match lr1 with
            | (Lab lab, bt1)::tl ->
              (match find_field lr2 lab with
               | LEmpty -> iterate_r1 tl lr2
               | bt2 -> (Lab lab, intersect_bt bt1 bt2)::(iterate_r1 tl lr2))
            | _ -> []
        in iterate_r1 lr1 lr2)
      (* get the fields only in lr1 but not in lr2 *)
     in let get_exclusive lr1 lr2 =
          let rec find_field r lab1=
            match r with
            | (Lab lab2, _ )::tl -> if lab1 = lab2 then true else find_field tl lab1
            | _ -> false
          in let rec iterate_record r lr2 =
            (match r with
              | (Lab lab, bt)::tl -> (if (find_field lr2 lab) then (iterate_record tl lr2) else (Lab lab, bt)::(iterate_record tl lr2))
              | _ -> [])
          in iterate_record lr1 lr2
    in LRecord ((intersect_common lr1 lr2)@ (get_exclusive lr1 lr2)@(get_exclusive lr2 lr1)))
  | _ -> LEmpty;;

let intersect_t t1 t2 =
  match (t1, t2) with
  | (T (bt1, neg1), T(bt2, neg2)) -> T (intersect_bt bt1 bt2, neg1@neg2);;

(* Transform match matterns to union of tags *)
let pToTau pa =
  let rec pToBt p =
    (match p with
    | PInt -> LInt
    | PTrue -> LTrue
    | PFalse -> LFalse
    | PFun -> LFun
    | PStar -> LStar
    | PRecord pr ->
      let rec iterate_record pr =
        (match pr with
         | (Lab lab, ppaa)::tl -> (Lab lab, pToBt ppaa)::(iterate_record tl)
         | _ -> [])
      in LRecord (iterate_record pr)
    )
  in let rec get_neg pa num = if num = 1 then [] else
         (match pa with
          | (p, e)::tl -> (pToBt p)::(get_neg tl (num-1))
          | _ -> raise TypeInferenceException)
  in let rec iterate_pattern pa all_pa num =
       (match pa with
        | (p, e)::tl -> (T (pToBt p, get_neg all_pa num), Ind (get_fresh_nounce 0))::(iterate_pattern tl all_pa (num+1))
        | _ -> [])
  in iterate_pattern pa pa 1;;

let nounce_flow = ref [];;

let extract_fields r t =
  let rec find_field_t lr lab is_neg =
    match lr with
    | (Lab l, bt)::tl -> if l = lab then bt else find_field_t tl lab is_neg
    | _ -> if is_neg then LEmpty else LStar
  in let proj_field bt l is_neg=
      (match bt with
       | LStar -> LStar
       | LRecord lr -> find_field_t lr l is_neg
       | _ -> LEmpty)
  in let rec iterate_neg_t neg l =
       (match neg with
        | bt::tl -> (proj_field bt l true)::(iterate_neg_t tl l)
        | _ -> [])
  in let rec iterate_t l tau =
    (match tau with
      | (T (bt, neg), Ind ind )::tl -> let nounce = get_fresh_nounce 0 in ( nounce_flow := (Ind nounce, Ind ind)::(!nounce_flow);(T (proj_field bt l false, iterate_neg_t neg l), Ind nounce)::(iterate_t l tl))
      | _ -> [])
  in let rec iterate_r r tau=
    (match r with
      | (Lab l, Ident x1)::tl -> (x1, canonicalize_tau (iterate_t l tau))::(iterate_r tl tau)
      | _ -> [])
  in iterate_r r t;;

(* let res = extract_fields [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")] [(T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], [LRecord [(Lab "a", LFalse)]]), Ind 1)];; *)

(* propagate x with type t using dataflow df *)
let rec backward_propagate all_df x t =
  let rec iterate_df df =
    (match df with
    | (Ident x1, Var (Ident x2))::tl -> if x1 = x then (backward_propagate all_df x2 t)@(iterate_df tl) else iterate_df tl
    | (Ident x1, Closure(Record r, env))::tl ->
      (if x1 = x then
         (let rec propagate_all all_fields =
            (match all_fields with
             | (xx, tt)::tl -> (backward_propagate all_df xx tt)@(propagate_all tl)
             | _ -> [])
         in propagate_all (extract_fields r t))
       else []) @(iterate_df tl)
    | hd::tl -> iterate_df tl
    | _ ->[(Ident x, t)])
  in iterate_df all_df;;

(* when encountering a record, just make a record of the field?  *)
let forward_propagate_wrapper all_df tags =
  let equals_t t1 t2 =
    (let rec iterate_tau ind1 t2 =
       match t2 with
       | (tb2, Ind ind2)::tl -> if ind1 = ind2 then true else iterate_tau ind1 tl
       | _ -> false
      in match t1 with
      | (tb1, Ind ind1)::tl -> iterate_tau ind1 t2
      | _ -> false)
  in let rec exists_tag tags x t =
    match tags with
    | (Ident x1, t1)::tl -> if (x=x1) && (equals_t t t1) then true else exists_tag tl x t
    | _ -> false
  in let exists_nounce_flow t1 t2 =
       (let rec found_nounce_flow ind1 ind2 nounce_flow =
          match nounce_flow with
          | (Ind n1, Ind n2)::tl -> if ind1 = n1 && ind2 = n2 then true else found_nounce_flow ind1 ind2 tl
          | _ -> false
        in let rec iterate_record_tag ind1 t2 =
          match t2 with
          | (tb2, Ind ind2)::tl -> if found_nounce_flow ind1 ind2 (!nounce_flow) then true else iterate_record_tag ind1 tl
          | _ -> false
        in match t1 with
        | (tb1, Ind ind1)::tl -> iterate_record_tag ind1 t2
        | _ -> false)
  in let rec exists_tag_record field_tag x tags =
       match tags with
       | (Ident x1, t1)::tl -> if (x=x1) && (exists_nounce_flow field_tag t1) then true else exists_tag_record field_tag x tl
       | _ -> false
  in let rec forward_propagate x t df =
     match df with
     | (Ident x1, Var (Ident x2))::tl -> if x2 = x && not (exists_tag tags x1 t) then (forward_propagate x1 t all_df)@(forward_propagate x t tl) else forward_propagate x t tl
     | (Ident x1, Closure (Record r, ev))::tl ->
       let rec construct_neg_record lab neg =
         match neg with
         | bt::tl -> LRecord [(Lab lab, bt)]::(construct_neg_record lab tl)
         | _ -> []
       in let rec construct_record lab t =
         match t with
            (* May need to change the nounce here *)
         | (T(bt, neg), ind)::tl -> (T(LRecord [(Lab lab, bt)], construct_neg_record lab neg), ind)::(construct_record lab tl)
         | _ -> []
       in let rec iterate_record_field r =
         (match r with
           | (Lab lab, Ident x2)::tl -> if x = x2 && not (exists_tag_record t x1 tags) then forward_propagate x1 (construct_record lab t) all_df else iterate_record_field tl
           | _ -> [])
       in (iterate_record_field r)@(forward_propagate x t tl)
     | hd::tl -> forward_propagate x t tl
     | _ -> [(Ident x, t)]
   in let rec iterate_tags tags =
        match tags with
        | (Ident x, t)::tl -> (forward_propagate x t all_df)@(iterate_tags tl)
        | _ -> []
 in iterate_tags tags;;

(* Find all the match clauses in the program *)
let rec find_match x (program: expr) =
  match program with
  | Clause (Ident xx, Match (Ident x1, pa))::tl ->
    if xx=x then Match (Ident x1, pa)
    else (let rec iterate_patterns pa =
            (match pa with
             | (p, e)::tl -> Empty
             | _ -> Empty )
          in match (iterate_patterns pa) with
          | Match (Ident x2, ppaa) -> Match (Ident x2, ppaa)
          | _ -> find_match x tl)
  | Clause (Ident xx, Function (Ident x1, e))::tl ->
    if xx = x then Empty else
      (match (find_match x e) with
       | Match (Ident x2, pe) -> Match (Ident x1, pe)
       | _ -> find_match x tl)
  | Clause (Ident xx, body)::tl -> if xx = x then Empty else find_match x tl
  | _ -> Empty;;

let rec reform_tag tags (program:expr) =
  let cnf_to_dnf tags =
    (let rec iterate_tau tau cur rst_tags=
      match tau with
        | (t, ind)::tl -> (iterate_tags (intersect_t cur t) rst_tags)@(iterate_tau tl cur rst_tags)
        | _ ->[]
    and iterate_tags cur tags =
      match tags with
      | tau1::tl -> iterate_tau tau1 cur tl
      | _ -> [(cur, Ind 0)]
    in match tags with
      | [] -> [(T (LStar, []), Ind 0)]
      | _ -> canonicalize_tau (iterate_tags (T (LStar, [])) tags))
  in let rec get_all_vars program =
    match program with
    | Clause (Ident x, Function (Ident x1, e))::tl -> [x]@(get_all_vars tl)@(get_all_vars e)
    | Clause (Ident x, Match (Ident x1, pa))::tl ->
      let rec iterate_pa pa =
        match pa with
        | (p, e)::tl -> (get_all_vars e)@(iterate_pa tl)
        | _ -> []
      in x::(iterate_pa pa)
    | Clause (Ident x, _ )::tl -> x::get_all_vars tl
    | _ -> []
  in let rec find_tag x tags =
       match tags with
       | (Ident x1, t)::tl -> if x1 = x then t::(find_tag x tl) else find_tag x tl
       | _ -> []
  in let rec iterate_all_vars vars =
       match vars with
       | x::tl -> (Ident x, cnf_to_dnf (find_tag x tags))::(iterate_all_vars tl)
       | _ -> []
  in iterate_all_vars (get_all_vars program);;

let rec type_inference df (program: expr) = fresh_nounce := 0; nounce_flow := [];
  match df with
  | (Ident x, Var (Ident x2))::tl ->
    (match (find_match x program) with
     | Empty -> type_inference tl program
     | Match (Ident xx, pa) -> (backward_propagate df xx (canonicalize_tau (pToTau pa)))@(type_inference tl program)
     | _ -> raise TypeInferenceException)
  | (Ident x, _) ::tl -> type_inference tl program
  | _ -> [];;

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

let in1 = [ Clause (Ident "x0", Int 1);
            Clause (Ident "x1", Var (Ident "x0"));
           Clause (Ident "x2", Int 2);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Int 3);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PTrue)])], [Clause (Ident "x7", Int 7)]);
                                                   (PStar, [Clause (Ident "x8", Int 8)])]))];;
let out1 = eval in1;;
let back = type_inference (!global_env) in1;;
let forward = forward_propagate_wrapper (!global_env) back;;
let final_res = reform_tag back in1;;

let rec getident x tags =
  match tags with
  | (Ident x1, t)::tl -> if x = x1 then (Ident x, t)::getident x tl else getident x tl
  | _ -> [];;

(* getident "x3" forward;;

reform_tag [(Ident "x3",
  [(T (LRecord [(Lab "a", LInt)], []), Ind 10);
   (T (LRecord [(Lab "a", LStar)], [LRecord [(Lab "a", LInt)]]), Ind 9)]);
   (Ident "x3",
     [(T (LRecord [(Lab "a", LInt)], []), Ind 10);
      (T (LRecord [(Lab "a", LStar)], [LRecord [(Lab "a", LInt)]]), Ind 9)]);
 (Ident "x3",
  [(T (LRecord [(Lab "b", LTrue)], []), Ind 8);
   (T (LRecord [(Lab "b", LStar)], [LRecord [(Lab "b", LTrue)]]), Ind 7)]);
 (Ident "x3",
  [(T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Ind 6);
   (T (LStar, [LRecord [(Lab "a", LInt); (Lab "b", LTrue)]]), Ind 5)])] in1;; *)


(*
x1 = 1
x2 = true
x3 = {a:x1; b:x2}
x4 = match x3 with
      | {a:Int} -> x5 = 2
      | * -> x6 =3
x7 = match x3 with
      | {b:true} -> x8 = 4
      | * - > x9 = 5
x10 = x3
 *)
let in2 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt)],[Clause (Ident "x5", Int 2)]);(PStar,[Clause (Ident "x6", Int 3)])]));
           Clause (Ident "x7", Match (Ident "x3", [(PRecord [(Lab "b", PTrue)],[Clause (Ident "x8", Int 4)]);(PStar,[Clause (Ident "x9", Int 5)])]));
           Clause (Ident "x10", Var (Ident "x3"))];;
let out2 = eval in2;;
let back2 = type_inference (!global_env) in2;;
let forward2 = forward_propagate_wrapper (!global_env) back2;;
let final_res2 = reform_tag back2 in2;;
!global_env;;

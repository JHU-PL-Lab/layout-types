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
and env = (ident * body) list
and tagged_env = (ident * (body * nonce)) list
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
(* Gives a fresh nonce every time when called, e can be anything *)
let fresh_nonce = ref 0;;
let get_fresh_nonce e = fresh_nonce := !fresh_nonce+1; let nonce = !fresh_nonce in nonce;;

(* Check whether bt1 is subtype of bt2, they are both of bt type *)
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

(* Check whether bt1 equals bt2 *)
let rec equals_bt (bt1:bt) (bt2:bt) =
    match (bt1, bt2) with
    | (LStar , LStar) -> true
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
            | _ -> true
          in check_record l1 l2 && (check_record l2 l1))
    | _ -> false;;

(* canonicalize *)
let canonicalize_tau tau =
  (* Check if bt1 has conflict with bt2, see Deinifition 1.6 Rule 6 for specification *)
  let rec conflict (bt1:bt) (bt2:bt) =
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
     | (LRecord r1, LRecord r2) ->
       (let rec find_lab_in_r1 r1 l =
          match r1 with
          | (Lab lab1, t1)::tl -> if lab1 = l then t1 else find_lab_in_r1 tl l
          | _ -> LStar
        in let rec iterate_r2 r2 =
             match r2 with
             | (Lab lab2, t2)::tl -> if (conflict t2 (find_lab_in_r1 r1 lab2)) then true else iterate_r2 tl
             | _ -> false
        in iterate_r2 r2)
     | (LRecord r1, _ ) -> true)

  in let canonicalize_t (t:t) =
    (let is_empty_t bt neg =
        (match (bt, neg) with
         | (LEmpty, _ ) -> true
         | _ -> false)
      (* Check if tb is subtype of any element in neg *)
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
                  | neg2::ttll -> if ((is_subtype_bt neg1 neg2) && (not (equals_bt neg1 neg2)|| (num1 < num))) then true else is_subtype_any_neg ttll (num1+1)
                  | _ -> false)
             in if (conflict neg1 bt) || (is_subtype_any_neg all_neg 1) then reform_neg tl bt all_neg (num+1) else neg1::(reform_neg tl bt all_neg (num+1))
           | _ -> []
      in match t with
      | T (bt, neg) -> if ((tb_is_subtype_neg bt neg) || (is_empty_t bt neg)) then T (LEmpty, []) else T (bt, reform_neg neg bt neg 1))

  in let rec iterate_tau tau =
    match tau with
      | (t, nc)::tl -> (canonicalize_t t, nc)::(iterate_tau tl)
      | _ -> []
  in let rec remove_empty_tags tags =
       match tags with
       | (T (LEmpty, []), nc)::tl -> remove_empty_tags tl
       | hd::tl -> hd::(remove_empty_tags tl)
       | _ -> []
  in let rec remove_duplicate_star tau has_star=
       match tau with
       | (T (LStar, []), nc)::tl -> if has_star then (remove_duplicate_star tl true) else (T (LStar, []), nc)::(remove_duplicate_star tl true)
       | hd::tl -> hd::(remove_duplicate_star tl has_star)
       | _ -> []
  in remove_duplicate_star (remove_empty_tags (iterate_tau tau)) false;;

(* Intersection of two tags, see Definition 1.8 for specification *)
let intersect_t t1 t2 =
  let rec intersect_bt (bt1:bt) (bt2:bt) =
    (match (bt1, bt2) with
    | (LStar, bt) -> bt
    | (bt, LStar) -> bt
    | (LInt, LInt) -> LInt
    | (LTrue, LTrue) -> LTrue
    | (LFalse, LFalse) -> LFalse
    | (LFun, LFun) -> LFun
    | (LRecord lr1, LRecord lr2) ->
      (* intersect the common fields in record 1 and 2 *)
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
    | _ -> LEmpty)
  in match (t1, t2) with
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
        | (p, e)::tl -> (T (pToBt p, get_neg all_pa num), Nonce (get_fresh_nonce 0))::(iterate_pattern tl all_pa (num+1))
        | _ -> [])
  in iterate_pattern pa pa 1;;

(* The record nonces that has already been projected.
   It is used to indicate whether we should continue to project a tag in backward propagation *)
let projected_record_nonces = ref [];;

(* Extract the tag for each field for record r with tag t, see Definition 3.1 for specification
   Returns: [(x1, tag1); (x2, tag2)...], where x1, x2, ... are the fields *)
let extract_fields r tau =
  (* If the field does not exist in the positive part of T, then we return LStar.
     If the field does not exist in the negative part of T, we return LEmpty *)
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
  in let rec iterate_tau l tau =
    (match tau with
      | (T (bt, neg), Nonce nonce )::tl -> projected_record_nonces := nonce :: (!projected_record_nonces);
                                      (T (proj_field bt l false, iterate_neg_t neg l), Nonce (get_fresh_nonce 0))::(iterate_tau l tl)
      | _ -> [])
  in let rec iterate_record r tau =
    (match r with
      | (Lab l, Ident x1)::tl -> (x1, canonicalize_tau (iterate_tau l tau))::(iterate_record tl tau)
      | _ -> [])
  in iterate_record r tau;;

(* Check whether a tag tau for x has already existed in the all_tags
   NOTICE: I'm lazy checking the equality of 2 taus -- since they are
   propagated using dataflow, if 2 taus are the same, then if any Nonce nc1
   matches any nonce nc2 in tau2, then the 2 taus should be the same *)
let rec exists_tag all_tags x tau =
  match all_tags with
  | (Ident x1, tau1)::tl ->
    let equals_t tau1 tau2 =
      (let rec iterate_tau nc1 tau2 =
         match tau2 with
         | (tb2, Nonce nc2)::tl -> if nc1 = nc2 then true else iterate_tau nc1 tl
         | _ -> false
       in match tau1 with
       | (tb1, Nonce nc1)::tl -> iterate_tau nc1 tau2
       | _ -> false)
    in if (x=x1) && (equals_t tau tau1) then true else exists_tag tl x tau
  | _ -> false;;

(* Check whether a tag tau has been projected before.
   NOTICE: I'm doing lazy checking here: if any nonce in the tag tau has been
   projected before, then all t's inside tau should already been projected before. *)
let has_projected tau projected_nonces=
  let rec iterate_nonces n projected_nonces =
    match projected_nonces with
    | n1::tl -> if n1 = n then true else iterate_nonces n tl
    | _ -> false
  in match tau with
  | (t, Nonce nc)::tl -> iterate_nonces nc projected_nonces
  | _ -> false;;

(* Propagation *)

(* Backward propagation *)
let backward_propagate_wrapper all_df tags record_var =
  let rec is_record x1 record_var =
    match record_var with
    | (Ident x2)::tl -> if x1 = x2 then true else is_record x1 tl
    | _ -> false
  (* backward propagate x with type t using dataflow df
     propagates under 2 condition:
      1. dataflow
      2. record projection *)
  in let rec backward_propagate df x t =
    (match df with
      | (Ident x1, Var (Ident x2))::tl -> if x1 = x && not (exists_tag tags x2 t)then (backward_propagate all_df x2 t)@(backward_propagate tl x t) else backward_propagate tl x t
      | (Ident x1, Closure(Record r, env))::tl ->
        (* Only continues to propagate if the variable is assigned a record in the program and the tag has not been projected before *)
        (if x1 = x && is_record x1 record_var && not (has_projected t (!projected_record_nonces)) then
           (let rec propagate_all all_fields =
              (match all_fields with
               | (xx, tt)::tl -> (backward_propagate all_df xx tt)@(propagate_all tl)
               | _ -> [])
           in propagate_all (extract_fields r t))
         else []) @(backward_propagate tl x t)
      | hd::tl -> backward_propagate tl x t
      | _ ->if (exists_tag tags x t) then [] else [(Ident x, t)])
  in let rec iterate_tags tags =
       match tags with
       | (Ident x, t)::tl -> (backward_propagate all_df x t)@(iterate_tags tl)
       | _ -> []
  in iterate_tags tags;;

(* Forward propagation  *)
let forward_propagate_wrapper all_df tags =
  (* forward propagate x with type t using dataflow df
     propagates under only 1 condition:
      1. dataflow *)
  let rec forward_propagate x t df =
     match df with
     | (Ident x1, Var (Ident x2))::tl -> if x2 = x && not (exists_tag tags x1 t)then (forward_propagate x1 t all_df)@(forward_propagate x t tl) else forward_propagate x t tl
     | hd::tl -> forward_propagate x t tl
     | _ -> if (exists_tag tags x t) then [] else [(Ident x, t)]
   in let rec iterate_tags tags =
        match tags with
        | (Ident x, t)::tl -> (forward_propagate x t all_df)@(iterate_tags tl)
        | _ -> []
 in iterate_tags tags;;

(* Reform all the tags, transform cnf to dnf
   Currently, assign *-[] for all variables that does not have tags *)
let old_nonce_to_new_tag_map = ref [];;

let rec reform_tag tags (program:expr) =
  let add_to_mapping old_tags (new_tags:(t*nonce) list) =
    let rec add_all_tau_nonces tau new_tags=
      (match tau with
       | (t, Nonce nc)::tl -> (nc, new_tags)::(add_all_tau_nonces tl new_tags)
       | _ -> [])
    in let rec iterate_disjuncts tags =
         (match tags with
          | tau::tl -> (add_all_tau_nonces tau new_tags) @ (iterate_disjuncts tl)
          | _ -> [])
    in old_nonce_to_new_tag_map := (iterate_disjuncts old_tags) @ (!old_nonce_to_new_tag_map)
  in let cnf_to_dnf tags =
    (let already_exists_tags tags =
       let rec iterate_map nc (map: (int*((t*nonce) list)) list) =
         (match map with
          | (nc1, tag)::tl -> if nc1 = nc then (true, tag) else iterate_map nc tl
          | _ -> (false, []))
       in (match tags with
         | ((t, Nonce nc)::tl)::ttll -> iterate_map nc (!old_nonce_to_new_tag_map)
         | _ -> (false, []))
    (* Product of all tags *)
    in let rec iterate_tau tau cur rst_tags=
      match tau with
        | (t, nc)::tl -> (iterate_tags (intersect_t cur t) rst_tags)@(iterate_tau tl cur rst_tags)
        | _ ->[]
    and iterate_tags cur tags =
      match tags with
      | tau1::tl -> iterate_tau tau1 cur tl
      | _ -> [(cur, Nonce (get_fresh_nonce 0))]
    in let (already_exist, res)= already_exists_tags tags
    in if already_exist then res else
    match tags with
      | [] -> [(T (LStar, []), Nonce (get_fresh_nonce 0))]
      | _ -> (let new_tag = canonicalize_tau (iterate_tags (T (LStar, [])) tags) in add_to_mapping tags new_tag; new_tag))
  in let rec get_all_vars program =
    match program with
    | Clause (Ident x, Function (Ident x1, e))::tl -> [x]@(get_all_vars tl)@(get_all_vars e)
    | Clause (Ident x, Match (Ident x1, pa))::tl ->
      let rec iterate_pa pa =
        match pa with
        | (p, e)::tl -> (get_all_vars e)@(iterate_pa tl)
        | _ -> []
      in x::((iterate_pa pa)@(get_all_vars tl))
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


(* todo:
    1. change remove duplicate star
    2. Example for record intersection *)
let rec type_inference (program: expr) =
  fresh_nonce := 0; projected_record_nonces := []; old_nonce_to_new_tag_map:= [];
  let _ = eval program in let all_df = !global_env
  in let rec get_match_tags x (program: expr) =
    match program with
    | Clause (Ident xx, Match (Ident x1, pa))::tl ->
      if xx=x then [(Ident x1, canonicalize_tau (pToTau pa))]
      else (let rec iterate_patterns pa =
              (match pa with
               | (p, e)::ttll -> (get_match_tags x e)@(iterate_patterns ttll)
               | _ -> [])
            in match (iterate_patterns pa) with
            | [] -> get_match_tags x tl
            | t -> t)
    | Clause (Ident xx, Function (Ident x1, e))::tl ->
      if xx = x then [] else
        (match (get_match_tags x e) with
         | [] -> get_match_tags x tl
         | t -> t)
    | Clause (Ident xx, body)::tl -> if xx = x then [] else get_match_tags x tl
    | _ -> []
  in let rec get_record_var (program:expr) =
    match program with
    | Clause (Ident x, Record r)::tl -> (Ident x)::(get_record_var tl)
    | Clause (Ident x, Function (x1,e))::tl -> (get_record_var e)@(get_record_var tl)
    | Clause (Ident x, Match (x1, pa))::tl ->
      let rec iterate_pattern pa =
        match pa with
        | (p,e)::ttll -> (get_record_var e)@(iterate_pattern ttll)
        | _ -> []
      in (iterate_pattern pa)@(get_record_var tl)
    | Clause (Ident x, _)::tl -> get_record_var tl
    | _ -> []
  in let rec get_all_match df =
       match df with
       | (Ident x, Var (Ident x2))::tl -> (get_match_tags x program)@(get_all_match tl)
       | hd::tl -> get_all_match tl
       | _ -> []
  in let rec iterate_backward_forward tags record_var =
       (let backward = backward_propagate_wrapper all_df tags record_var
        in let forward = forward_propagate_wrapper all_df (tags@backward)
        in match (forward@backward) with
        | [] -> tags
        | _ -> iterate_backward_forward (tags@forward@backward) record_var)
in reform_tag (iterate_backward_forward (get_all_match all_df) (get_record_var program)) program;;
(* in (iterate_backward_forward (get_all_match all_df) (get_record_var program));; *)

(*
  x0 = 1
  x1 = x0;
  x2 = 2;
  x3 = {a:x1, b:x2}
  x4 = 3
  x5 = {c:x3, d: x4}
  x6 = Match x5 with
    | {c:{a:PInt, b:PTrue}} -> x7=7
    | PStar -> x8 = 8

expected res :
x0 : (int-[]) U ( *-[int])
x1 : (int-[]) U ( *-[int])
x2 : (true-[]) U ( *-[true])
x3 : ({a:int;b:true}-[]) U (/* - [{a:int; b:true}])
x4 : (/* - [])
x5 : ({c:{a:int; b:true}} - []) U (/* - [{c:{a:int; b:true}}])
x6 : *-[]
x7 : *-[]
x8 : *-[]
*)

let in1 = [ Clause (Ident "x0", Int 1);
            Clause (Ident "x1", Var (Ident "x0"));
           Clause (Ident "x2", Int 2);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Int 3);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PTrue)])], [Clause (Ident "x7", Int 7)]);
                                                   (PStar, [Clause (Ident "x8", Int 8)])]))];;
let res = type_inference in1;;

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

res:
x1 : (int - []) U (/*-[int])
x2 : (true - []) U (/* - [true])
x3 : ({a:int; b:true} - []) U ({b:true} - [{a:int}]) U ({a:int}-[{b:true}]) U (/* - {a:int; b:true})
x10 : ({a:int; b:true} - []) U ({b:true} - [{a:int}]) U ({a:int}-[{b:true}]) U (/* - {a:int; b:true})
Nonce of x3 and x10 should be the same. 
 *)
let in2 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt)],[Clause (Ident "x5", Int 2)]);(PStar,[Clause (Ident "x6", Int 3)])]));
           Clause (Ident "x7", Match (Ident "x3", [(PRecord [(Lab "b", PTrue)],[Clause (Ident "x8", Int 4)]);(PStar,[Clause (Ident "x9", Int 5)])]));
           Clause (Ident "x10", Var (Ident "x3"))];;
let res2 = type_inference in2;;
!old_nonce_to_new_tag_map;;

(*
x1 = 1
x2 = {a:x1}
x3 = match x2 with
      | {a:int} -> x4 = 2
      | * -> x5 = 3
x6 = match x2 with
      | {a:int} -> x7 = 4
      | * -> x8 = 5

res:
x1: (int-[]) U (/*-[int])
x2: ({a:int}-[]) U (/* - [{a:int}])
*)
let in3 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Record [(Lab "a", Ident "x1")]);
           Clause (Ident "x3", Match (Ident "x2", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x4", Int 2)]);
                                                   (PStar, [Clause (Ident "x5", Int 3)])]));
           Clause (Ident "x6", Match (Ident "x2", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x7", Int 4)]);
                                                   (PStar, [Clause (Ident "x8", Int 5)])]))];;
let res3 = type_inference in3;;

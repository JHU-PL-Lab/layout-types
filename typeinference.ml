open Layout;;
open Setinterpreter;;
open Helper;;

exception TypeInferenceException;;
exception UnionFindException;;

(* Type inference *)
(* Gives a fresh nonce every time when called, e can be anything *)
let fresh_nonce = ref 0;;
let get_fresh_nonce _ = fresh_nonce := !fresh_nonce+1; let nonce = !fresh_nonce in nonce;;

(* Canonicalize
   See commit 31a09f, Definition 1.6
   Modified: If a field is bottom in a record, then the record should be bottom *)
let canonicalize_tau tau =
  (* Check if bt1 has conflict with bt2, see Deinifition 1.6 Rule 6 for specification *)
    let canonicalize_t (t:t) =
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
        in let rec has_empty_field lr =
             match lr with
             | LRecord ((Lab _, LEmpty)::_) -> true
             | LRecord (_::tl) -> has_empty_field (LRecord tl)
             | _ -> false
      in match t with
      | T (bt, neg) -> if ((tb_is_subtype_neg bt neg) || (is_empty_t bt neg) || (has_empty_field bt)) then T (LEmpty, []) else T (bt, reform_neg neg bt neg 1))

  in let rec iterate_tau tau =
    match tau with
      | (t, nc)::tl -> (canonicalize_t t, nc)::(iterate_tau tl)
      | _ -> []
  in let rec remove_empty_tags tags =
       match tags with
       | (T (LEmpty, []), _)::tl -> remove_empty_tags tl
       | hd::tl -> hd::(remove_empty_tags tl)
       | _ -> []
  in remove_empty_tags (iterate_tau tau);;

(* Intersection of two tags
   See commit 31a09f Definition 1.8 for specification *)
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

(* Transform match matterns to union of tags
   See commit 31a09f, Definiton 3.2, rule 1*)
let pToTau patterns =
  (* Get the negative part of the transformed tag, num is the number of patterns that should be in the negative part *)
  let rec get_neg patterns num = if num = 1 then [] else
         (match patterns with
          | (p, _)::tl -> (pattern_to_bt p)::(get_neg tl (num-1))
          | _ -> raise TypeInferenceException)
      (* Iterate through the patterns, match_ind is the index of the first matching pattern *)
  in let rec iterate_pattern pa all_patterns match_ind =
       (match pa with
        | (p, _)::tl -> (T (pattern_to_bt p, get_neg all_patterns match_ind), Nonce (get_fresh_nonce 0))::(iterate_pattern tl all_patterns (match_ind+1))
        | _ -> [])
  in iterate_pattern patterns patterns 1;;

(* The record nonces that has already been projected.
   It is used to indicate whether we should continue to project a tag in backward propagation *)
let projected_record_nonces = ref [];;

(* Extract the tag for each field for record r with tag tau.
   See commit 529bb7, Definition 3.1 for specification
   Returns: [(x1, tag1); (x2, tag2)...], where x1, x2, ... are the fields *)
let extract_fields r tau =
  let rec find_field_t lr lab =
    match lr with
    | (Lab l, bt)::tl -> if l = lab then bt else find_field_t tl lab
    | _ -> LStar
  in let proj_field bt l=
      (match bt with
       | LStar -> LStar
       | LRecord lr -> find_field_t lr l
       | _ -> LEmpty)
  in let rec project_neg neg l =
       (match neg with
        | bt::tl -> (proj_field bt l)::(project_neg tl l)
        | _ -> [])
  in let rec iterate_tau l tau=
    (match tau with
      | (T (bt, neg), Nonce nonce )::tl -> projected_record_nonces := nonce :: (!projected_record_nonces);
        (T (proj_field bt l, project_neg neg l), Nonce (get_fresh_nonce 0))::(iterate_tau l tl)
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
         | (_, Nonce nc2)::tl -> if nc1 = nc2 then true else iterate_tau nc1 tl
         | _ -> false
       in match tau1 with
       | (_, Nonce nc1)::_ -> iterate_tau nc1 tau2
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
  | (_, Nonce nc)::_ -> iterate_nonces nc projected_nonces
  | _ -> false;;

(* Propagation *)

(* Backward propagation
   See commit 31a09f, Definition 3.5*)
let backward_propagate_wrapper all_df tags record_var =
  let rec find_record x record_var =
       match record_var with
       | (Ident x1, r)::tl -> if x = x1 then r else find_record x tl
       | _ -> []
  (* backward propagate x with type t using dataflow df
     propagates under 2 condition:
      1. dataflow
      2. record projection *)
  in let rec backward_propagate df x t =
    (match df with
      | (Ident x1, Var (Ident x2))::tl -> if x1 = x && not (exists_tag tags x2 t)then (backward_propagate all_df x2 t)@(backward_propagate tl x t) else backward_propagate tl x t
      | _::_ -> raise WrongFormatOfDataFlow
      | _ ->if (exists_tag tags x t) then [] else [(Ident x, t)])
  in let rec propagate_all_fields all_fields =
       (match all_fields with
        | (xx, tt)::tl -> (backward_propagate all_df xx tt)@(propagate_all_fields tl)
        | _ -> [])
  in let rec iterate_tags tags =
       match tags with
       (* Only continues to propagate if the variable is assigned a record in the program and the tag has not been projected before *)
       | (Ident x, t)::tl ->
         (if not (has_projected t (!projected_record_nonces))
          then propagate_all_fields (extract_fields (find_record x record_var) t)else [])
         @(backward_propagate all_df x t)@(iterate_tags tl)
       | _ -> []
  in iterate_tags tags;;

(* Forward propagation
   See commit 31a09f, Definition 3.5*)
let forward_propagate_wrapper all_df tags =
  (* forward propagate x with type t using dataflow df
     propagates under only 1 condition:
      1. dataflow *)
  let rec forward_propagate x t df =
     match df with
     | (Ident x1, Var (Ident x2))::tl -> if x2 = x && not (exists_tag tags x1 t)then (forward_propagate x1 t all_df)@(forward_propagate x t tl) else forward_propagate x t tl
     | _::_ -> raise WrongFormatOfDataFlow
     | _ -> if (exists_tag tags x t) then [] else [(Ident x, t)]
   in let rec iterate_tags tags =
        match tags with
        | (Ident x, t)::tl -> (forward_propagate x t all_df)@(iterate_tags tl)
        | _ -> []
   in iterate_tags tags;;

(* Union Find, used to find sets of equal variables *)
let rec get_union_find_val ls x =
     match ls with
     | (x1, v1)::tl -> if x1 = x then v1 else get_union_find_val tl x
     | _ -> raise UnionFindException;;

let union_find all_df all_vars =
  let rec construct_list vars =
    match vars with
    | x::tl -> (x, x)::(construct_list tl)
    | _ -> []
  in let union ls x1 x2 = (
      let v1 = get_union_find_val ls x1
      in let v2 = get_union_find_val ls x2
      (* Change all entries in the list ls with value v1 to value v2 *)
      in let rec populate ls v1 v2 =
           match ls with
           | (x, v)::tl -> (if v = v1 then (x,v2) else (x, v))::(populate tl v1 v2)
           | _ -> []
      in populate ls v1 v2
    )
  in let rec iterate_df df ls =
       match df with
       | (Ident x1, Var (Ident x2))::tl -> iterate_df tl (union ls x1 x2)
       | _ -> ls
  in iterate_df all_df (construct_list all_vars)

(* The tags that have been assigned to some variable.
   In the form of [(x1,tau1);(x2, tau2);...] *)
let assigned_tags = ref [];;

(* Reform all the tags, transform cnf to dnf
   Assign *-[] for all variables that does not have tags
   See commit 31a09f, Lemma 3.8 *)
let reform_tag tags (program:expr) all_df =
  let rec already_exists x assigned_tags union_find_list =
    match assigned_tags with
    | (x1, t1)::tl -> if (get_union_find_val union_find_list x) = (get_union_find_val union_find_list x1) then (true ,t1) else already_exists x tl union_find_list
    | _ -> (false, [])
  in let cnf_to_dnf tags =
    (* Product of all tags *)
    let rec iterate_tau tau cur rst_tags=
      match tau with
        | (t, _)::tl -> (iterate_tags (intersect_t cur t) rst_tags)@(iterate_tau tl cur rst_tags)
        | _ ->[]
    and iterate_tags cur tags =
      match tags with
      | tau1::tl -> iterate_tau tau1 cur tl
      | _ -> [(cur, Nonce (get_fresh_nonce 0))]
    in match tags with
      | [] -> [(T (LStar, []), Nonce (get_fresh_nonce 0))]
      | _ -> canonicalize_tau (iterate_tags (T (LStar, [])) tags)
  in let rec get_all_vars program =
    match program with
    | Clause (Ident x, Function (Ident x1, e))::tl -> [x;x1]@(get_all_vars tl)@(get_all_vars e)
    | Clause (Ident x, Match (Ident _, pa))::tl ->
      let rec iterate_pa pa =
        match pa with
        | (_, e)::tl -> (get_all_vars e)@(iterate_pa tl)
        | _ -> []
      in x::((iterate_pa pa)@(get_all_vars tl))
    | Clause (Ident x, _ )::tl -> x::get_all_vars tl
    | _ -> []
  in let rec find_tag x tags =
       match tags with
       | (Ident x1, t)::tl -> if x1 = x then t::(find_tag x tl) else find_tag x tl
       | _ -> []
  in let rec iterate_all_vars vars union_find_list =
       match vars with
       | x::tl ->
         let already_exist, res = already_exists x (!assigned_tags) union_find_list
         in let t = if already_exist then res else cnf_to_dnf (find_tag x tags)
         in assigned_tags := (x, t)::(!assigned_tags); (Ident x, t)::(iterate_all_vars tl union_find_list)
       | _ -> []
  in let all_vars = get_all_vars program
  in let union_find_list = union_find all_df all_vars
  in iterate_all_vars all_vars union_find_list;;

(* Type Inference
   See commit 31a09f, Definition 3.5 *)
let type_inference (program: expr) =
  fresh_nonce := 0; projected_record_nonces := [];assigned_tags := [];
  let _,all_df = eval program
  in let rec get_match_tags x (program: expr) =
    match program with
    | Clause (Ident xx, Match (Ident x1, pa))::tl ->
      if xx=x then [(Ident x1, canonicalize_tau (pToTau pa))]
      else (let rec iterate_patterns pa =
              (match pa with
               | (_, e)::ttll -> (get_match_tags x e)@(iterate_patterns ttll)
               | _ -> [])
            in match (iterate_patterns pa) with
            | [] -> get_match_tags x tl
            | t -> t)
    | Clause (Ident xx, Function (Ident _, e))::tl ->
      if xx = x then [] else
        (match (get_match_tags x e) with
         | [] -> get_match_tags x tl
         | t -> t)
    | Clause (Ident xx, _)::tl -> if xx = x then [] else get_match_tags x tl
    | _ -> []
  in let rec get_record_var (program:expr) =
    match program with
    | Clause (Ident x, Record r)::tl -> (Ident x, r)::(get_record_var tl)
    | Clause (Ident _, Function (_,e))::tl -> (get_record_var e)@(get_record_var tl)
    | Clause (Ident _, Match (_, pa))::tl ->
      let rec iterate_pattern pa =
        match pa with
        | (_,e)::ttll -> (get_record_var e)@(iterate_pattern ttll)
        | _ -> []
      in (iterate_pattern pa)@(get_record_var tl)
    | Clause _::tl -> get_record_var tl
    | _ -> []
  in let rec get_all_match df =
       match df with
       | (Ident x, Var (Ident _))::tl -> (get_match_tags x program)@(get_all_match tl)
       | _::_ -> raise WrongFormatOfDataFlow
       | _ -> []
  in let rec iterate_backward_forward tags record_var =
       (let backward = backward_propagate_wrapper !all_df tags record_var
        in let forward = forward_propagate_wrapper !all_df (tags@backward)
        in match (forward@backward) with
        | [] -> tags
        | _ -> iterate_backward_forward (tags@forward@backward) record_var)
  in reform_tag (iterate_backward_forward (get_all_match (!all_df)) (get_record_var program)) program !all_df;;

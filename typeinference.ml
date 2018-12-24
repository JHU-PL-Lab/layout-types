open Layout;;
open Setinterpreter;;
open Typechecker;;
open Helper;;

exception TypeInferenceException;;
exception UnionFindException;;

(* Type inference *)
(* Gives a fresh nonce every time when called, e can be anything *)
let fresh_nonce = ref 0;;
let get_fresh_nonce e = fresh_nonce := !fresh_nonce+1; let nonce = !fresh_nonce in nonce;;

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
             | LRecord ((Lab lab, LEmpty)::tl) -> true
             | LRecord (hd::tl) -> has_empty_field (LRecord tl)
             | _ -> false
      in match t with
      | T (bt, neg) -> if ((tb_is_subtype_neg bt neg) || (is_empty_t bt neg) || (has_empty_field bt)) then T (LEmpty, []) else T (bt, reform_neg neg bt neg 1))

  in let rec iterate_tau tau =
    match tau with
      | (t, nc)::tl -> (canonicalize_t t, nc)::(iterate_tau tl)
      | _ -> []
  in let rec remove_empty_tags tags =
       match tags with
       | (T (LEmpty, []), nc)::tl -> remove_empty_tags tl
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
          | (p, e)::tl -> (pattern_to_bt p)::(get_neg tl (num-1))
          | _ -> raise TypeInferenceException)
      (* Iterate through the patterns, match_ind is the index of the first matching pattern *)
  in let rec iterate_pattern pa all_patterns match_ind =
       (match pa with
        | (p, e)::tl -> (T (pattern_to_bt p, get_neg all_patterns match_ind), Nonce (get_fresh_nonce 0))::(iterate_pattern tl all_patterns (match_ind+1))
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
      | hd::tl -> raise WrongFormatOfDataFlow
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
     | hd::tl -> raise WrongFormatOfDataFlow
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
let rec reform_tag tags (program:expr) all_df =
  let rec already_exists x assigned_tags union_find_list =
    match assigned_tags with
    | (x1, t1)::tl -> if (get_union_find_val union_find_list x) = (get_union_find_val union_find_list x1) then (true ,t1) else already_exists x tl union_find_list
    | _ -> (false, [])
  in let cnf_to_dnf tags =
    (* Product of all tags *)
    let rec iterate_tau tau cur rst_tags=
      match tau with
        | (t, nc)::tl -> (iterate_tags (intersect_t cur t) rst_tags)@(iterate_tau tl cur rst_tags)
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
let rec type_inference (program: expr) =
  fresh_nonce := 0; projected_record_nonces := [];assigned_tags := [];
  let _,all_df = eval program
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
    | Clause (Ident x, Record r)::tl -> (Ident x, r)::(get_record_var tl)
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
       | (Ident x, Var (Ident x2))::tl -> Printf.printf "%s\n" x;(get_match_tags x program)@(get_all_match tl)
       | hd::tl -> raise WrongFormatOfDataFlow
       | _ -> []
  in let rec iterate_backward_forward tags record_var =
       (let backward = backward_propagate_wrapper !all_df tags record_var
        in let forward = forward_propagate_wrapper !all_df (tags@backward)
        in match (forward@backward) with
        | [] -> tags
        | _ -> iterate_backward_forward (tags@forward@backward) record_var)
  in reform_tag (iterate_backward_forward (get_all_match (!all_df)) (get_record_var program)) program !all_df;;

(*
  x0 = 1
  x1 = x0;
  x2 = true;
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
x5 : ({c:{a:int; b:true}} - []) U (/* - [{c:{a:int; b:true}}])
*)

let in1 = [ Clause (Ident "x0", Int 1);
            Clause (Ident "x1", Var (Ident "x0"));
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Int 3);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PTrue)])], [Clause (Ident "x7", Int 7)]);
                                                   (PStar, [Clause (Ident "x8", Int 8)])]))];;
let res1 = type_inference in1;;
let (sound1, rou1, delta1) = typecheck (tag_program in1 res1);;
(* Test whether x10 and x3 have same nonce
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
let (sound2, rou2, delta2) = typecheck (tag_program in2 res2);;

(* Test intersection of same tags
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
let (sound3, rou3, delta3) = typecheck (tag_program in3 res3);;

(*
Simplified Master Example part 1.
(Since current version doesn't support UNK, I'm using 2 separate match to simulate it. )
Problem with duplicate

x1 = {}
x2 = 3
x3 = {c:x1; d:x2}
x4 = match x3 with
      | {d:int} -> x5 = 1
      | {c:int; d:* } -> x6 = 2
      | {d:*} -> x7 = 3
      | {e:*} -> x8 = 4
      | {a:*} -> x9 = 5
      | int -> x10 = 6
      | * -> x11 = 7
x12 = match x3 with
      | {q: *} -> x13 = 8
      | * -> x14 = 9

res:
x1: * U (int - [])
x2: (int - []) U (/* - [int])
x3: ({d:int; q:*} - []) U ({d:int} - [{q:*}])
    U ({c:int; d:*; q:*} - [{d:int}]) U ({c:int; d:*} - [{d:int}; {q:*}])
    U ({d:*; q:*} - [{d:int}; {c:int; d:*}]) U ({d:*} - [{d:int}; {c:int; d:*};{q:*}])
    U ({e:*; q:*} - [{d:*}]) U ({e:*} - [{d:*}; {q:*}])
    U ({a:*; q:*} - [{d:*}; {e:*}]) U ({a:*} - [{d:*}; {e:*}; {q:*})
    U (int - [])
    U ({q:*} - [{d:*}; {e:*}; {a:*}]) U (/* - [{d:*}; {e:*}; {a:*}; int; {q:*}])
 *)

let in4 = [Clause (Ident "x1", Record []);
           Clause (Ident "x2", Int 3);
           Clause (Ident "x3", Record [(Lab "c", Ident "x1");(Lab "d", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3",
                                      [(PRecord [(Lab "d", PInt)], [Clause (Ident "x5", Int 1)]);
                                       (PRecord [(Lab "c", PInt); (Lab "d", PStar)], [Clause (Ident "x6", Int 2)]);
                                       (PRecord [(Lab "d", PStar)], [Clause (Ident "x7", Int 3)]);
                                       (PRecord [(Lab "e", PStar)], [Clause (Ident "x8", Int 4)]);
                                       (PRecord [(Lab "a", PStar)], [Clause (Ident "x9", Int 5)]);
                                       (PInt, [Clause (Ident "x10", Int 6)]);
                                       (PStar, [Clause (Ident "x11", Int 7)])]));
           Clause (Ident "12", Match (Ident "x3",
                                      [(PRecord [(Lab "q", PStar)], [Clause (Ident "x13", Int 8)]);
                                       (PStar, [Clause (Ident "x14", Int 9)])]))];;
let res4 = type_inference in4;;
let (sound4, rou4, delta4) = typecheck (tag_program in4 res4);;

(* let rec get_ident res x =
  match res with
  | (Ident x1, tag)::tl -> if x = x1 then tag else get_ident tl x
  | _ ->[];;

get_ident res4 "x3";; *)

 (*

 x1 = {}
 x2 = 3
 x3 = {c:x1; d:x2}
 x4 = match x3 with
       | {c:int; d:* } -> x5 = 1
       | {d:*} -> x6 = 2
       | * -> x7 = 3

 res:
 x1: (int - []) U (/*-[int])
 x2: *
 x3: ({c:int;d:*} - []) U ({d:*} - [{c:int; d:*}]) U (/* - [{d:*}])
  *)

let in5 = [Clause (Ident "x1", Record []);
           Clause (Ident "x2", Int 3);
           Clause (Ident "x3", Record [(Lab "c", Ident "x1");(Lab "d", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "c", PInt); (Lab "d", PStar)],[Clause (Ident "x5", Int 1)]);
                                                   (PRecord [(Lab "d", PStar)], [Clause (Ident "x6", Int 2)]);
                                                   (PStar, [Clause (Ident "x7", Int 3)])]))];;
let res5 = type_inference in5;;
let (sound5, rou5, delta5) = typecheck (tag_program in5 res5);;

(* Test intersection of records
x1 = 1
x2 = true
x3 = {a:x1; b:x2}
x4 = false
x5 = {c: x3; d: x4}
x6 = match x5 with
    | {c: {}; d: true } -> x7 = 1
    | {c: {a:int}; d: false} -> x8 = 2
    | * -> x9 = 3
x10 = match x5 with
    | {c: {}; d: int } -> x11 = 4
    | {c: {b:true}; d: false} -> x12 = 5
    | * -> x13 = 6

res:
   x1: * U int
   x2: * U true
   x3: {} U {b:true} U {a:int; b:true} U {a:int} U *-{}
   x4: true U false U int U (/* - [true, false, int])
   x5: {c:{};d:true}
      U {c:{a:int; b:true}; d:false} U ({c:{a:int}; d:false} - {c:{b:true}; d:false})
      U {c:{}; d:int} U ({c:{b:true}; d:false} - {c:{a:int}; d:false}) U (/* - [{c:{a:int}; d:false}; {c:{};d:true}; {c:{}; d:int}; {c:{b:true}; d:false}])

 *)
let in6 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", False);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord []);(Lab "d", PTrue)],[Clause (Ident "x7", Int 1)]);
                                                   (PRecord [(Lab "c", PRecord [(Lab "a", PInt)]); (Lab "d", PFalse)],[Clause (Ident "x8", Int 2)]);
                                                   (PStar,[Clause (Ident "x9", Int 3)])]));
           Clause (Ident "x10", Match (Ident "x5", [(PRecord [(Lab "c", PRecord []); (Lab "d", PInt)],[Clause (Ident "x11", Int 4)]);
                                                    (PRecord [(Lab "c", PRecord [(Lab "b", PTrue)]); (Lab "d", PFalse)], [Clause (Ident "x12", Int 5)]);
                                                    (PStar, [Clause (Ident "x13", Int 6)])]))];;
let res6 = type_inference in6;;
let (sound6, rou6, delta6) = typecheck (tag_program in6 res6);;

(*
Simplified test 4.

x1 = {}
x2 = 3
x3 = {c:x1; d:x2}
x4 = match x3 with
      | {d:int} -> x5 = 1
      | {c:int; d:*} -> x6 = 2
      | {d:*} -> x7 = 3
      | * -> x8 = 4
x9 = match x3 with
      | {q: *} -> x10 = 5
      | * -> x11 = 6

res:
x1: * U (int - [])
x2: (int - []) U (/* - [int])
x3: ({d:int; q:*} - []) U ({d:int} - [{q:*}])
    U ({c:int; d:*; q:*} - [{d:int}]) U ({c:int; d:*} - [{d:int}; {q:*}])
    U ({d:*; q:*} - [{d:int}; {c:int; d:*}]) U ({d:*} - [{d:int}; {c:int; d:*};{q:*}])
    U ({q:*} - [{d:*}]) U (/* - [{d:*}; {q:*}])
 *)

let in7 = [Clause (Ident "x1", Record []);
           Clause (Ident "x2", Int 3);
           Clause (Ident "x3", Record [(Lab "c", Ident "x1");(Lab "d", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3",
                                      [(PRecord [(Lab "d", PInt)], [Clause (Ident "x5", Int 1)]);
                                       (PRecord [(Lab "c", PInt); (Lab "d", PStar)], [Clause (Ident "x6", Int 2)]);
                                       (PRecord [(Lab "d", PStar)], [Clause (Ident "x7", Int 3)]);
                                       (PStar, [Clause (Ident "x8", Int 7)])]));
           Clause (Ident "x9", Match (Ident "x3",
                                      [(PRecord [(Lab "q", PStar)], [Clause (Ident "x10", Int 8)]);
                                       (PStar, [Clause (Ident "x11", Int 9)])]))];;
let res7 = type_inference in7;;
let (sound7, rou7, delta7) = typecheck (tag_program in7 res7);;

(*
  Test subtyping inside atomic typing
  x1 = 1
  x2 = match x1 with
        | false -> x3 = 1
        | * -> x4 = 2
 *)

let in8 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Match (Ident "x1", [(PFalse, [Clause (Ident "x3", Int 1)]);
                                                   (PStar, [Clause (Ident "x4", Int 2)])]))];;
let res8 = type_inference in8;;
let (sound8, rou8, delta8) = typecheck (tag_program in8 res8);;


(* test AMB
   x1 = true or false
   x2 = match x1 with
        | true -> x3 = 1
        | false -> x4 = 2
        | * -> x5 = 3
*)

let in9 = [Clause (Ident "x1", Amb [True;False]);
           Clause (Ident "x2", Match (Ident "x1", [(PTrue, [Clause (Ident "x3", Int 1)]);
                                                   (PFalse, [Clause (Ident "x4", Int 2)]);
                                                   (PStar, [Clause (Ident "x5", Int 3)])]))];;
let res9 = type_inference in9;;
let (sound9, rou9, delta9) = typecheck (tag_program in9 res9);;

(* Test iteration of backward/forward
*)

(*
x1 = 1
x2 = 2
x3 = x1 + x2
x4 = match x3 with
      | int -> x5 = 1
      | * -> x6 = 2

res:
x3: int U *-int
*)
let in10 = [Clause (Ident "x1", Int 1);
            Clause (Ident "x2", Int 2);
            Clause (Ident "x3", Plus (Ident "x1", Ident "x2"));
            Clause (Ident "x4", Match (Ident "x3", [(PInt, [Clause (Ident "x5", Int 1)]);
                                                    (PStar, [Clause (Ident "x6", Int 2)])]))];;
let res10 = type_inference in10;;
let (sound10, rou10, delta10) = typecheck (tag_program in10 res10);;

(*
x1 = 1
x2 = 2
x3 = x1 + x2
x4 = match x3 with
      | true -> x5 = 1
      | * -> x6 = 2

res:
x3: true U *-true
should fail! needs implementation of operators propagation
*)

(*
x1 = True or False
x2 = match x1 with
      | True -> x3 = 1;
                x31 = match x3 with
                    | Int -> x32 = 1
                    | * -> x33 = 2
                x34 = x3
      | False -> x4 = True;
                 x41 = match x4 with
                    | True -> x42 = 3
                    | * -> x43 = 4
                 x44 = x4
      | * -> x5 = 5

res:
 *)
let in11 = [Clause (Ident "x1", Amb [True; False]);
            Clause (Ident "x2", Match (Ident "x1", [(PTrue, [Clause (Ident "x3", Int 1);
                                                             Clause (Ident "x31", Match (Ident "x3", [(PInt, [Clause (Ident "x32", Int 1)]);
                                                                                                      (PStar, [Clause (Ident "x33", Int 2)])]));
                                                             Clause (Ident "x34", Var (Ident "x3"))]);
                                                    (PFalse, [Clause (Ident "x4", True);
                                                              Clause (Ident "x41", Match (Ident "x4", [(PTrue, [Clause (Ident "x42", Int 3)]);
                                                                                                       (PStar, [Clause (Ident "x43", Int 4)])]));
                                                              Clause (Ident "x44", Var (Ident "x4"))]);
                                                    (PStar, [Clause (Ident "x5", Int 5)])]))];;
let res11 = type_inference in11;;
let (sound11, rou11, delta11) = typecheck (tag_program in11 res11);;

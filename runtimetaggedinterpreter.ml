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
          | Match of ident * (pattern * expr) list | TaggedClosure of body * tagged_env
and env = (ident * body) list
and tagged_env = (ident * (body * ind)) list
and clause = Clause of ident * tau * body
and expr = clause list
and pattern = PRecord of (label * pattern) list | PInt | PTrue | PFalse | PFun | PStar;;

exception BodyNotMatched;;
exception ClauseNotMatched;;
exception ForkFailed;;
exception CannotFindTau;;

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
  | Clause (Ident x, t, b)::[] -> x
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
  | Clause (Ident x,Tau t, b)::[] -> let res = eval_body b ev (Ident x) in (global_env := (Ident x, res) :: !global_env; match res with
    | OrVal o -> OrVal o
    | _ -> OrVal [res])
  | Clause (Ident x,Tau t, b)::tl ->
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

(* helper methods *)
let rec get_all_typedec expr =
  match expr with
  | Clause (Ident x, Tau tau, Function (Ident x1, e1))::tl -> (Ident x, Tau tau)::(get_all_typedec tl)@(get_all_typedec e1)
  | Clause (Ident x, Tau tau, Match (Ident x1, pattern))::tl ->
    (let rec iterate_pattern pattern =
       match pattern with
       |(p1, e1)::ttll -> (get_all_typedec e1)@(iterate_pattern ttll)
       | _ -> [] in (Ident x, Tau tau)::(iterate_pattern pattern)@(get_all_typedec tl))
  | Clause (Ident x, Tau tau, b)::tl -> (Ident x, Tau tau)::(get_all_typedec tl)
  | _ -> [];;

let rec find_tau typedec x =
  match typedec with
  | (Ident x1, Tau tau)::tl -> if x = x1 then tau else find_tau tl x
  | _ -> raise CannotFindTau;;

(* Atomic typed *)
(* should we include OrVals?
   should we include false/true for and/or/not? *)
let rec atomic_typed (program:expr) =
  match program with
  | Clause (Ident x, Tau tau, Int i)::tl ->
    (match tau with
     | [(T (LInt, []), Ind ind)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, True)::tl ->
    (match tau with
     | [(T (LTrue, []), Ind ind)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, False)::tl ->
    (match tau with
     | [(T (LFalse, []), Ind ind)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Function (x1, e1))::tl ->
    (match tau with
     | [(T (LFun, []), Ind ind)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Equals (x1, x2))::tl ->
    (match tau with
     | [(T (LTrue, []), Ind ind);(T (LFalse, []), Ind ind2)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Plus (x1, x2))::tl ->
    (match tau with
     | [(T (LInt, []), Ind ind)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Minus (x1, x2))::tl ->
    (match tau with
     | [(T (LInt, []), Ind ind)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, And (x1, x2))::tl ->
    (match tau with
     | [(T (LTrue, []), Ind ind);(T (LFalse, []), Ind ind2)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Or (x1, x2))::tl ->
    (match tau with
     | [(T (LTrue, []), Ind ind);(T (LFalse, []), Ind ind2)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Not x1)::tl ->
    (match tau with
     | [(T (LTrue, []), Ind ind);(T (LFalse, []), Ind ind2)] -> atomic_typed tl
     | _ -> false)
  | Clause (Ident x, Tau tau, Match (x1, patterns))::tl ->
    (let rec check_all_patterns patterns =
       match patterns with
       | (p1, e1)::ttll -> atomic_typed e1 && check_all_patterns ttll
       | _ -> true in check_all_patterns patterns && atomic_typed tl)
  | Clause (Ident x, Tau tau, b)::tl -> atomic_typed tl
  | _ -> true;;

(* Subtype soundness *)
let rec is_subtype_t (t1:t) (t2:t) =
  let rec is_subtype_bt (bt1:bt) (bt2:bt) =
    (match (bt1, bt2) with
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
     | _ -> false) in
  (match (t1, t2) with
   | (T (bt1, neg1), T (bt2, neg2)) ->
     let rec iterate_neg neg1 bt2 =
       match neg1 with
       | bt1::tl -> if is_subtype_bt bt2 bt1 then true else iterate_neg tl bt2
       | _ -> false
     in
     let rec check_neg neg1 neg2 =
       match neg2 with
       | bt2::tl -> if iterate_neg neg1 bt2 then check_neg neg1 tl else false
       | _ -> true
     in if is_subtype_bt bt1 bt2 then check_neg neg1 neg2 else false);;

(* whether t1 is subtype of t2, t1 and t2 are both tau type *)
let rec is_subtype tau1 tau2 =
  let rec iterate_tau2 t1 tau2 =
    match tau2 with
    | (t2, i2)::tl -> if (is_subtype_t t1 t2) then true else iterate_tau2 t1 tl
    | _ -> false
  in
  let rec iterate_tau1 tau1 tau2 =
    match tau1 with
    | (t1, i1)::tl -> if iterate_tau2 t1 tau2 then is_subtype tl tau2 else false
    | _ -> true
  in iterate_tau1 tau1 tau2;;

let rec sound_subtype typedec (df:env) =
  match df with
  | (Ident x1, Var(Ident x2))::tl -> if (is_subtype (find_tau typedec x2) (find_tau typedec x1)) then sound_subtype typedec tl else false
  | (Ident x1, b)::tl -> sound_subtype typedec tl
  | _ -> true;;

(* Record Soundness *)
let rec record_soundness typedec (program:expr) =
  let get_canonical_record_wrapper r =
    (let rec get_canonical_record r =
       match r with
       | (Lab lab, T (bt, neg))::tl ->
         let (r2, neg2) = get_canonical_record tl
         in let rec flattern_neg neg =
              match neg with
              | btn::ttll -> (LRecord [(Lab lab, btn)])::(flattern_neg ttll)
              | _ -> []
         in (( Lab lab, bt)::r2,(flattern_neg neg)@neg2)
       | _ -> ([],[])
     in let (bt, neg) = get_canonical_record r
     in T (LRecord bt, neg)) in
  let get_field_product r typedec =
    (let rec iterate_res lab t ind res =
       match res with
       | (record_list, nounce_list)::tl -> ((lab, t)::record_list,ind::nounce_list)::(iterate_res lab t ind tl)
       | _ -> []
     in let rec iterate_disjuncts lab disjuncts res =
          match disjuncts with
          | (t, ind)::tl -> (iterate_res lab t ind res) @ (iterate_disjuncts lab tl res)
          | _ -> []
     in let rec iterate_record r typedec =
          match r with
          | (lab, Ident x)::tl -> let res = iterate_record tl typedec in iterate_disjuncts lab (find_tau typedec x) res
          | _ -> [([],[])]
     in iterate_record r typedec) in
  let rec iterate_tau r1 tau =
    (match tau with
     | (t1, Ind ind)::tl -> if is_subtype_t r1 t1 then ind else iterate_tau r1 tl
     | _ -> -1) in
  (match program with
   | (Clause (Ident x, Tau tau, Record r))::tl ->
     let rec iterate_product product tau =
       match product with
       | (record, nounce_list)::tl ->let match_ind = iterate_tau (get_canonical_record_wrapper record) tau in
         if (match_ind = -1) then (false,[])
         else (let (matches, table) = iterate_product tl tau in
               if matches = true then (true, (nounce_list, match_ind) :: table) else (false, []))
       | _ ->(true, [])
     in let (matches_tl, rou_tl) = record_soundness typedec tl
     in let (matches_cur, table_cur) = iterate_product (get_field_product r typedec) tau
     in if matches_tl && matches_cur then (true, (Ident x, table_cur)::rou_tl) else (false, [])
   | hd::tl -> record_soundness typedec tl
   | _ -> (true, []));;

(* Pattern Complete *)
let rec tb_pattern_match bt pattern =
  match (bt, pattern) with
  | (LEmpty, _) -> true
  | (_, PStar) -> true
  | (LInt, PInt) -> true
  | (LFalse, PFalse) -> true
  | (LTrue, PTrue) -> true
  | (LFun, PFun) -> true
  | (LRecord lr, PRecord pr) ->
    let rec iterate_record lr labp pa =
      match lr with
      | (Lab labr, btr)::tl -> if labp = labr then tb_pattern_match btr pa else iterate_record tl labp pa
      | _ -> false
    in let rec iterate_pattern lr pr =
         match pr with
         | (Lab labp, pa)::tl -> if iterate_record lr labp pa then iterate_pattern lr tl else false
         | _ -> true
    in iterate_pattern lr pr
  | _ -> false;;

let rec tb_pattern_not_match bt pattern =
  match (bt, pattern) with
  | (_, PStar) -> false
  | (LStar, _) -> false
  | (LInt, p) ->
    (match p with
     | PInt -> false
     | _ -> true)
  | (LTrue, p) ->
    (match p with
     | PTrue -> false
     | _ -> true)
  | (LFalse, p) ->
    (match p with
     | PFalse -> false
     | _ -> true)
  | (LFun, p) ->
    (match p with
     | PFun -> false
     | _ -> true)
  | (LRecord lr, PRecord pr) ->
    let rec iterate_record lr labp pa=
      match lr with
      | (Lab labr, btr)::tl -> if labr = labp then tb_pattern_not_match btr pa else iterate_record tl labp pa
      | _ -> false
    in let rec iterate_pattern lr pr =
         match pr with
         | (Lab labp, pa)::tl -> if iterate_record lr labp pa then true else iterate_pattern lr tl
         | _ -> false
    in iterate_pattern lr pr
  | (LRecord lr, _) -> true
  | (LEmpty, _) -> false;;

let rec t_pattern_match bt neg pattern =
  let rec iterate_neg neg pattern =
    match neg with
    | nbt::tl -> if tb_pattern_not_match nbt pattern then iterate_neg tl pattern else false
    | _ -> true
  in tb_pattern_match bt pattern && iterate_neg neg pattern;;

let rec pattern_complete typedec (program:expr) =
  let rec pattern_cover tau patterns =
    (match tau with
     | (T (bt, neg), Ind i)::tl ->
       let rec iterate_patterns patterns pat_ind=
         match patterns with
         | (p,e)::ttll -> if t_pattern_match bt neg p then pat_ind else iterate_patterns ttll (pat_ind+1)
         | _ -> 0
       in let cur_match = iterate_patterns patterns 1
       in let (tail_match, delta) = pattern_cover tl patterns
       in if (cur_match != 0) && tail_match then (true, (Ind i, cur_match)::delta) else (false, [])
     | _ -> (true, [])) in
  (match program with
   | (Clause (Ident x1, Tau tau, Match (Ident x2, patterns)))::tl ->
     let (match_cur, table_cur) = pattern_cover (find_tau typedec x2) patterns
     in let (match_tail, delta_tail) = pattern_complete typedec tl
     in if match_cur && match_tail then (true, (Ident x1, table_cur) :: delta_tail) else (false, [])
   | hd::tl -> pattern_complete typedec tl
   | _ -> (true,[]));;

let get_matching_nounce typedec x tb =
  let rec iterate_tau tau tb =
    match tau with
    | (T (bt, []), Ind ind)::tl -> if bt=tb then ind::(iterate_tau tl tb) else iterate_tau tl tb
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
       | (T (LRecord lr, []), Ind ind)::tl -> if (exists_lab lr lab) then ind::(iterate_tau tl lab) else iterate_tau tl lab
       | hd::tl -> iterate_tau tl lab
       | _ -> []
  in iterate_tau (find_tau typedec x) lab;;

let rec get_runtime_success_dispatch_table (program:expr) typedec=
  match program with
  | Clause (Ident x, Tau tau, Plus (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LInt);(get_matching_nounce typedec x2 LInt)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Minus (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LInt);(get_matching_nounce typedec x2 LInt)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Not (Ident x1))::tl -> (Ident x, [(get_matching_nounce typedec x1 LTrue)@(get_matching_nounce typedec x1 LFalse)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, And (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LTrue)@(get_matching_nounce typedec x1 LFalse);(get_matching_nounce typedec x2 LTrue)@(get_matching_nounce typedec x2 LFalse)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Or (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LTrue)@(get_matching_nounce typedec x1 LFalse);(get_matching_nounce typedec x2 LTrue)@(get_matching_nounce typedec x2 LFalse)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Equals (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LInt);(get_matching_nounce typedec x2 LInt)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Appl (Ident x1, Ident x2))::tl -> (Ident x, [(get_matching_nounce typedec x1 LFun)])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Proj (Ident x1, Lab lab))::tl -> (Ident x, [get_projection_nounce typedec x1 lab])::(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Function (Ident x1, e))::tl -> (get_runtime_success_dispatch_table e typedec)@(get_runtime_success_dispatch_table tl typedec)
  | Clause (Ident x, Tau tau, Match (Ident x1, pe))::tl ->
    (let rec iterate_pattern_clause pe typedec=
       (match pe with
        | (p, e)::tl-> (get_runtime_success_dispatch_table e typedec)@(iterate_pattern_clause tl typedec)
        | _ -> [])
     in (iterate_pattern_clause pe typedec)@(get_runtime_success_dispatch_table tl typedec))
  | hd::tl -> get_runtime_success_dispatch_table tl typedec
  | _ -> [];;

(* typechecking, return true/false, rou and delta *)
let typecheck (program:expr) =
  let (_, global) = eval program in
  let typedec = get_all_typedec program in
  let (recordsound, rou) = (record_soundness typedec program) in
  let (patterncomplete, delta) = (pattern_complete typedec program) in
  ((atomic_typed program) && (sound_subtype typedec !global) && recordsound && patterncomplete,rou, delta);;


(* Runtime tagged interpreter *)

let rec find_tagged_var x envir =
  match envir with
  | (Ident x1, btag)::tl -> if x = x1 then btag else find_tagged_var x tl
  | _ -> (Empty, Ind (-1));;

let rec get_rou rou x =
  match rou with
  | (Ident xx, entry)::tl -> if x = xx then entry else get_rou tl x
  | _ -> [];;

let rec get_delta delta x =
  match delta with
  | (Ident xx, entry)::tl -> if x = xx then entry else get_delta tl x
  | _ ->[];;

let get_nounce_from_rou nlist rou =
  let rec match_entry nlist entry =
    match (nlist, entry) with
    | ([],[]) -> true
    | (ind1::tl1, (Ind ind2)::tl2) -> if ind1 = ind2 then match_entry tl1 tl2 else false
    | _ -> false
  in let rec iterate_rou nlist rou =
    match rou with
    | (entry, ind)::tl -> if match_entry nlist entry then Ind ind else iterate_rou nlist rou
    | _ -> Ind (-1)
  in iterate_rou nlist rou;;

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
          | [(T (LInt, []), Ind ind)]-> (Int n, Ind ind)
          | _ -> (Empty, Ind (-1)))
      | True -> (match tau with
          | [(T (LTrue, []), Ind ind)] -> (True, Ind ind)
          | _ -> (Empty, Ind (-1)))
      | False -> (match tau with
          | [(T (LFalse, []), Ind ind)] -> (False, Ind ind)
          | _ -> (Empty, Ind (-1)))
      | Var (Ident x) -> find_tagged_var x ev
      | Function (x1, e1) -> (match tau with
          | [(T (LFun, []), Ind ind)]-> (TaggedClosure (b, ev), Ind ind)
          | _ -> (Empty, Ind (-1)))
      | Record rc ->
        let rec get_record_field_nounce rc =
          match rc with
          | (lab, Ident x) :: tl ->
            (match find_tagged_var x ev with
             | (_ , Ind ind) -> ind)::get_record_field_nounce tl
          | _ -> []
        in (TaggedClosure (b, ev), get_nounce_from_rou (get_record_field_nounce rc) (get_rou rou flowto))
      | Plus (Ident x1, Ident x2) ->
       (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((Int i1, Ind ind1), (Int i2, Ind ind2)) -> (match tau with
           | [(T (LInt, []), Ind ind)]-> if (check_runtime_success rst flowto [ind1; ind2]) then (Int (i1+i2), Ind ind) else (Empty, Ind (-1))
           | _ -> (Empty, Ind (-1)))
       | _ -> (Empty, Ind (-1)))
    | Minus (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((Int i1, Ind ind1), (Int i2, Ind ind2)) -> (match tau with
           | [(T (LInt, []), Ind ind)]-> if (check_runtime_success rst flowto [ind1; ind2]) then (Int (i1-i2), Ind ind) else (Empty, Ind (-1))
           | _ -> (Empty, Ind (-1)))
       | _ -> (Empty, Ind (-1)))
    | Not (Ident x1) ->
      (match (find_tagged_var x1 ev, tau) with
       | ((True, Ind ind1), [(T (LFalse, []), Ind ind)]) -> if (check_runtime_success rst flowto [ind1]) then (False, Ind ind) else (Empty, Ind (-1))
       | ((False, Ind ind1), [(T (LTrue, []), Ind ind)]) -> if (check_runtime_success rst flowto [ind1]) then (True, Ind ind) else (Empty, Ind (-1))
       | _ -> (Empty, Ind (-1)))
    | And (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev, tau) with
       | ((True, Ind ind1), (False, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (False, Ind ind4) else (Empty, Ind (-1))
       | ((True, Ind ind1), (True, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (True, Ind ind3) else (Empty, Ind (-1))
       | ((False, Ind ind1), (True, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (False, Ind ind4) else (Empty, Ind (-1))
       | ((False, Ind ind1), (False, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (False, Ind ind4) else (Empty, Ind (-1))
       | _ -> (Empty, Ind (-1)))
    | Or (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev, tau) with
       | ((True, Ind ind1), (False, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (True, Ind ind3) else (Empty, Ind (-1))
       | ((True, Ind ind1), (True, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (True, Ind ind3) else (Empty, Ind (-1))
       | ((False, Ind ind1), (True, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (True, Ind ind3) else (Empty, Ind (-1))
       | ((False, Ind ind1), (False, Ind ind2), [(T (LTrue, []), Ind ind3);(T (LFalse, []), Ind ind4)]) -> if (check_runtime_success rst flowto [ind1;ind2]) then (False, Ind ind4) else (Empty, Ind (-1))
       | _ -> (Empty, Ind (-1)))
    | Equals (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((Int i1, Ind ind1), (Int i2, Ind ind2)) -> if i1 = i2 && (check_runtime_success rst flowto [ind1;ind2]) then (match tau with
                                                                     | [(T (LTrue, []), Ind ind)] -> (True, Ind ind)
                                                                     | _ -> (Empty, Ind (-1)))
                                                                else (match tau with
                                                                     | [(T (LFalse, []), Ind ind)] -> (False, Ind ind)
                                                                     | _ -> (Empty, Ind (-1)))
       | _ -> (Empty, Ind (-1)))
    | Appl (Ident x1, Ident x2) ->
      (match (find_tagged_var x1 ev, find_tagged_var x2 ev) with
       | ((TaggedClosure (Function (xx, ee), eevv), Ind ind1), v) -> if (check_runtime_success rst flowto [ind1]) then (tagged_eval_clauses ee ((xx, v)::eevv) rou delta rst) else (Empty, Ind (-1))
       | _ -> (Empty, Ind (-1)))
    | Proj (Ident x1, Lab l1) ->
      (match (find_tagged_var x1 ev) with
       | (TaggedClosure (Record r, eevv), Ind ind1)->if (check_runtime_success rst flowto [ind1]) then find_tagged_var (get_record_val r l1) eevv else (Empty, Ind (-1))
       | _ -> (Empty, Ind (-1)))
    | Match (Ident x1, p) ->
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
and tagged_eval_clauses (clauses:expr) (ev:tagged_env) rou delta rst =
  match clauses with
  | Clause (Ident x, Tau tau, b)::[] ->  tagged_eval_body b tau ev x rou delta rst
  | Clause (Ident x,Tau tau, b)::tl -> let res = tagged_eval_body b tau ev x rou delta rst in tagged_eval_clauses tl ((Ident x, res)::ev) rou delta rst
  | _ -> raise ClauseNotMatched;;

(*
x1:Int = 1
x2:Int = 2
x3:Int = x1+x2

should return 3
global_env = {x1->1, x2->2, x3->3}
sound = true
rou = []
delta = []
*)
let in1 = [Clause (Ident "x1",Tau [( T (LInt, []), Ind 1)], Int 1);
           Clause (Ident "x2",Tau [( T (LInt, []), Ind 2)], Int 2);
           Clause (Ident "x3",Tau [( T (LInt, []), Ind 3)], Plus (Ident "x1", Ident "x2"))];;
let (sound1, rou1, delta1) = typecheck in1;;
let res1 = tagged_eval_clauses in1 [] rou1 delta1 (get_runtime_success_dispatch_table in1 (get_all_typedec in1));;

(*
x1:True = True
x2:False = False
x3:[True;False] = x1 && x2

should return False
global_env = {x1->True, x2->False, x3->False}
sound = True
rou = []
delta = []
*)
let in2 = [Clause (Ident "x1",Tau [( T (LTrue, []), Ind 1)], True);
           Clause (Ident "x2",Tau [( T (LFalse, []), Ind 2)], False);
           Clause (Ident "x3",Tau [( T (LTrue, []), Ind 3); ( T (LFalse, []), Ind 4)], And (Ident "x1", Ident "x2"))];;
let (sound2, rou2, delta2) = typecheck in2;;
let res2 = tagged_eval_clauses in2 [] rou2 delta2 (get_runtime_success_dispatch_table in2 (get_all_typedec in2));;

(*
x1:Int = 1
x2:Int = x1

should return 1
gloval_env = {x1->1, x2->1, x2->x1}
sound = true
rou = []
delta = []
*)
let in3 = [Clause (Ident "x1", Tau [( T (LInt, []), Ind 1)], Int 1);
           Clause (Ident "x2", Tau [( T (LInt, []), Ind 2)], Var(Ident "x1"))];;
let (sound3, rou3, delta3) = typecheck in3;;
let res3 = tagged_eval_clauses in3 [] rou3 delta3 (get_runtime_success_dispatch_table in3 (get_all_typedec in3));;

(*
x1:[(LInt-{}, Ind 1)] = 1
x2:[(LTrue-{}, Ind 2)] = True
x3 : [({a:Int; b: True}-{}, Ind 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Ind 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

should return 3
global_env = {x1->1, x2->True, x3->Closure({a:x1; b:x2}, {x1->1;x2->True}); x4-> 3; x5->3; x4->x5}
sound = true
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in4 = [Clause (Ident "x1", Tau [( T (LInt, []), Ind 1)], Int 1);
           Clause (Ident "x2", Tau [( T (LTrue, []), Ind 2)], True);
           Clause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Ind 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Tau [( T (LInt, []), Ind 4)], Match (Ident "x3", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x5", Tau [( T (LInt, []), Ind 5)], Int 3)])]))];;
let (sound4, rou4, delta4) = typecheck in4;;
let res4 = tagged_eval_clauses in4 [] rou4 delta4 (get_runtime_success_dispatch_table in4 (get_all_typedec in4));;

(*
x1:LInt = 1
x2:LTrue = True
x3 : [{a:LStar};({b:LStar} - {c:LStar})] = {a:x1; b:x2}
x4 :LInt = Match x3 with
      | {PRecord [a:PStar; c: PStar]} -> x5:LInt = Int 3

sound = false
*)

let in5 = [Clause (Ident "x1", Tau [( T (LInt, []), Ind 1)], Int 1);
           Clause (Ident "x2", Tau [( T (LTrue, []), Ind 2)], True);
           Clause (Ident "x3", Tau [( T (LRecord [(Lab "a", LStar)], []), Ind 3); (T (LRecord [(Lab "b", LStar)], [LRecord [(Lab "c", LStar)]]), Ind 6)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Tau [( T (LInt, []), Ind 4)], Match (Ident "x3", [(PRecord [(Lab "a", PStar);(Lab "c", PStar)], [Clause (Ident "x5", Tau [( T (LInt, []), Ind 5)], Int 3)])]))];;

let (sound5, rou5, delta5) = typecheck in5;;

(*
x1 : LTrue = True
x2 : LFalse = false
x3 : {q:LStar} - [{q:LInt}, {q:LFalse}] = {q:x1}
x4 : {r:LStar} - [{r: LInt}] = {r: x2}
x5 : {a: {q:LStar}; b: {r:LStar}} - [{a: {q:LInt}}; {a:{q:LFalse}};
                                      {b:{r:LInt}}] = {a: x3, b:x4}

sound = false ****should be fixed
*)

let in6 = [Clause (Ident "x1", Tau [(T (LTrue, []), Ind 1)], True);
           Clause (Ident "x2", Tau [(T (LFalse, []), Ind 2)], False);
           Clause (Ident "x3", Tau [(T (LRecord [(Lab "q", LStar)],[LRecord [(Lab "q", LInt)];LRecord [(Lab "q", LFalse)]]), Ind 3)], Record [(Lab "q", Ident "x1")]);
           Clause (Ident "x4", Tau [(T (LRecord [(Lab "r", LStar)], [LRecord [(Lab "r", LInt)]]), Ind 4)], Record [(Lab "r", Ident "x2")]);
           Clause (Ident "x5",
                   Tau [(T (LRecord [(Lab "a", LRecord [(Lab "q", LStar)]);(Lab "b", LRecord [(Lab "r", LStar)])],
                            [LRecord [(Lab "a", LRecord [(Lab "q", LInt)])];
                             LRecord [(Lab "a", LRecord [(Lab "q", LFalse)])];
                             LRecord [(Lab "b", LRecord [(Lab "r", LInt)])]]), Ind 5)],
                   Record [(Lab "a", Ident "x3"); (Lab "b", Ident "x4")])
          ];;
let (sound6, rou6, delta6) = typecheck in6;;

(*
x1 : LTrue = True
x3 : {q:LStar} - [{q:LInt}, {q:LFalse}] = {q:x1}
sound = false
*)

let in7 = [Clause (Ident "x1", Tau [(T (LTrue, []), Ind 1)], True);
           Clause (Ident "x3", Tau [(T (LRecord [(Lab "q", LStar)],[LRecord [(Lab "q", LInt)];LRecord [(Lab "q", LFalse)]]), Ind 3)], Record [(Lab "q", Ident "x1")]);
          ];;
let (sound7, rou7, delta7) = typecheck in7;;

(*
x1:[(Int-{}, Ind 1);(True-{}, Ind 2)] = 1
x2:[(True-{}, Ind 3);(False-{}, Ind 4)] = True
x3 : [({a:Int; b: True}-{}, Ind 5);
      ({a:Int; b: False}-{}, Ind 6);
      ({a:True; b: True}-{}, Ind 7);
      ({a:True; b: False}-{}, Ind 8);] = {a:x1; b:x2}
x4 :[(LInt-{}, Ind 9)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:[(LInt-{}, Ind 10)] = Int 3
      | {PRecord [a:PTrue]} -> x6:[(LInt-{}, Ind 11)] = Int 4

should return 3
global_env = {x1->1, x2->True, x3->Closure({a:x1; b:x2}, {x1->1;x2->True}); x4-> 4; x6-> 4; x4->x6}
sound = false
rou:[(x3, [(1,3)->5; (1,4)->6; (2,3)->7; (2,4)->8])]
delta: [(x4, [5->1;6->1; 7->2; 8->2])]
*)
let in8 = [Clause (Ident "x1", Tau [( T (LInt, []), Ind 1); ( T (LTrue, []), Ind 2)], Int 1);
           Clause (Ident "x2", Tau [( T (LTrue, []), Ind 3);( T (LFalse, []), Ind 4)], True);
           Clause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Ind 5);
                                    ( T (LRecord [(Lab "a", LInt); (Lab "b", LFalse)], []), Ind 6);
                                    ( T (LRecord [(Lab "a", LTrue); (Lab "b", LTrue)], []), Ind 7);
                                    ( T (LRecord [(Lab "a", LTrue); (Lab "b", LFalse)], []), Ind 8);], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Tau [( T (LInt, []), Ind 9)], Match (Ident "x3",
                                                                    [(PRecord [(Lab "a", PInt)], [Clause (Ident "x5", Tau [( T (LInt, []), Ind 10)], Int 3)]);
                                                                     (PRecord [(Lab "a", PTrue)], [Clause (Ident "x6", Tau [( T (LInt, []), Ind 11)], Int 4)])]))];;
let (sound8, rou8, delta8) = typecheck in8;;


(*
x1:[(LInt-{LTrue}, Ind 1)] = 1
x2:[(LTrue-{LFalse}, Ind 2)] = True
x3 : [({a:Int; b: True}-{}, Ind 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Ind 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

should return 3
global_env = {x1->1, x2->True, x3->Closure({a:x1; b:x2}, {x1->1;x2->True}); x4-> 3; x5->3; x4->x5}
sound = false
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in9 = [Clause (Ident "x1", Tau [( T (LInt, [LTrue]), Ind 1)], Int 1);
           Clause (Ident "x2", Tau [( T (LTrue, [LFalse]), Ind 2)], True);
           Clause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Ind 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Tau [( T (LInt, []), Ind 4)], Match (Ident "x3", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x5", Tau [( T (LInt, []), Ind 5)], Int 3)])]))];;
let (sound9, rou9, delta9) = typecheck in9;;

(*
x1 :LFun = Fun x2 -> {x3 = x2 + 1}
x4 = 1
x5 = x1 x4 *)

(*
x1:Int = 1;
x2:True = true
x3:Record = {a:x1; b:x2}
x4:Int = x3.a *)

let in10 = [Clause (Ident "x1", Tau [( T (LInt, []), Ind 1)], Int 1);
            Clause (Ident "x2", Tau [( T (LTrue, []), Ind 2)], True);
            Clause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Ind 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
            Clause (Ident "x4", Tau [( T (LInt, []), Ind 4)], Proj (Ident "x3", Lab "a"))];;
let table10 = get_runtime_success_dispatch_table in10 (get_all_typedec in10);;

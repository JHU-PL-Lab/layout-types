open Layout;;
open Setinterpreter;;
open Helper;;

exception CannotFindTau;;

(* helper methods *)

(* Get a typedec table with variable to tags mapping specified in the program, serves to lookup purposes.  *)
let rec get_all_typedec (expr: tagged_expr) =
  match expr with
  | TaggedClause (Ident x, Tau tau, TaggedFunction (Ident x1,Tau tau1, e1))::tl -> [(Ident x, Tau tau); (Ident x1, Tau tau1)]@(get_all_typedec tl)@(get_all_typedec e1)
  | TaggedClause (Ident x, Tau tau, TaggedMatch (Ident _, pattern))::tl ->
    (let rec iterate_pattern pattern =
       match pattern with
       |(_, e1)::ttll -> (get_all_typedec e1)@(iterate_pattern ttll)
       | _ -> [] in (Ident x, Tau tau)::(iterate_pattern pattern)@(get_all_typedec tl))
  | TaggedClause (Ident x, Tau tau, _)::tl -> (Ident x, Tau tau)::(get_all_typedec tl)
  | _ -> [];;

(* Find the tag associated with variable x in the typedec table *)
let rec find_tau typedec x =
  match typedec with
  | (Ident x1, Tau tau)::tl -> if x = x1 then tau else find_tau tl x
  | _ -> raise CannotFindTau;;

(* Atomic typed
   See commit 31a09f, Definition 1.16
   Modified: all the "=" in the definition should is changed to <<: *)
let rec atomic_typed (program:tagged_expr) typedec =
  let rec exists_subtype (t:t) tau =
    match tau with
    | (t1, _)::tl -> if is_subtype_t t t1 then true else exists_subtype t tl
    | _ -> false
  in match program with
    | hd::tl ->
      (match hd with
       | TaggedClause (Ident _, Tau tau, Int _) -> exists_subtype (T (LInt,[])) tau
       | TaggedClause (Ident _, Tau tau, True) -> exists_subtype (T (LTrue,[])) tau
       | TaggedClause (Ident _, Tau tau, False) -> exists_subtype (T (LFalse,[])) tau
       | TaggedClause (Ident _, Tau tau, TaggedFunction (_,_, e1)) -> (exists_subtype (T (LFun,[])) tau) && (atomic_typed e1 typedec)
       | TaggedClause (Ident _, Tau tau, Equals (Ident x1, Ident x2)) ->((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                            && (exists_subtype (T (LInt,[])) (find_tau typedec x1)) && (exists_subtype (T (LInt,[])) (find_tau typedec x2))
       | TaggedClause (Ident _, Tau tau, Plus (Ident x1, Ident x2)) -> (exists_subtype (T (LInt,[])) tau)
                                                                           && (exists_subtype (T (LInt,[])) (find_tau typedec x1)) && (exists_subtype (T (LInt,[])) (find_tau typedec x2))
       | TaggedClause (Ident _, Tau tau, Minus (Ident x1, Ident x2)) -> (exists_subtype (T (LInt,[])) tau)
                                                                            && (exists_subtype (T (LInt,[])) (find_tau typedec x1)) && (exists_subtype (T (LInt,[])) (find_tau typedec x2))
       | TaggedClause (Ident _, Tau tau, And (Ident x1, Ident x2)) -> ((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                          && (exists_subtype (T (LTrue,[])) (find_tau typedec x1) || exists_subtype (T (LFalse,[])) (find_tau typedec x1))
                                                                          && (exists_subtype (T (LTrue,[])) (find_tau typedec x2) || exists_subtype (T (LFalse,[])) (find_tau typedec x2))
       | TaggedClause (Ident _, Tau tau, Or (Ident x1, Ident x2)) -> ((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                         && (exists_subtype (T (LTrue,[])) (find_tau typedec x1) || exists_subtype (T (LFalse,[])) (find_tau typedec x1))
                                                                         && (exists_subtype (T (LTrue,[])) (find_tau typedec x2) || exists_subtype (T (LFalse,[])) (find_tau typedec x2))
       | TaggedClause (Ident _, Tau tau, Not (Ident x1)) -> ((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                && (exists_subtype (T (LTrue,[])) (find_tau typedec x1) || exists_subtype (T (LFalse,[])) (find_tau typedec x1))
       | TaggedClause (Ident _, Tau _, TaggedMatch (_, patterns)) ->
         (let rec check_all_patterns patterns =
            match patterns with
            | (_, e1)::ttll -> atomic_typed e1 typedec && check_all_patterns ttll
            | _ -> true in check_all_patterns patterns)
       | _ -> true) && (atomic_typed tl typedec)
    | _ -> true;;

(* Subtype soundness
   See commit 31a09f, Definition 1.17 *)
let rec sound_subtype typedec (df:env) =
  match df with
  | (Ident x1, Var(Ident x2))::tl -> if (is_subtype (find_tau typedec x2) (find_tau typedec x1)) then sound_subtype typedec tl else false
  | _::_ -> raise WrongFormatOfDataFlow
  | _ -> true;;

(* Record Soundness
   See commit 31a09f, Definition 1.18
   Returns whether the program is record sound. If so then return rou that maps
   from the nonces of the field to the nonce of the record. *)
let rec record_soundness typedec (program:tagged_expr) =
  (* Combine the field tags to give the record tag
     See commit 31a09f, Definition 1.14 *)
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
  (* Product all the tags of all fields to give all possible tags for the record
     See commit 31a09f, Definition 1.18 Rule 1*)
  let get_field_product r typedec =
    (let rec iterate_res lab t nc res =
      match res with
      | (record_list, nonce_list)::tl -> ((lab, t)::record_list,nc::nonce_list)::(iterate_res lab t nc tl)
      | _ -> []
    in let rec iterate_disjuncts lab disjuncts res =
         match disjuncts with
         | (t, nc)::tl -> (iterate_res lab t nc res) @ (iterate_disjuncts lab tl res)
         | _ -> []
    in let rec iterate_record r typedec =
         match r with
         | (lab, Ident x)::tl -> let res = iterate_record tl typedec in iterate_disjuncts lab (find_tau typedec x) res
         | _ -> [([],[])]
    in iterate_record r typedec) in
  let rec find_matching_nonce r1 tau =
    (match tau with
    | (t1, Nonce nc)::tl -> if is_subtype_t r1 t1 then nc else find_matching_nonce r1 tl
    | _ -> -1) in
  (match program with
  | (TaggedClause (Ident x, Tau tau, Record r))::tl ->
    let rec iterate_product product tau =
      match product with
      | (record, nonce_list)::tl ->let match_nonce = find_matching_nonce (get_canonical_record_wrapper record) tau in
        if (match_nonce = -1) then (false,[])
        else (let (matches, table) = iterate_product tl tau in
              if matches = true then (true, (nonce_list, match_nonce) :: table) else (false, []))
      | _ ->(true, [])
    in let (matches_tl, rou_tl) = record_soundness typedec tl
    in let (matches_cur, table_cur) = iterate_product (get_field_product r typedec) tau
    in if matches_tl && matches_cur then (true, (Ident x, table_cur)::rou_tl) else (false, [])
  | _::tl -> record_soundness typedec tl
  | _ -> (true, []));;

(* Pattern Completeness
   See commit 31a09f, Definition 1.20, 1.21*)
let rec pattern_complete typedec (program:tagged_expr) =
  (* Pattern Cover
     See commit 31a09f, Definition 1.19*)
  let rec pattern_cover tau patterns =
    (match tau with
     | (t, Nonce nc)::tl ->
      let rec t_not_cover_previous_patterns patterns pat_ind =
        if pat_ind = 1 then true else
          (match patterns with
           |(p,_)::ttll -> if t_pattern_not_match t p then t_not_cover_previous_patterns ttll (pat_ind-1) else false
           | _ -> true)
      in let rec t_covers_pattern patterns pat_ind all_patterns=
        match patterns with
        | (p,_)::ttll -> if t_pattern_match t p && t_not_cover_previous_patterns all_patterns pat_ind then pat_ind else t_covers_pattern ttll (pat_ind+1) all_patterns
        | _ -> (-1)
      in let cur_match = t_covers_pattern patterns 1 patterns
      in let (tail_match, delta) = pattern_cover tl patterns
      in if (cur_match != (-1)) && tail_match then (true, (Nonce nc, cur_match)::delta) else (false, [])
    | _ -> (true, [])) in
  (match program with
   | (TaggedClause (Ident x1, Tau _, TaggedMatch (Ident x2, patterns)))::tl ->
     let rec iterate_pattern_body patterns =
       match patterns with
       | (_, e)::tl ->
         let (match_cur_pattern, delta_cur_pattern) = pattern_complete typedec e
         in let (match_pattern_tail, delta_pattern_tail) = iterate_pattern_body tl
         in if match_cur_pattern && match_pattern_tail then (true, delta_cur_pattern@delta_pattern_tail) else (false, [])
       | _ -> (true, [])
      in let (match_cur, table_cur) = pattern_cover (find_tau typedec x2) patterns
      in let (match_tail, delta_tail) = pattern_complete typedec tl
      in let (match_pattern_body, delta_pattern_body) = iterate_pattern_body patterns
      in if match_cur && match_tail && match_pattern_body then (true, ((Ident x1, table_cur) :: delta_tail)@delta_pattern_body) else (false, [])
    | (TaggedClause (Ident _, Tau _, TaggedFunction (Ident _,_, e2)))::tl ->
      let (match_func_body, delta_func_body) = pattern_complete typedec e2
      in let (match_tail, delta_tail) = pattern_complete typedec tl
      in if match_func_body && match_tail then (true, delta_func_body@delta_tail) else (false, [])
    | _::tl -> pattern_complete typedec tl
    | _ -> (true,[]));;

(* Typecheck
   See commit 31a09f, Definition 1.22*)
let typecheck (program:tagged_expr) =
  let (_, df) = eval (untag_program program) in
  let typedec = get_all_typedec program in
  let (recordsound, rou) = (record_soundness typedec program) in
  let (patterncomplete, delta) = (pattern_complete typedec program) in
  ((atomic_typed program typedec) && (sound_subtype typedec !df) && recordsound && patterncomplete,rou, delta);;

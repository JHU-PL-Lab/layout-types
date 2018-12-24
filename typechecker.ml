open Layout;;
open Setinterpreter;;
open Helper;;

exception CannotFindTau;;

(* helper methods *)

(* Get a typedec table with variable to tags mapping specified in the program, serves to lookup purposes.  *)
let rec get_all_typedec (expr: tagged_expr) =
  match expr with
  | TaggedClause (Ident x, Tau tau, TaggedFunction (Ident x1, e1))::tl -> (Ident x, Tau tau)::(get_all_typedec tl)@(get_all_typedec e1)
  | TaggedClause (Ident x, Tau tau, TaggedMatch (Ident x1, pattern))::tl ->
    (let rec iterate_pattern pattern =
       match pattern with
       |(p1, e1)::ttll -> (get_all_typedec e1)@(iterate_pattern ttll)
       | _ -> [] in (Ident x, Tau tau)::(iterate_pattern pattern)@(get_all_typedec tl))
  | TaggedClause (Ident x, Tau tau, b)::tl -> (Ident x, Tau tau)::(get_all_typedec tl)
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
    | (t1, nc)::tl -> if is_subtype_t t t1 then true else exists_subtype t tl
    | _ -> false
  in match program with
  | TaggedClause (Ident x, Tau tau, Int i)::tl -> exists_subtype (T (LInt,[])) tau
  | TaggedClause (Ident x, Tau tau, True)::tl -> exists_subtype (T (LTrue,[])) tau
  | TaggedClause (Ident x, Tau tau, False)::tl -> exists_subtype (T (LFalse,[])) tau
  | TaggedClause (Ident x, Tau tau, TaggedFunction (x1, e1))::tl -> exists_subtype (T (LFun,[])) tau
  | TaggedClause (Ident x, Tau tau, Equals (Ident x1, Ident x2))::tl ->((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                       && (exists_subtype (T (LInt,[])) (find_tau typedec x1)) && (exists_subtype (T (LInt,[])) (find_tau typedec x2))
  | TaggedClause (Ident x, Tau tau, Plus (Ident x1, Ident x2))::tl -> (exists_subtype (T (LInt,[])) tau)
                                                                      && (exists_subtype (T (LInt,[])) (find_tau typedec x1)) && (exists_subtype (T (LInt,[])) (find_tau typedec x2))
  | TaggedClause (Ident x, Tau tau, Minus (Ident x1, Ident x2))::tl -> (exists_subtype (T (LInt,[])) tau)
                                                                       && (exists_subtype (T (LInt,[])) (find_tau typedec x1)) && (exists_subtype (T (LInt,[])) (find_tau typedec x2))
  | TaggedClause (Ident x, Tau tau, And (Ident x1, Ident x2))::tl -> ((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                     && (exists_subtype (T (LTrue,[])) (find_tau typedec x1) || exists_subtype (T (LFalse,[])) (find_tau typedec x1))
                                                                     && (exists_subtype (T (LTrue,[])) (find_tau typedec x2) || exists_subtype (T (LFalse,[])) (find_tau typedec x2))
  | TaggedClause (Ident x, Tau tau, Or (Ident x1, Ident x2))::tl -> ((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                                    && (exists_subtype (T (LTrue,[])) (find_tau typedec x1) || exists_subtype (T (LFalse,[])) (find_tau typedec x1))
                                                                    && (exists_subtype (T (LTrue,[])) (find_tau typedec x2) || exists_subtype (T (LFalse,[])) (find_tau typedec x2))
  | TaggedClause (Ident x, Tau tau, Not (Ident x1))::tl -> ((exists_subtype (T (LTrue,[])) tau) || (exists_subtype (T (LFalse,[])) tau))
                                                           && (exists_subtype (T (LTrue,[])) (find_tau typedec x1) || exists_subtype (T (LFalse,[])) (find_tau typedec x1))
  | TaggedClause (Ident x, Tau tau, TaggedMatch (x1, patterns))::tl ->
    (let rec check_all_patterns patterns =
       match patterns with
       | (p1, e1)::ttll -> atomic_typed e1 typedec && check_all_patterns ttll
       | _ -> true in check_all_patterns patterns && atomic_typed tl typedec)
  | TaggedClause (Ident x, Tau tau, b)::tl -> atomic_typed tl typedec
  | _ -> true;;

(* Subtype soundness
   See commit 31a09f, Definition 1.17 *)
let rec sound_subtype typedec (df:env) =
  match df with
  | (Ident x1, Var(Ident x2))::tl -> if (is_subtype (find_tau typedec x2) (find_tau typedec x1)) then sound_subtype typedec tl else false
  | hd::tl -> raise WrongFormatOfDataFlow
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
  | hd::tl -> record_soundness typedec tl
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
           |(p,e)::ttll -> if t_pattern_not_match t p then t_not_cover_previous_patterns ttll (pat_ind-1) else false
           | _ -> true)
      in let rec t_covers_pattern patterns pat_ind all_patterns=
        match patterns with
        | (p,e)::ttll -> if t_pattern_match t p && t_not_cover_previous_patterns all_patterns pat_ind then pat_ind else t_covers_pattern ttll (pat_ind+1) all_patterns
        | _ -> (-1)
      in let cur_match = t_covers_pattern patterns 1 patterns
      in let (tail_match, delta) = pattern_cover tl patterns
      in if (cur_match != (-1)) && tail_match then (true, (Nonce nc, cur_match)::delta) else (false, [])
    | _ -> (true, [])) in
  (match program with
   | (TaggedClause (Ident x1, Tau tau, TaggedMatch (Ident x2, patterns)))::tl ->
     let rec iterate_pattern_body patterns =
       match patterns with
       | (p, e)::tl ->
         let (match_cur_pattern, delta_cur_pattern) = pattern_complete typedec e
         in let (match_pattern_tail, delta_pattern_tail) = iterate_pattern_body tl
         in if match_cur_pattern && match_pattern_tail then (true, delta_cur_pattern@delta_pattern_tail) else (false, [])
       | _ -> (true, [])
      in let (match_cur, table_cur) = pattern_cover (find_tau typedec x2) patterns
      in let (match_tail, delta_tail) = pattern_complete typedec tl
      in let (match_pattern_body, delta_pattern_body) = iterate_pattern_body patterns
      in if match_cur && match_tail && match_pattern_body then (true, ((Ident x1, table_cur) :: delta_tail)@delta_pattern_body) else (false, [])
    | (TaggedClause (Ident x1, Tau tau, TaggedFunction (Ident x2, e2)))::tl ->
      let (match_func_body, delta_func_body) = pattern_complete typedec e2
      in let (match_tail, delta_tail) = pattern_complete typedec tl
      in if match_func_body && match_tail then (true, delta_func_body@delta_tail) else (false, [])
    | hd::tl -> pattern_complete typedec tl
    | _ -> (true,[]));;

(* Typecheck
   See commit 31a09f, Definition 1.22*)
let typecheck (program:tagged_expr) =
  let (_, df) = eval (untag_program program) in
  let typedec = get_all_typedec program in
  let (recordsound, rou) = (record_soundness typedec program) in
  let (patterncomplete, delta) = (pattern_complete typedec program) in
  ((atomic_typed program typedec) && (sound_subtype typedec !df) && recordsound && patterncomplete,rou, delta);;

(*
x1:Int = 1
x2:Int = 2
x3:Int = x1+x2

should return 3
df = {}
sound = true
rou = []
delta = []
*)
let in1 = [TaggedClause (Ident "x1",Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2",Tau [( T (LInt, []), Nonce 2)], Int 2);
           TaggedClause (Ident "x3",Tau [( T (LInt, []), Nonce 3)], Plus (Ident "x1", Ident "x2"))];;
let (sound1, rou1, delta1) = typecheck in1;;

(*
x1:True = True
x2:False = False
x3:[True;False] = x1 && x2

should return False
df = {}
sound = True
rou = []
delta = []
*)
let in2 = [TaggedClause (Ident "x1",Tau [( T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x2",Tau [( T (LFalse, []), Nonce 2)], False);
           TaggedClause (Ident "x3",Tau [( T (LTrue, []), Nonce 3); ( T (LFalse, []), Nonce 4)], And (Ident "x1", Ident "x2"))];;
let (sound2, rou2, delta2) = typecheck in2;;

(*
x1:Int = 1
x2:Int = x1

should return 1
df = {x2->x1}
sound = true
rou = []
delta = []
*)
let in3 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LInt, []), Nonce 2)], Var(Ident "x1"))];;
let (sound3, rou3, delta3) = typecheck in3;;

(*
x1:[(LInt-{}, Nonce 1)] = 1
x2:[(LTrue-{}, Nonce 2)] = True
x3 : [({a:Int; b: True}-{}, Nonce 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

should return 3
df = {x4->x5}
sound = true
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in4 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 5)], Int 3)])]))];;
let (sound4, rou4, delta4) = typecheck in4;;


(*
x1:LInt = 1
x2:LTrue = True
x3 : [{a:LStar};({b:LStar} - {c:LStar})] = {a:x1; b:x2}
x4 :LInt = Match x3 with
      | {PRecord [a:PStar; c: PStar]} -> x5:LInt = Int 3

sound = false
*)

let in5 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LStar)], []), Nonce 3); (T (LRecord [(Lab "b", LStar)], [LRecord [(Lab "c", LStar)]]), Nonce 6)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PStar);(Lab "c", PStar)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 5)], Int 3)])]))];;

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

let in6 = [TaggedClause (Ident "x1", Tau [(T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x2", Tau [(T (LFalse, []), Nonce 2)], False);
           TaggedClause (Ident "x3", Tau [(T (LRecord [(Lab "q", LStar)],[LRecord [(Lab "q", LInt)];LRecord [(Lab "q", LFalse)]]), Nonce 3)], Record [(Lab "q", Ident "x1")]);
           TaggedClause (Ident "x4", Tau [(T (LRecord [(Lab "r", LStar)], [LRecord [(Lab "r", LInt)]]), Nonce 4)], Record [(Lab "r", Ident "x2")]);
           TaggedClause (Ident "x5",
                   Tau [(T (LRecord [(Lab "a", LRecord [(Lab "q", LStar)]);(Lab "b", LRecord [(Lab "r", LStar)])],
                            [LRecord [(Lab "a", LRecord [(Lab "q", LInt)])];
                             LRecord [(Lab "a", LRecord [(Lab "q", LFalse)])];
                             LRecord [(Lab "b", LRecord [(Lab "r", LInt)])]]), Nonce 5)],
                   Record [(Lab "a", Ident "x3"); (Lab "b", Ident "x4")])
          ];;
let (sound6, rou6, delta6) = typecheck in6;;

(*
x1 : LTrue = True
x3 : {q:LStar} - [{q:LInt}, {q:LFalse}] = {q:x1}
sound = false
*)

let in7 = [TaggedClause (Ident "x1", Tau [(T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x3", Tau [(T (LRecord [(Lab "q", LStar)],[LRecord [(Lab "q", LInt)];LRecord [(Lab "q", LFalse)]]), Nonce 3)], Record [(Lab "q", Ident "x1")]);
          ];;
let (sound7, rou7, delta7) = typecheck in7;;

(*
x1:[(Int-{}, Nonce 1);(True-{}, Nonce 2)] = 1
x2:[(True-{}, Nonce 3);(False-{}, Nonce 4)] = True
x3 : [({a:Int; b: True}-{}, Nonce 5);
      ({a:Int; b: False}-{}, Nonce 6);
      ({a:True; b: True}-{}, Nonce 7);
      ({a:True; b: False}-{}, Nonce 8);] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 9)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:[(LInt-{}, Nonce 10)] = Int 3
      | {PRecord [a:PTrue]} -> x6:[(LInt-{}, Nonce 11)] = Int 4

should return 3
df = {x4->x6}
sound = false
rou:[(x3, [(1,3)->5; (1,4)->6; (2,3)->7; (2,4)->8])]
delta: [(x4, [5->1;6->1; 7->2; 8->2])]
*)
let in8 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1); ( T (LTrue, []), Nonce 2)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 3);( T (LFalse, []), Nonce 4)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 5);
                                    ( T (LRecord [(Lab "a", LInt); (Lab "b", LFalse)], []), Nonce 6);
                                    ( T (LRecord [(Lab "a", LTrue); (Lab "b", LTrue)], []), Nonce 7);
                                    ( T (LRecord [(Lab "a", LTrue); (Lab "b", LFalse)], []), Nonce 8);], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 9)], TaggedMatch (Ident "x3",
                                                                    [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 10)], Int 3)]);
                                                                     (PRecord [(Lab "a", PTrue)], [TaggedClause (Ident "x6", Tau [( T (LInt, []), Nonce 11)], Int 4)])]))];;
let (sound8, rou8, delta8) = typecheck in8;;


(*
x1:[(LInt-{LTrue}, Nonce 1)] = 1
x2:[(LTrue-{LFalse}, Nonce 2)] = True
x3 : [({a:Int; b: True}-{}, Nonce 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

should return 3
df = {x4->x5}
sound = false
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in9 = [TaggedClause (Ident "x1", Tau [( T (LInt, [LTrue]), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, [LFalse]), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 5)], Int 3)])]))];;
let (sound9, rou9, delta9) = typecheck in9;;

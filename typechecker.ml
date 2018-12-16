open Layout;;
open Setinterpreter;;

exception CannotFindTau;;

(* helper methods *)
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

let rec find_tau typedec x =
  match typedec with
  | (Ident x1, Tau tau)::tl -> if x = x1 then tau else find_tau tl x
  | _ -> raise CannotFindTau;;

(* Atomic typed *)
(* should we include OrVals?
   should we include false/true for and/or/not? *)
let rec atomic_typed (program:tagged_expr) =
  match program with
  | TaggedClause (Ident x, Tau tau, Int i)::tl ->
    (match tau with
     | [(T (LInt, []), Nonce nc)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, True)::tl ->
    (match tau with
     | [(T (LTrue, []), Nonce nc)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, False)::tl ->
    (match tau with
     | [(T (LFalse, []), Nonce nc)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, TaggedFunction (x1, e1))::tl ->
    (match tau with
     | [(T (LFun, []), Nonce nc)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, Equals (x1, x2))::tl ->
    (match tau with
     | [(T (LTrue, []), Nonce nc);(T (LFalse, []), Nonce nc2)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, Plus (x1, x2))::tl ->
    (match tau with
     | [(T (LInt, []), Nonce nc)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, Minus (x1, x2))::tl ->
    (match tau with
     | [(T (LInt, []), Nonce nc)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, And (x1, x2))::tl ->
    (match tau with
     | [(T (LTrue, []), Nonce nc);(T (LFalse, []), Nonce nc2)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, Or (x1, x2))::tl ->
    (match tau with
     | [(T (LTrue, []), Nonce nc);(T (LFalse, []), Nonce nc2)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, Not x1)::tl ->
    (match tau with
     | [(T (LTrue, []), Nonce nc);(T (LFalse, []), Nonce nc2)] -> atomic_typed tl
     | _ -> false)
  | TaggedClause (Ident x, Tau tau, TaggedMatch (x1, patterns))::tl ->
    (let rec check_all_patterns patterns =
       match patterns with
       | (p1, e1)::ttll -> atomic_typed e1 && check_all_patterns ttll
       | _ -> true in check_all_patterns patterns && atomic_typed tl)
  | TaggedClause (Ident x, Tau tau, b)::tl -> atomic_typed tl
  | _ -> true;;

(* Subtype soundness *)
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
   | _ -> false);;

let rec is_subtype_t (t1:t) (t2:t) =
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
let rec record_soundness typedec (program:tagged_expr) =
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
  let rec iterate_tau r1 tau =
    (match tau with
    | (t1, Nonce nc)::tl -> if is_subtype_t r1 t1 then nc else iterate_tau r1 tl
    | _ -> -1) in
  (match program with
  | (TaggedClause (Ident x, Tau tau, Record r))::tl ->
    let rec iterate_product product tau =
      match product with
      | (record, nonce_list)::tl ->let match_ind = iterate_tau (get_canonical_record_wrapper record) tau in
        if (match_ind = -1) then (false,[])
        else (let (matches, table) = iterate_product tl tau in
              if matches = true then (true, (nonce_list, match_ind) :: table) else (false, []))
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

let rec pattern_complete typedec (program:tagged_expr) =
  let rec pattern_cover tau patterns =
    (match tau with
    | (T (bt, neg), Nonce nc)::tl ->
      let rec iterate_patterns patterns pat_ind=
        match patterns with
        | (p,e)::ttll -> if t_pattern_match bt neg p then pat_ind else iterate_patterns ttll (pat_ind+1)
        | _ -> 0
      in let cur_match = iterate_patterns patterns 1
      in let (tail_match, delta) = pattern_cover tl patterns
      in if (cur_match != 0) && tail_match then (true, (Nonce nc, cur_match)::delta) else (false, [])
    | _ -> (true, [])) in
  (match program with
    | (TaggedClause (Ident x1, Tau tau, TaggedMatch (Ident x2, patterns)))::tl ->
      let (match_cur, table_cur) = pattern_cover (find_tau typedec x2) patterns
      in let (match_tail, delta_tail) = pattern_complete typedec tl
      in if match_cur && match_tail then (true, (Ident x1, table_cur) :: delta_tail) else (false, [])
    | hd::tl -> pattern_complete typedec tl
    | _ -> (true,[]));;

(* typechecking, return true/false, rou and delta *)
let typecheck (program:tagged_expr) =
  let (_, global) = eval (untag_program program) in
  let typedec = get_all_typedec program in
  let (recordsound, rou) = (record_soundness typedec program) in
  let (patterncomplete, delta) = (pattern_complete typedec program) in
  ((atomic_typed program) && (sound_subtype typedec !global) && recordsound && patterncomplete,rou, delta);;

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
let in1 = [TaggedClause (Ident "x1",Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2",Tau [( T (LInt, []), Nonce 2)], Int 2);
           TaggedClause (Ident "x3",Tau [( T (LInt, []), Nonce 3)], Plus (Ident "x1", Ident "x2"))];;
let (sound1, rou1, delta1) = typecheck in1;;

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
let in2 = [TaggedClause (Ident "x1",Tau [( T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x2",Tau [( T (LFalse, []), Nonce 2)], False);
           TaggedClause (Ident "x3",Tau [( T (LTrue, []), Nonce 3); ( T (LFalse, []), Nonce 4)], And (Ident "x1", Ident "x2"))];;
let (sound2, rou2, delta2) = typecheck in2;;

(*
x1:Int = 1
x2:Int = x1

should return 1
gloval_env = {x1->1, x2->1, x2->x1}
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
global_env = {x1->1, x2->True, x3->Closure({a:x1; b:x2}, {x1->1;x2->True}); x4-> 3; x5->3; x4->x5}
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
global_env = {x1->1, x2->True, x3->Closure({a:x1; b:x2}, {x1->1;x2->True}); x4-> 4; x6-> 4; x4->x6}
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
global_env = {x1->1, x2->True, x3->Closure({a:x1; b:x2}, {x1->1;x2->True}); x4-> 3; x5->3; x4->x5}
sound = false
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in9 = [TaggedClause (Ident "x1", Tau [( T (LInt, [LTrue]), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, [LFalse]), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 5)], Int 3)])]))];;
let (sound9, rou9, delta9) = typecheck in9;;

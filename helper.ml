open Layout;;

(* Returns true if bt1 conflicts with bt2,
   See commit 31a09f, Definition 1.6 Rule 6
   Note: Conflict means the intersection is empty *)
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
   | (LRecord r1, _ ) -> true);;


(* Returns true if bt1 is a subtype of bt2, false otherwise.
   See commit 31a09f, Definition 1.10 for specification
   Modified: bt <<: bt' also when bt = bt'*)
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
           | _ -> true
         in check_record l1 l2)
   | _ -> false);;

(* Returns true it t1 is a subtype of t2, false otherwise.
   See commit 31a09f, Definition 1.10 *)
let rec is_subtype_t (t1:t) (t2:t) =
  (match (t1, t2) with
  | (T (bt1, neg_list1), T (bt2, neg_list2)) ->
    let rec iterate_neg neg1 bt2 =
      match neg1 with
      | bt1::tl -> if is_subtype_bt bt2 bt1 then true else iterate_neg tl bt2
      | _ -> false
    in
    let rec check_neg neg_list1 neg_list2 =
      match neg_list2 with
      | neg2::tl -> if conflict bt1 neg2 || iterate_neg neg_list1 neg2 then check_neg neg_list1 tl else false
      | _ -> true
    in if is_subtype_bt bt1 bt2 then check_neg neg_list1 neg_list2 else false);;

(* Returns true if t1 is subtype of t2, false otherwise.
   t1 and t2 are both tau type
   See commit 31a09f,Definition 1.11. *)
let rec is_subtype tau1 tau2 =
  let rec iterate_tau2 nc1 tau2 =
    match tau2 with
    | (t2, nc2)::tl -> if (nc1 = nc2) then true else iterate_tau2 nc1 tl
    | _ -> false
  in
  let rec iterate_tau1 tau1 tau2 =
    match tau1 with
    | (t1, nc1)::tl -> if iterate_tau2 nc1 tau2 then is_subtype tl tau2 else false
    | _ -> true
  in iterate_tau1 tau1 tau2;;

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

(* Transform a pattern to a base tag
   See commit 31a09f, Definition 3.2 Rule 2 *)
let rec pattern_to_bt p =
  (match p with
   | PInt -> LInt
   | PTrue -> LTrue
   | PFalse -> LFalse
   | PFun -> LFun
   | PStar -> LStar
   | PRecord pr ->
     let rec iterate_record pr =
       (match pr with
        | (Lab lab, ppaa)::tl -> (Lab lab, pattern_to_bt ppaa)::(iterate_record tl)
        | _ -> [])
     in LRecord (iterate_record pr)
  )

(* Returns true if bt matches the pattern
   See commit 31a09f, Definition 1.3 Rule 2*)
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

(* Returns true if bt does not match a pattern.
   See commit 31a09f, Def 1.3 Rule 3*)
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

(* Returns true if t matches the pattern.
   See commit 31a09f, Def 1.3 Rule 1*)
let t_pattern_match (t:t) pattern =
   match t with
   | T (bt, neg) -> tb_pattern_match bt pattern;;

(* Returns true if t matches the pattern.
   Don't have the definition yet in commit 31a09f
   t does not match the pattern if tb does not match the pattern
   Or the pattern is a subset of the negative part of t. *)
let t_pattern_not_match (t:t) pattern =
  let rec pattern_is_subset_of_neg neg_list pat_tag =
    match neg_list with
    | neg1::tl -> if is_subtype_bt pat_tag neg1 then true else pattern_is_subset_of_neg tl pat_tag
    | _ -> false
  in match t with
    | T (bt, neg) -> if tb_pattern_not_match bt pattern then true else pattern_is_subset_of_neg neg (pattern_to_bt pattern);;

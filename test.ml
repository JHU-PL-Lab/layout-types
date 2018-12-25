open OUnit;;
open Typeinference;;
open Typechecker;;
open Layout;;

let test_wrapper input =
  let (sound, _, _) = typecheck (tag_program input (type_inference input))
  in sound;;

(* Test when no match is present
 x0 = 1;
 x1 = {a:x0};
 expected res:
 x0: *
 x1: * *)
let in1 = [Clause (Ident "x0", Int 1);
           Clause (Ident "x1", Record [(Lab "a", Ident "x0")])];;
let test1 = assert_equal true (test_wrapper in1);;

(* Simple test
x0 = 1;
x1 = match x0 with
      | Int -> x2 = 1
      | * -> x3 = 2*)
let in2 = [Clause (Ident "x0", Int 1);
           Clause (Ident "x1", Match (Ident "x0", [(PInt, [Clause (Ident "x2", Int 1)]);
                                                   (PStar, [Clause (Ident "x3", Int 2)])]))];;
let test2 = assert_equal true (test_wrapper in2);;

(*
  Test subtyping inside atomic typing
  x1 = 1
  x2 = match x1 with
        | false -> x3 = 1
        | * -> x4 = 2
 *)

let in3 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Match (Ident "x1", [(PFalse, [Clause (Ident "x3", Int 1)]);
                                                   (PStar, [Clause (Ident "x4", Int 2)])]))];;
let test3 = assert_equal true (test_wrapper in3);;

(* Test record projection
   x1 = 1
   x2 = 2
   x3 = {a:x1; b:x2}
   x4 = match x3 with
        | {a:int; b:int} -> x5 = 1
        | * -> x6 = 2 *)
let in4 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Int 2);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt); (Lab "b", PInt)],[Clause (Ident "x5", Int 1)]);
                                                   (PStar, [Clause (Ident "x6", Int 2)])]))]
let test4 = assert_equal true (test_wrapper in4);;

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
let in5 = [Clause (Ident "x1", Int 1);
            Clause (Ident "x2", Int 2);
            Clause (Ident "x3", Plus (Ident "x1", Ident "x2"));
            Clause (Ident "x4", Match (Ident "x3", [(PInt, [Clause (Ident "x5", Int 1)]);
                                                    (PStar, [Clause (Ident "x6", Int 2)])]))];;
let test5 = assert_equal true (test_wrapper in5);;

(* Test atomic typing
   This is only used for testing, there should be a PStar at the end of match clause
   x1 = 1
   x2 = true
   x3 = {a:x1; b:x2}
   x4 = match x3 with
        | {a:int; b:int} -> x5 = 1*)
let in6 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt); (Lab "b", PInt)],
                                                    [Clause (Ident "x5", Int 1)])]))];;
let test6 = assert_equal false (test_wrapper in6);;

(* Test atomic typing with plus
   x1 = 1
   x2 = true
   x3 = x1 + x2
   x4 = match x2 with
        | true -> x5 = 1
   x6 = match x3 with
        | int -> x7 = 2
        | * -> x8 = 3 *)

let in7 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Plus (Ident "x1", Ident "x2"));
           Clause (Ident "x4", Match (Ident "x2", [(PTrue, [Clause (Ident "x5", Int 1)])]));
           Clause (Ident "x6", Match (Ident "x3", [(PInt, [Clause (Ident "x7", Int 2)]);
                                                   (PStar, [Clause (Ident "x8", Int 3)])]))];;
let test7 = assert_equal false (test_wrapper in7);;

(* test clauses inside function body
   x1 = Function x2 -> x3 = 1
                       x4 = match x3 with
                            | Int -> x5 = 1
                            | * -> x6 = 2
   x7 = 2
   x8 = x1 x7*)
let in8 = [Clause (Ident "x1", Function (Ident "x2", [Clause (Ident "x3",Int 1);
                                                      Clause (Ident "x4", Match (Ident "x3", [(PInt, [Clause (Ident "x5", Int 1)]);
                                                                                              (PStar, [Clause (Ident "x6", Int 2)])]))]));
           Clause (Ident "x7", Int 2);
           Clause (Ident "x8", Appl (Ident "x1", Ident "x7"))];;
let test8 = assert_equal true (test_wrapper in8);;

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
let in9 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Record [(Lab "a", Ident "x1")]);
           Clause (Ident "x3", Match (Ident "x2", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x4", Int 2)]);
                                                   (PStar, [Clause (Ident "x5", Int 3)])]));
           Clause (Ident "x6", Match (Ident "x2", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x7", Int 4)]);
                                                   (PStar, [Clause (Ident "x8", Int 5)])]))];;
let test9 = assert_equal true (test_wrapper in9);;

(* Test intersection of different tags and forward propagation
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
let in10 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt)],[Clause (Ident "x5", Int 2)]);(PStar,[Clause (Ident "x6", Int 3)])]));
           Clause (Ident "x7", Match (Ident "x3", [(PRecord [(Lab "b", PTrue)],[Clause (Ident "x8", Int 4)]);(PStar,[Clause (Ident "x9", Int 5)])]));
           Clause (Ident "x10", Var (Ident "x3"))];;
let test10 = assert_equal true (test_wrapper in10);;

(* Test empty field after intersection
   x1 = 1;
   x2 = {a:x1};
   x3 = match x2 with
   | {a:int} -> x4 = 1
   | * -> x5 = 2
   x6 = match x2 with
   | {a:true} -> x7 = 3
   | * -> x8 = 4*)
let in11 = [Clause (Ident "x1", Int 1);
            Clause (Ident "x2", Record [(Lab "a", Ident "x1")]);
            Clause (Ident "x3", Match (Ident "x2", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x4", Int 1)]);
                                                    (PStar, [Clause (Ident "x5", Int 2)])]));
            Clause (Ident "x6", Match (Ident "x2", [(PRecord [(Lab "a", PTrue)], [Clause (Ident "x7", Int 3)]);
                                                    (PStar, [Clause (Ident "x8", Int 4)])]))];;
let test11 = assert_equal true (test_wrapper in11);;

(* test AMB
   x1 = true or false
   x2 = match x1 with
        | true -> x3 = 1
        | false -> x4 = 2
        | * -> x5 = 3
*)

let in12 = [Clause (Ident "x1", Amb [True;False]);
           Clause (Ident "x2", Match (Ident "x1", [(PTrue, [Clause (Ident "x3", Int 1)]);
                                                   (PFalse, [Clause (Ident "x4", Int 2)]);
                                                   (PStar, [Clause (Ident "x5", Int 3)])]))];;
let test12 = assert_equal true (test_wrapper in12);;

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
let in13 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt)],[Clause (Ident "x5", Int 2)]);(PStar,[Clause (Ident "x6", Int 3)])]));
           Clause (Ident "x7", Match (Ident "x3", [(PRecord [(Lab "b", PTrue)],[Clause (Ident "x8", Int 4)]);(PStar,[Clause (Ident "x9", Int 5)])]));
           Clause (Ident "x10", Var (Ident "x3"))];;
let test13 = assert_equal true (test_wrapper in13);;

(* Test nested record
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
let in14 = [Clause (Ident "x0", Int 1);
           Clause (Ident "x1", Var (Ident "x0"));
           Clause (Ident "x2", True);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Int 3);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PTrue)])], [Clause (Ident "x7", Int 7)]);
                                                   (PStar, [Clause (Ident "x8", Int 8)])]))];;
let test14 = assert_equal true (test_wrapper in14);;

(* Test backward and forward propagation
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
let in15 = [Clause (Ident "x1", Amb [True; False]);
            Clause (Ident "x2", Match (Ident "x1", [(PTrue, [Clause (Ident "x3", Int 1);
                                                             Clause (Ident "x31", Match (Ident "x3", [(PInt, [Clause (Ident "x32", Int 1)]);
                                                                                                      (PStar, [Clause (Ident "x33", Int 2)])]));
                                                             Clause (Ident "x34", Var (Ident "x3"))]);
                                                    (PFalse, [Clause (Ident "x4", True);
                                                              Clause (Ident "x41", Match (Ident "x4", [(PTrue, [Clause (Ident "x42", Int 3)]);
                                                                                                       (PStar, [Clause (Ident "x43", Int 4)])]));
                                                              Clause (Ident "x44", Var (Ident "x4"))]);
                                                    (PStar, [Clause (Ident "x5", Int 5)])]))];;
let test15 = assert_equal true (test_wrapper in15);;

(* Test projection
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

let in16 = [Clause (Ident "x1", Record []);
          Clause (Ident "x2", Int 3);
          Clause (Ident "x3", Record [(Lab "c", Ident "x1");(Lab "d", Ident "x2")]);
          Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "c", PInt); (Lab "d", PStar)],[Clause (Ident "x5", Int 1)]);
                                                  (PRecord [(Lab "d", PStar)], [Clause (Ident "x6", Int 2)]);
                                                  (PStar, [Clause (Ident "x7", Int 3)])]))];;
let test16 = assert_equal true (test_wrapper in16);;

(* Tests that should fail but did not *)

(* Needs implementation of operator tags propagation
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
let in101 = [Clause (Ident "x1", Int 1);
            Clause (Ident "x2", Int 2);
            Clause (Ident "x3", Plus (Ident "x1", Ident "x2"));
            Clause (Ident "x4", Match (Ident "x3", [(PTrue, [Clause (Ident "x5", Int 1)]);
                                                    (PStar, [Clause (Ident "x6", Int 2)])]))];;
(* let test101 = assert_equal false (test_wrapper in101);; *)

(* Test record projection with unspecified field
   x1 = 1
   x2 = true
   x3 = {a:x1; b:x2}
   x4 = match x3 with
          | {a:int} -> x5 = 1
          | {b:true} -> x6 = 2
          | * -> x7 = 3
   Fails because of record soundness *)
let in102 = [Clause (Ident "x1", Int 1);
            Clause (Ident "x2", True);
            Clause (Ident "x3", Record [(Lab "a", Ident "x1");(Lab "b", Ident "x2")]);
            Clause (Ident "x4", Match (Ident "x3", [(PRecord [(Lab "a", PInt)], [Clause (Ident "x5", Int 1)]);
                                                    (PRecord [(Lab "b", PTrue)], [Clause (Ident "x6", Int 2)]);
                                                    (PStar, [Clause (Ident "x7", Int 3)])]))];;
(* let test102 = assert_equal true (test_wrapper in102);; *)

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

let in103 = [Clause (Ident "x1", Record []);
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
(* let test103 = assert_equal true (test_wrapper in103);; *)

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
let in104 = [Clause (Ident "x1", Int 1);
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
(* let test104 = assert_equal true (test_wrapper in104);; *)

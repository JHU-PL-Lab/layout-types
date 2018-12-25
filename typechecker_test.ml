open OUnit;;
open Layout;;
open Typechecker;;

let test_wrapper input sound rou delta =
  let (sound1, rou1, delta1) = typecheck input
  in assert_equal sound sound1;assert_equal rou rou1; assert_equal delta delta1;;

(*
x1:Int = 1
x2:Int = 2
x3:Int = x1+x2

sound = true
rou = []
delta = []
*)
let in1 = [TaggedClause (Ident "x1",Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2",Tau [( T (LInt, []), Nonce 2)], Int 2);
           TaggedClause (Ident "x3",Tau [( T (LInt, []), Nonce 3)], Plus (Ident "x1", Ident "x2"))];;
let test1 = test_wrapper in1 true [] [];;

(*
x1:True = True
x2:False = False
x3:[True;False] = x1 && x2

sound = True
rou = []
delta = []
*)
let in2 = [TaggedClause (Ident "x1",Tau [( T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x2",Tau [( T (LFalse, []), Nonce 2)], False);
           TaggedClause (Ident "x3",Tau [( T (LTrue, []), Nonce 3); ( T (LFalse, []), Nonce 4)], And (Ident "x1", Ident "x2"))];;
let test2 = test_wrapper in2 true [] [];;

(*
x1:Int = 1
x2:Int = x1

sound = true
rou = []
delta = []
*)
let in3 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LInt, []), Nonce 1)], Var(Ident "x1"))];;
let test3 = test_wrapper in3 true [] [];;

(*
x1:[(LInt-{}, Nonce 1)] = 1
x2:[(LTrue-{}, Nonce 2)] = True
x3 : [({a:Int; b: True}-{}, Nonce 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

sound = true
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in4 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 4)], Int 3)])]))];;
let test4 = test_wrapper in4 true [(Ident "x3", [([Nonce 1; Nonce 2], 3)])] [(Ident "x4", [(Nonce 3, 1)])];;


(*
x1:LInt = 1
x2:LTrue = True
x3 : [{a:LStar};({b:LStar} - {c:LStar})] = {a:x1; b:x2}
x4 :LInt = Match x3 with
      | {PRecord [a:PStar; c: PStar]} -> x5:LInt = Int 3

sound = false
rou = [(x3, [(1,2)->3])]
delta = []
*)

let in5 = [TaggedClause (Ident "x1", Tau [( T (LInt, []), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, []), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LStar)], []), Nonce 3); (T (LRecord [(Lab "b", LStar)], [LRecord [(Lab "c", LStar)]]), Nonce 6)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PStar);(Lab "c", PStar)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 4)], Int 3)])]))];;
let test5 = test_wrapper in5 false [(Ident "x3", [([Nonce 1; Nonce 2], 3)])] [];;

(*
x1 : LTrue = True
x2 : LFalse = false
x3 : {q:LStar} - [{q:LInt}, {q:LFalse}] = {q:x1}
x4 : {r:LStar} - [{r: LInt}] = {r: x2}
x5 : {a: {q:LStar}; b: {r:LStar}} - [{a: {q:LInt}}; {a:{q:LFalse}};
                                      {b:{r:LInt}}] = {a: x3, b:x4}

sound = true
rou = [(x3, [(1)-> 3]); (x4, [(2)-> 4]);
 (x5, [(3,4)->5])]
delta = []
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
let test6 = test_wrapper in6 true [(Ident "x3", [([Nonce 1], 3)]); (Ident "x4", [([Nonce 2], 4)]);
                                   (Ident "x5", [([Nonce 3; Nonce 4], 5)])] [];;

(*
x1 : LTrue = True
x3 : {q:LStar} - [{q:LInt}, {q:LFalse}] = {q:x1}

sound = True
rou: [(x3, [(1)->3])]
delta: []
*)

let in7 = [TaggedClause (Ident "x1", Tau [(T (LTrue, []), Nonce 1)], True);
           TaggedClause (Ident "x3", Tau [(T (LRecord [(Lab "q", LStar)],[LRecord [(Lab "q", LInt)];LRecord [(Lab "q", LFalse)]]), Nonce 3)], Record [(Lab "q", Ident "x1")]);
          ];;
let test7 = test_wrapper in7 true [(Ident "x3", [([Nonce 1], 3)])] [];;

(*
x1:[(Int-{}, Nonce 1);(True-{}, Nonce 2)] = 1
x2:[(True-{}, Nonce 3);(False-{}, Nonce 4)] = True
x3 : [({a:Int; b: True}-{}, Nonce 5);
      ({a:Int; b: False}-{}, Nonce 6);
      ({a:True; b: True}-{}, Nonce 7);
      ({a:True; b: False}-{}, Nonce 8);] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 9)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:[(LInt-{}, Nonce 10)] = Int 3
      | {PRecord [a:PTrue]} -> x6:[(LInt-{}, Nonce 9)] = Int 4

sound = true
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
                                                                    [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 9)], Int 3)]);
                                                                     (PRecord [(Lab "a", PTrue)], [TaggedClause (Ident "x6", Tau [( T (LInt, []), Nonce 11)], Int 4)])]))];;
let test8 = test_wrapper in8 true [(Ident "x3",
                                    [([Nonce 1; Nonce 3], 5); ([Nonce 1; Nonce 4], 6);
                                     ([Nonce 2; Nonce 3], 7); ([Nonce 2; Nonce 4], 8)])]
    [(Ident "x4", [(Nonce 5, 1); (Nonce 6, 1); (Nonce 7, 2); (Nonce 8, 2)])];;


(*
x1:[(LInt-{LTrue}, Nonce 1)] = 1
x2:[(LTrue-{LFalse}, Nonce 2)] = True
x3 : [({a:Int; b: True}-{}, Nonce 3)] = {a:x1; b:x2}
x4 :[(LInt-{}, Nonce 4)] = Match x3 with
      | {PRecord [a:PInt]} -> x5:LInt = Int 3

sound = true
rou:[(x3, [(1,2)->3])]
delta: [(x4, [(3->1)])]
*)
let in9 = [TaggedClause (Ident "x1", Tau [( T (LInt, [LTrue]), Nonce 1)], Int 1);
           TaggedClause (Ident "x2", Tau [( T (LTrue, [LFalse]), Nonce 2)], True);
           TaggedClause (Ident "x3", Tau [( T (LRecord [(Lab "a", LInt); (Lab "b", LTrue)], []), Nonce 3)], Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           TaggedClause (Ident "x4", Tau [( T (LInt, []), Nonce 4)], TaggedMatch (Ident "x3", [(PRecord [(Lab "a", PInt)], [TaggedClause (Ident "x5", Tau [( T (LInt, []), Nonce 4)], Int 3)])]))];;
let test9 = test_wrapper in9 true [(Ident "x3", [([Nonce 1; Nonce 2], 3)])] [(Ident "x4", [(Nonce 3, 1)])];;

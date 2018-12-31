open OUnit;;
open Layout;;
open Setinterpreter;;

let test_wrapper input res df=
  let (res1, df1) = eval input
  in assert_equal res res1; assert_equal df (!df1);;

(*
x1 = 1 or 2
x2 = 2
x3 = x1+x2
return: 3 or 4
dataflow = []
*)
let in1 = [Clause (Ident "x1", Amb [Int 1; Int 2]);
           Clause (Ident "x2", Int 2);
           Clause (Ident "x3", Plus (Ident "x1", Ident "x2"))];;
let test1 = test_wrapper in1 (Amb [Int 3;Int 4]) [];;

(*
x1 = 1 or True
x2 = not x1
return : empty or false
dataflow = []
 *)

let in2 = [Clause (Ident "x1", Amb [Int 1; True]);
           Clause (Ident "x2", Not (Ident "x1"))];;
let test2 = test_wrapper in2 (Amb [Empty; False]) [];;

(*
x1 = 1 or True
x2 = true or False
x4 = x1 or x2
return: empty or empty or true or false
dataflow = []
 *)
let in3 = [Clause (Ident "x1", Amb [Int 1; True]);
           Clause (Ident "x2", Amb [True; False]);
           Clause (Ident "x3", Or(Ident "x1", Ident "x2"))];;
let test3 = test_wrapper in3 (Amb [Empty; Empty; True; True]) [];;

(*
x1 = 1 or true
x2 = 1 or 2
x3 = x1 == x2
return: true or false or empty or empty
dataflow = [] *)
let in4 = [Clause (Ident "x1", Amb [Int 1; True]);
           Clause (Ident "x2", Amb [Int 1; Int 2]);
           Clause (Ident "x3", Equals(Ident "x1", Ident "x2"))];;
let test4 = test_wrapper in4 (Amb [True; False; Empty; Empty]) [];;

(*
x1 = 1
x2 = Fun y -> {
        xx = 2
        xx2 = xx+y
      }
x3 = x2 x1
same as: (Fun y -> y+2) 1
return: 3
dataflow = [x3 -> xx2; y -> x1]  x2 here is a closure!
*)
let in5 = [Clause(Ident "x1", Int 1);
           Clause(Ident "x2", Function (Ident "y", [Clause(Ident "xx", Int 2);
                                                    Clause(Ident "xx2", Plus (Ident "xx", Ident "y"))]));
           Clause (Ident "x3", Appl(Ident "x2", Ident "x1"))];;
let test5 = test_wrapper in5 (Amb [Int 3]) [(Ident "x3", Var (Ident "xx2")); (Ident "y", Var (Ident "x1"))];;

(*
x1 = 1
x2 = {a:x1}
x3 = x2.a
return: 1
dataflow = [x3->x1]
*)
let in6 = [Clause(Ident "x1", Int 1);
           Clause(Ident "x2", Record [(Lab "a", Ident "x1")]);
           Clause (Ident "x3", Proj (Ident "x2", Lab "a"))];;
let test6 = test_wrapper in6 (Amb [Int 1]) [(Ident "x3", Var (Ident "x1"))];;

(*
x1 = 1
x2 = Match x1 with
      | PInt -> {
            x3 = 2
        }
return: 2
dataflow = {x2 -> x3}
*)
let in7 = [Clause(Ident "x1", Int 1);
           Clause (Ident "x2", Match (Ident "x1", [(PInt, [Clause (Ident "x3", Int 2)])]))];;
let test7 = test_wrapper in7 (Amb [Int 2]) [(Ident "x2", Var (Ident "x3"))];;

(*
x1 = 1 or 2
x2 = match x1 with
      | int -> x3 = 2
returns : 2 or 2
dataflow = [x2 -> x3; x2->x3]*)
let in8 = [Clause(Ident "x1", Amb [Int 1; Int 2]);
           Clause (Ident "x2", Match (Ident "x1", [(PInt, [Clause (Ident "x3", Int 2)])]))];;
let test8 = test_wrapper in8 (Amb [Int 2; Int 2]) [(Ident "x2", Var(Ident "x3"));(Ident "x2", Var(Ident "x3"))];;

(*
x1 = 1
x2 = {a:x1}
x3 = Match x2 with
    {a:PInt} -> {
              x4 = 4
          }
return: 4
dataflow = [x3->x4]
*)
let in9 = [Clause(Ident "x1", Int 1);
           Clause (Ident "x2", Record [(Lab "a", Ident "x1")]);
           Clause (Ident "x3", Match (Ident "x2", [PRecord [(Lab "a", PInt)],[Clause (Ident "x4", Int 4)]]))];;
let test9 = test_wrapper in9 (Amb [Int 4]) [(Ident "x3", Var (Ident "x4"))]

(*
x1 = 1
x2 = 2
x3 = {a:x1, b: x2}
x4 = Match x3 with
      | {a:PInt} -> {x5 = 4}
return: 4
dataflow = [x4->x5]
*)
let in10 = [Clause(Ident "x1", Int 1);
           Clause(Ident "x2", Int 2);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1");(Lab "b", Ident "x2")]);
           Clause (Ident "x4", Match (Ident "x3", [PRecord [(Lab "a", PInt)],[Clause (Ident "x5", Int 4)]]))];;
let test10 = test_wrapper in10 (Amb [Int 4]) [(Ident "x4", Var (Ident "x5"))];;

(*
x1 = 1 or 2
x2 = 3 or False
x3 = {a:x1, b: x2}
x4 = True
x5 = {c:x3, d:x4}
x6 = Match x5 with
      | {c: {a:Int; b:false}, d: True} -> {x7 = 4}
return: empty or 4 or empty or 4
global_env = [x6 -> x7; x6->x7]
*)
let in11 = [Clause (Ident "x1", Amb [Int 1; Int 2]);
            Clause (Ident "x2", Amb [Int 3; False]);
            Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
            Clause (Ident "x4", True);
            Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
            Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PFalse)]); (Lab "d", PTrue)], [Clause (Ident "x7", Int 4)])]))
           ];;
let test11 = test_wrapper in11 (Amb [Empty; Int 4; Empty; Int 4]) [(Ident "x6", Var (Ident "x7"));(Ident "x6", Var (Ident "x7"))];;


(*
 x1 = Fun x -> {
              x2 = Fun y -> {
                          x3 = x+y
                        }
            }
x4 = 1 or 2
x5 = 10 or 20
x6 = x1 x4
x7 = x6 x5
return: 11 or 21 or 12 or 22
 *)
let in12 = [Clause (Ident "x1", Function (Ident "x",
                                          [Clause (Ident "x2", Function (Ident "y",
                                                                         [Clause (Ident "x3", Plus(Ident "x", Ident "y"))]))]));
            Clause (Ident "x4", Amb [Int 1; Int 2]);
            Clause (Ident "x5", Amb [Int 10; Int 20]);
            Clause (Ident "x6", Appl (Ident "x1", Ident "x4"));
            Clause (Ident "x7", Appl (Ident "x6", Ident "x5"))];;
let test12 = test_wrapper in12 (Amb [Int 11; Int 21; Int 12; Int 22]) [(Ident "x7", Var (Ident "x3")); (Ident "y", Var (Ident "x5"));
                                                                       (Ident "x6", Var (Ident "x2")); (Ident "x", Var (Ident "x4"));
                                                                       (Ident "x7", Var (Ident "x3")); (Ident "y", Var (Ident "x5"));
                                                                       (Ident "x6", Var (Ident "x2")); (Ident "x", Var (Ident "x4"));
                                                                       (Ident "x7", Var (Ident "x3")); (Ident "y", Var (Ident "x5"));
                                                                       (Ident "x6", Var (Ident "x2")); (Ident "x", Var (Ident "x4"));
                                                                       (Ident "x7", Var (Ident "x3")); (Ident "y", Var (Ident "x5"));
                                                                       (Ident "x6", Var (Ident "x2")); (Ident "x", Var (Ident "x4"))];;

(*
x1 = 1
x2 = x1
return: 1
dataflow = [x2->x1]
*)
let in13 = [Clause(Ident "x1", Int 1);
            Clause(Ident "x2", Var (Ident "x1"))];;
let test13 = test_wrapper in13 (Amb [Int 1]) [(Ident "x2", Var (Ident "x1"))];;

(*
x1 = 1;
x2 = 2;
x3 = {a:x1, b:x2}
x4 = 3
x5 = {c:x3, d: x4}
x6 = Match x5 with
  | {c:{a:PInt, b:PTrue}} -> x7=7
  | PStar -> x8 = 8
return: 8
dataflow: [x6 -> x8]
*)

let in14 = [Clause (Ident "x1", Int 1);
           Clause (Ident "x2", Int 2);
           Clause (Ident "x3", Record [(Lab "a", Ident "x1"); (Lab "b", Ident "x2")]);
           Clause (Ident "x4", Int 3);
           Clause (Ident "x5", Record [(Lab "c", Ident "x3"); (Lab "d", Ident "x4")]);
           Clause (Ident "x6", Match (Ident "x5", [(PRecord [(Lab "c", PRecord [(Lab "a", PInt); (Lab "b", PTrue)])], [Clause (Ident "x7", Int 7)]);
                                                   (PStar, [Clause (Ident "x8", Int 8)])]))];;
let test14 = test_wrapper in14 (Amb [Int 8]) [(Ident "x6", Var (Ident "x8"))];;

(*
x1 = Fun f ->
    y = Fun x -> {
                x2 = 0;
                x3 = Equals (x, x2)
                x4 = Match x3 with
                | PTrue -> 0
                | PFalse -> {
                        x5 = f f
                        x11 = 1;
                        x6 = x-x11;
                        x7 = x5 x6
                        x8 = x + x7
                        }
          }
x9 = x1 x1
x10 = 6
x12 = x9 x10

should return 21
*)

let in15 = [Clause (Ident "x1", Function (Ident "f",
                                         [Clause (Ident "y", Function (Ident "x",
                                                                       [Clause (Ident "x2", Int 0);
                                                                        Clause (Ident "x3", Equals (Ident "x", Ident "x2"));
                                                                        Clause (Ident "x4", Match (Ident "x3",
                                                                                                   [(PTrue, [Clause (Ident "xx", Int 0)]);
                                                                                                    (PFalse, [Clause (Ident "x5", Appl (Ident "f", Ident "f"));
                                                                                                              Clause (Ident "x11", Int 1);
                                                                                                              Clause (Ident "x6", Minus (Ident "x", Ident "x11"));
                                                                                                              Clause (Ident "x7", Appl (Ident "x5", Ident "x6"));
                                                                                                              Clause (Ident "x8", Plus (Ident "x", Ident "x7"))])]))]))]));
           Clause (Ident "x9", Appl (Ident "x1", Ident "x1"));
           Clause (Ident "x10", Int 6);
           Clause (Ident "x12", Appl (Ident "x9", Ident "x10"))];;

let test15 = test_wrapper in15 (Amb [Int 21]) [(Ident "x4", Var (Ident "xx")); (Ident "x7", Var (Ident "x4"));
                                          (Ident "x", Var (Ident "x6")); (Ident "x5", Var (Ident "y"));
                                          (Ident "f", Var (Ident "f")); (Ident "x4", Var (Ident "x8"));
                                          (Ident "x7", Var (Ident "x4")); (Ident "x", Var (Ident "x6"));
                                          (Ident "x5", Var (Ident "y")); (Ident "f", Var (Ident "f"));
                                          (Ident "x4", Var (Ident "x8")); (Ident "x7", Var (Ident "x4"));
                                          (Ident "x", Var (Ident "x6")); (Ident "x5", Var (Ident "y"));
                                          (Ident "f", Var (Ident "f")); (Ident "x4", Var (Ident "x8"));
                                          (Ident "x7", Var (Ident "x4")); (Ident "x", Var (Ident "x6"));
                                          (Ident "x5", Var (Ident "y")); (Ident "f", Var (Ident "f"));
                                          (Ident "x4", Var (Ident "x8")); (Ident "x7", Var (Ident "x4"));
                                          (Ident "x", Var (Ident "x6")); (Ident "x5", Var (Ident "y"));
                                          (Ident "f", Var (Ident "f")); (Ident "x4", Var (Ident "x8"));
                                          (Ident "x7", Var (Ident "x4")); (Ident "x", Var (Ident "x6"));
                                          (Ident "x5", Var (Ident "y")); (Ident "f", Var (Ident "f"));
                                          (Ident "x4", Var (Ident "x8")); (Ident "x12", Var (Ident "x4"));
                                          (Ident "x", Var (Ident "x10")); (Ident "x9", Var (Ident "y"));
                                          (Ident "f", Var (Ident "x1"))];;

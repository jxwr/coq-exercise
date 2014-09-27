(* *)

(* p159 6.4 多态，冒号前的部分为类型参数，冒号后为实际类型 *)
(* 需要注意：Inductive不止用来定义类型，也定义函数 *)
Inductive sorted (A : Set) (R : A -> A -> Prop) : list A -> Prop :=
  | sorted0 : sorted A R nil
  | sorted1 : forall x : A, sorted A R (cons x nil)
  | sorted2 : forall (x y : A) (l : list A),
                R x y ->
                sorted A R (cons y l) -> sorted A R (cons x (cons y l)).

(* 隐式参数让编译器自动推导，在使用时要省略 *)
Implicit Arguments sorted [A].

(* 8.4.2 *)
Require Import ZArith.
Open Scope Z_scope.

Section little_semantics.
  Variables Var aExp bExp : Set.

  Inductive inst : Set :=
    | Skip : inst
    | Assign : Var -> aExp -> inst
    | Sequence : inst -> inst -> inst
    | WhileDo : bExp -> inst -> inst.
  
  Variable
    (state : Set)
    (update : state -> Var -> Z -> option state)
    (evalA : state -> aExp -> option Z)
    (evalB : state -> bExp -> option bool).

  Inductive exec : state -> inst -> state -> Prop :=
    | execSkip : forall s : state, exec s Skip s
    | execAssign : 
        forall (s s1 : state) (v : Var) (n : Z) (a : aExp),
          evalA s a = Some n -> update s v n = Some s1 -> 
          exec s (Assign v a) s1
    | execSequence :
        forall (s s1 s2 : state) (i1 i2 : inst),
          exec s i1 s1 -> exec s1 i2 s2 ->
          exec s (Sequence i1 i2) s2
    | execWhileFalse :
        forall (s : state) (i : inst) (e : bExp),
          evalB s e = Some false -> exec s (WhileDo e i) s
    | execWhileTrue :
        forall (s s1 s2 : state) (i : inst) (e : bExp),
          evalB s e = Some true -> 
          exec s i s1 ->
          exec s1 (WhileDo e i) s2 ->
          exec s (WhileDo e i) s2.
End little_semantics.

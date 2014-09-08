(* Commutativity of Addition in Coq *)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint plus (x y : Nat) : Nat :=
  match x with
    | O => y
    | S x' => S (plus x' y)
  end.

Lemma plus_O (x : Nat) : plus x O = x.
Proof.
  induction x.
  - simpl. reflexivity. 
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_S (x y : Nat) : plus x (S y) = S (plus x y).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plust_com (x y : Nat) : plus x y = plus y x.
Proof.
  induction x.
  - simpl. rewrite plus_O. reflexivity.
  - simpl. rewrite IHx. rewrite plus_S. reflexivity.
Qed.

Print not.

(* Triple Negation *)
Goal forall X : Prop, ~ ~ ~ X -> ~ X.
Proof.
  exact (fun X A B => A (fun C => C B)).
Qed.

Goal forall X Y : Prop, X -> Y -> X.
Proof.
  intros X Y A B. exact A.
Qed.

Goal forall X Y : Prop, X -> Y -> X.
Proof.
  (* intros X Y. exact (fun A B => A). *)
  exact (fun X Y A B => A).
Qed.

(* use fun *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z.
  exact (fun A B X => B (A X)).
Qed.

(* use apply, 以结果为目标选择应用项 *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z A B C.
  apply B.
  apply A.
  exact C.
Qed.

(* normal proof *)
Goal forall X Y Z : Prop, (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof.
  intros.
  apply H.
  exact H1.
  apply H0.
  exact H1.
Qed.

(* use fun *)
Goal forall X Y Z : Prop, (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof.
  intros X Y Z.
  exact (fun A B C => A C (B C)).
Qed.

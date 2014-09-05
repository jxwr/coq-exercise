
(* nat_scope *)
Check plus.
Check S.
Check 4*10.

(* fun *)
Definition fourfold := 
  fun n => let m := n * n in m * m.

Definition double n := n * n.
Definition fourfold_short n := let m := double n in double m.

Check fourfold.

(* global *)
Parameter max_int : nat.

(* section 定义块，同时也辅助定义函数 *)
Section bin_def.
  (* local *)
  Variable a b : nat.
  Definition c := a + b.
End bin_def.

Print c.

Theorem imp_trans (p q r: Prop): 
  (p -> q) -> (q -> r) -> p -> r.
Proof.
  intros.
  apply H0.
  apply H.
  exact H1. (* or assumption *)
Qed.

Print imp_trans.

Lemma l_35_36 :
  forall n : nat, 7*5 < n -> 6*6 <= n.
Proof.
  intros.
  exact H.
Qed.


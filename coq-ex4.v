(* p52 ex3.2 *)

Parameter P Q R T : Prop.

Lemma id_P : P -> P.
Proof.
  intro.
  assumption.
Qed.

Lemma id_PP : (P -> P) -> (P -> P).
Proof.
  intros H p.
  assumption.
Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  exact (fun X Y Z => Y (X Z)).
Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros.
  apply H; assumption.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros.
  apply H; assumption.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros.
  apply H; assumption.
Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros.
  apply H1.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

Lemma weak_peirce: ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intros.
  assumption.
Qed.

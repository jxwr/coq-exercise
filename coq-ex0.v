Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop):
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  split.
  intros [y [H1 H2]].
  split.
  assumption.
  exists y.
  assumption.
  intros [H1 [y H2]].
  exists y.
  split.
  assumption.
  assumption.
Qed.

Parameter A B C : Set.

(* f : A -> B -> C *)
Definition curry (f : A * B -> C) := fun a => fun b => f (a, b).
Definition uncurry (g : A -> B -> C) := fun p => g (fst p) (snd p).

Theorem prf0 : forall f a b, uncurry (curry f) (a, b)= f (a, b).
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  reflexivity.
Qed.

Theorem prf1 : forall g a b, curry (uncurry g) a b = g a b.
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  auto.
Qed.


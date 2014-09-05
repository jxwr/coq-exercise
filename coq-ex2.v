(* Inductive *)

Inductive bool : Set := true : bool | false : bool.

Theorem bool_equal : 
  forall b : bool, b = true \/ b = false.
Proof.
  intro m; pattern m.
  apply bool_ind; auto.
Qed.

Inductive month : Set := 
  January | February | March | April | May | June | July 
  | Auguest | September | October | November | December.

Definition month_length (leap : bool) (m : month) : nat := 
  match m with
    | February => if leap then 29 else 28
    | April => 30 | June => 30 | September => 30 | November => 30
    | other => 31
  end.

Theorem month_at_least_28:
  forall (leap : bool) (m : month), 28 <= month_length leap m.
Proof.
  intros leap m; case m; simpl; auto.
  case leap; auto.
Qed.

(* maybe *)
Inductive maybe (A : Set) : Set :=
  Just : A -> maybe A | Nothing : maybe A.

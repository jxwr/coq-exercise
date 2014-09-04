
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
Definition divides (b q r a : nat) := a = b * q + r.

(* Stating the Division Theorem *)
Theorem division_theorem_exists : forall (a b : nat),
  b > 0 -> 
  exists q r, a = q * b + r /\ 0 <= r < b.
Proof.
Admitted.

Theorem division_theorem : forall a b : nat,
  b > 0 ->
  exists q r : nat, a = b * q + r /\ 0 <= r < b /\
  forall q' r', a = b * q' + r' -> 0 <= r' < b -> q' = q /\ r' = r.
Proof.
Admitted. 

Require Import Nat Arith.

(* Definition of factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

Lemma factorial_le_n_to_n: forall n, 2 < n -> factorial n <= n^n.
Proof.
Admitted.


Lemma factorial_le_two_pow_n: forall n, 2 < n -> 2^n <= factorial n.
Proof.
Admitted.

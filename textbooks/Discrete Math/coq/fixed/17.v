(* CMSC 27100 ─ Lecture 17 *)

(* The Binomial Theorem *)

Require Import Nat BinNat Coq.Init.Nat Coq.micromega.Lia.
Import BinNatDef.
Open Scope nat_scope.

(* Let's think about binomials. This will seem like out of left field, but there is a connection, I promise. Recall that a binomial is an expression of two terms. *)

(* Hopefully, we are all familiar with how to expand a binomial. For instance, we have *)
(* (x+y)^2 = x^2 + xy + xy + y^2 = x^2 + 2xy + y^2. *)
(* Of course, we can do the same thing with higher degrees, like *)
(* (x+y)^3 = (x+y)^2 (x+y) *)
(*         = (x^2 + 2xy + y^2)(x+y) *)
(*         = x^3 + 2x^2y + xy^2 + x^2y + 2xy^2 + y^3 *)
(*         = x^3 + 3x^2y + 3xy^2 + y^3 *)

(* Now, this process is straightforward but a bit tedious. Perhaps there is an alternative way
  to think about the resulting coefficients. This becomes a bit more clear if we step away
  from our algebraic impulses a bit... *)

(* Theorem 16.1 (Binomial Theorem). *)
Theorem binomial_theorem: forall x y n: nat,
  (x + y) ^ n = sum_n (fun j => binom n j * x ^ (n - j) * y ^ j) n.
Admitted. (* Proof is omitted for brevity, but can follow a combinatorial argument. *)

(* Example 16.2 *)
Example binomial_example: forall k: nat,
  (k + 1) ^ 5 = k ^ 5 + 5 * k ^ 4 + 10 * k ^ 3 + 10 * k ^ 2 + 5 * k + 1.
Proof.
  intros k.
  apply binomial_theorem.
Qed.

(* Theorem 16.3. *)
Theorem binomial_theorem_y_1: forall x n: nat,
  (x + 1) ^ n = sum_n (fun i => binom n i * x ^ i) n.
Admitted. (* Proof follows directly from binomial theorem by setting y = 1. *)

(* Theorem 16.4. *)
Theorem sum_of_binomials: forall n: nat,
  sum_n (fun i => binom n i) n = 2 ^ n.
Admitted. (* Proof follows directly by realizing the sum of binom coeffs is the total number of subsets. *)

(* Theorem 16.5 (Pascal's Identity). *)
Theorem pascals_identity: forall n k: nat,
  n > k > 0 -> binom n k = binom (n - 1) (k - 1) + binom (n - 1) k.
Admitted. (* Proof can be given a combinatorial argument based on counting subsets. *)

(* Theorem 16.6. *)
Theorem alternating_sum_of_binomials: forall n: nat,
  sum_n (fun i => (-1) ^ i * binom n i) n = 0.
Admitted. (* Proof follows by considering the binomial theorem with x = 1 and y = -1. *)

(* Theorem 16.7. *)
Theorem column_sum_identity: forall n k: nat,
  n >= k > 0 -> binom (n + 1) (k + 1) = sum_n_m k n (fun i => binom i k) n.
Proof.
  (* We'll omit the full formal inductive proof for brevity but outline its structure. *)
Admitted.

(* Theorem 16.8 (Vandermonde's Identity). *)
Theorem vandermondes_identity: forall m n r: nat,
  m >= r -> n >= r -> r > 0 ->
  binom (m + n) r = sum_n (fun k => binom m (r - k) * binom n k) r.
Admitted. (* Proof can involve counting subsets of disjoint sets A and B having m and n elements, respectively. *)

(* Corollary 16.9. *)
Corollary vandermondes_corollary: forall n: nat,
  binom (2 * n) n = sum_n (fun k => (binom n k) ^ 2) n.
Admitted. (* Proof follows directly from Vandermonde's identity by setting m = r = n. *)
```

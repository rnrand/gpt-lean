```coq
(* This Coq script is based on the lecture notes of CMSC 27100 - Lecture 7, covering basic concepts of divisibility in number theory, proofs of several theorems on divisibility, and an introduction to the Division Theorem. *)

Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Definition 6.1: Divisibility *)
(* Let a, b be integers. We say that a divides b, written a | b, if there exists an integer n such that a * n = b. We also say that b is a multiple of a. *)

Definition divides (a b : Z) : Prop := exists n : Z, a * n = b.

Notation "a | b" := (divides a b) (at level 0).

(* Theorem 6.2: If a | b and a | c, then a | (b + c). *)
Lemma divisibility_addition : forall a b c : Z, a | b -> a | c -> a | (b + c).
Proof.
  intros a b c [m Hm] [n Hn]. (* Introduce arbitrary integers a, b, c and assume a | b and a | c. *)
  exists (m + n). rewrite Hm, Hn. ring.
Qed.

(* Theorem 6.3: If a | b, then a | bc. *)
Lemma divisibility_multiplication : forall a b c : Z, a | b -> a | (b * c).
Proof.
  intros a b c [n Hn].
  exists (n * c). rewrite Hn. ring.
Qed.

(* Theorem 6.4: Transitivity of divides relation. If a | b and b | c, then a | c. *)
Lemma divisibility_transitivity : forall a b c : Z, a | b -> b | c -> a | c.
Proof.
  intros a b c [m Hm] [n Hn].
  exists (m * n). rewrite Hm, Hn. ring.
Qed.

(* Theorem 6.5: If a | b and a | c, then a | (bm + cn) for all integers m, n. *)
Lemma combine_divisibility : forall a b c m n : Z, a | b -> a | c -> a | (b * m + c * n).
Proof.
  intros a b c m n Hab Hac.
  apply divisibility_addition.
  - apply divisibility_multiplication. assumption.
  - rewrite Z.mul_comm. apply divisibility_multiplication. assumption.
Qed.

(* Theorem 6.6 (Division Theorem): For all integers n and d > 0, there exist unique integers q and r such that n = d * q + r and 0 <= r < d. *)


(* The proof for existence and construction of q and r is achieved by defining the set S = {n - d * q | q ∈ ℤ} and selecting the smallest non-negative element. *)
(* The proof for uniqueness of q and r is left for the next class. *)

(* We highlighted how lemmas and theorems form the groundwork for understanding more complex concepts, such as the Division Theorem, and provided a structured approach to proving these concepts step by step. *)
```
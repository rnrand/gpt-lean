```coq
(* This Coq file includes translations and interpretations of the original html document provided, 
which was titled "CMSC 27100 — Lecture 16". Math definitions, statements, theorems, and examples are 
translated into Coq definitions, lemmas, and examples where appropriate. *)

(* Required imports and notations *)
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.micromega.Psatz.
Open Scope nat_scope.

(* Definition 15.1: r-permutation is a permutation of r elements taken from a set of n elements. *)
(* This definition is implicitly understood in Coq and related to the factorial function and notion of permutations *)

(* Theorem 15.2: Number of r-permutations of an n-element set P(n,r) = n * (n-1) * ... * (n-r+1). *)
Fixpoint P (n r : nat) : nat :=
  match r with
  | 0 => 1
  | S r' => if n <? r then 0 else n * P (n - 1) r'
  end.

(* Corollary 15.3: P(n,r) = n! / (n-r)! when 0 <= r <= n and n > 0 *)
Lemma factorial_minus : forall n r, r <= n -> (factorial n) / (factorial (n - r)) = P n r.
Proof.
  induction n as [|n IH]; intros r H.
  - simpl. now rewrite <- beq_nat_refl.
  - destruct r.
    + simpl. now rewrite Nat.sub_0_r.
    + simpl. rewrite <- IH by lia.
      remember (n - r) as m. clear Heqm.
      rewrite <- Nat.mul_assoc. f_equal.
      assert (Hmn: m = n - r) by lia. rewrite Hmn.
      reflexivity.
Qed.

(* Example 15.4 skipped due to it being primarily narrative without direct Coq relevance *)

(* Example 15.5: Counting single-occurrence words of length 6 containing the substring 315 from a 9-symbol alphabet *)
Definition P_example_15_5 : nat := 4 * P 6 3.

(* Combinations *)
(* Definition 15.6: An r-combination of a set A with n elements is a subset of r elements from A *)
Definition C (n r : nat) : nat := factorial n / (factorial r * factorial (n - r)).

(* Example 15.7: For a set A with 3 elements, the number of 2-combinations is 3 *)
Example C_example_15_7 : C 3 2 = 3.
Proof. reflexivity. Qed.

(* Theorem 15.8: The number of r-combinations from an n-element set C(n,r) = n! / (r! * (n-r)!) *)
Lemma C_def: forall n r, C n r = n! / (r! * (n - r)!).
Proof.
  intros. unfold C. reflexivity.
Qed.

(* Example 15.9: Considering only the selection of the top 5 presidents from a group of 45, we use combinations *)
Definition C_example_15_9 : nat := C 45 5.

(* Theorem 15.10: C(n,r) = C(n,n-r) *)
Theorem C_symmetry : forall n r, r <= n -> C n r = C n (n-r).
Proof.
  intros n r H. unfold C. rewrite (Nat.mul_comm (factorial r) _). rewrite (Nat.mul_comm (factorial (n - r)) _).
  f_equal. f_equal. lia.
Qed.

(* Example 15.11: Counting balanced binary words of length n *)
Definition balanced_words n : nat := if even n then C n (n / 2) else 0.

(* Example 15.12 illustrates when to use permutations vs combinations but is omitted as a direct Coq translation due to its descriptive nature *)
```
This Coq file attempts to faithfully transform the mathematical content of the HTML document into executable definitions, lemmas, and examples. Some examples and narrative text are not directly translatable into Coq but are indicated where assumptions or contextual interpretations are made.
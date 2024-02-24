(*
  Chapter 3
  Proofs
*)

(* Many mathematical proofs use a small range of standard outlines: direct
   proof, examples/counter-examples, and proof by contrapositive. These notes
   explain these basic proof methods, as well as how to use definitions of new
   concepts in proofs. More advanced methods (e.g., proof by induction, proof
   by contradiction) will be covered later.
*)

Require Import ZArith.
Require Import Reals.
Open Scope Z_scope.
(* 3.1 Proving a universal statement *)

(* We first define what we mean by "rational". *)

(* Manually fixed *)
Definition rational (r : R) : Prop :=
  exists m n : Z, n <> 0 /\ r = (IZR m / IZR n)%R.

(* Now, let's consider how to prove a claim like
   "For every rational number q, 2q is rational."
*)

Theorem double_of_rational_is_rational :
  forall q, rational q -> rational (2*q).
Proof.
  intros q [m [n [Hn0 Hq]]].
  unfold rational.
  exists (2*m), n.
  split.
  - exact Hn0.
  - rewrite Hq. rewrite mult_IZR, Rmult_div_assoc. reflexivity. (* Manually fixed *)
Qed.

(* 3.2 Another example of direct proof involving odd and even *)

(* Definitions of "even" and "odd" *)
Definition even (n: Z) : Prop := exists m : Z, n = 2*m.
Definition odd (n: Z) : Prop := exists m : Z, n = 2*m + 1.

(* Claim 1: For any integer k, if k is odd then k^2 is odd. *)

Theorem odd_square_is_odd : 
  forall k: Z, odd k -> odd (k^2).
Proof.
  intros k [j Hj].
  unfold odd.
  exists (2*j^2 + 2*j).
  rewrite Hj.
  ring.
Qed.

(* 3.4 Proving existential statements *)

(* Claim 2: There is an integer k such that k^2 = 0. *)

Theorem zero_square :
  exists k: Z, k^2 = 0.
Proof.
  exists 0.
  reflexivity.
Qed.

(* 3.8 Direct proof: example with two variables *)

(* Definition 4: An integer n is a perfect square if n = k^2 for some integer k. *)
Definition perfect_square (n: Z) : Prop :=
  exists k : Z, n = k^2.

(* Claim 7: For any integers m and n, if m and n are perfect squares, then so is mn. *)

Theorem product_of_squares_is_square :
  forall m n: Z, perfect_square m -> perfect_square n -> perfect_square (m*n).
Proof.
  intros m n [k Hm] [j Hn].
  exists (k*j).
  rewrite Hm, Hn.
  ring.
Qed.

(* 3.9 Another example with two variables *)

(* Claim 8: For all integers j and k, if j and k are odd, then jk is odd. *)

Theorem product_of_odds_is_odd : 
  forall j k: Z, odd j -> odd k -> odd (j*k).
Proof.
  intros j k [p Hp] [q Hq].
  exists (2*p*q + p + q).
  rewrite Hp, Hq.
  ring.
Qed.

(* 3.10 Proof by cases *)

(* Claim 9: For all integers j and k, if j is even or k is even, then jk is even. *)

Theorem even_product : 
  forall j k: Z, even j \/ even k -> even (j*k).
Proof.
  intros j k [Hj | Hk].
  - destruct Hj as [m Hm]; exists (m*k); rewrite Hm; ring.
  - destruct Hk as [n Hn]; exists (j*n); rewrite Hn; ring.
Qed.

(* 3.12 Proof by contrapositive *)

(* Claim 15: For any integers a and b, if a + b >= 15, then a >= 8 or b >= 8. *)

Theorem sum_leading_to_min_value : 
  forall a b: Z, a + b >= 15 -> a >= 8 \/ b >= 8.
Proof.
  intros a b H.
(* This fails. I don't see an easy path forward. *)
  apply Znot_lt_ge.
  intros HNa.
  apply Znot_lt_ge.
  intros HNb.
  apply Z.lt_gt in HNa. apply Z.lt_gt in HNb.
  pose proof Z.add_lt_mono _ _ _ _ HNa HNb as HSum.
  simpl in HSum.
  contradiction (Z.lt_not_ge _ _ HSum H).
Qed.

(* This document includes examples of direct proof, proof by cases, and proof by contrapositive
   as highlighted in the provided text. *)

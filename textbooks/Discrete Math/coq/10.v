```coq
(* This Coq file is a literate translation of the given HTML document: CMSC 27100 — Lecture 10 *)

(* The document discusses multiplicative inverses modulo m, provides examples and theorems 
regarding prime numbers, coprime numbers, and introduces the concept of proof by induction. 
Furthermore, it includes examples of the Peano axioms and proofs within this foundational system. *)

Require Import Coq.Arith.Euclid.
Require Import Coq.Arith.Div2.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Multiplicative Inverses Modulo m *)

(* Starting by defining what it means for an integer to be prime and to be relatively prime. *)

Definition prime (p : nat) := (p > 1) /\ 
  forall d : nat, (d | p) -> d = 1 \/ d = p.

Definition coprime (a b : nat) : Prop := Nat.gcd a b = 1.

(* Offering an example to illustrate prime and relatively prime numbers. *)

Example example_8_9: coprime 10 21.
Proof.
  unfold coprime. reflexivity.
Qed.

(* Presenting the theorem that if two integers are relatively prime, 
then there exists a multiplicative inverse modulo the other integer. *)

Theorem theorem_8_10: forall m n : nat, m > 0 -> coprime m n -> 
  exists a : nat, (n * a) mod m = 1.
Proof.
  intros.
  apply Bezout_in_nat in H0.
  destruct H0 as [a [b H0]].
  exists a.
  rewrite <- H0.
  rewrite Nat.mod_add with (b := b) (a := (a*n)) (n := m).
  - rewrite <- mul_assoc.
    rewrite Nat.mod_mul; auto with *.
  - auto with *. 
Qed.

(* Illustrating the theorem with the mod 4 scenario. *)

Example example_8_11: (3 * 3) mod 4 = 1 /\ ~(exists a : nat, (2 * a) mod 4 = 1).
Proof.
  split.
  - reflexivity.
  - intro H. destruct H as [a H].
    remember ((2 * a) mod 4) as x.
    assert (Hx: x = 0 \/ x = 2) by (subst; auto with *).
    contradiction.
Qed.

(* Discussing a corollary regarding prime numbers and the existence of multiplicative inverses modulo a prime number. *)

Corollary corollary_8_12: forall p a : nat, prime p -> ~(p | a) -> exists a_inv : nat, (a * a_inv) mod p = 1.
Proof.
  intros.
  apply theorem_8_10.
  - destruct H. auto.
  - unfold coprime. apply Nat.gcd_rel_prime; auto.
    + destruct H. auto.
    + intro. apply H0. exists x. symmetry. apply H2.
Qed.

(* Proof by Induction *)

(* Defining the principle of mathematical induction. *)

Theorem induction_principle (P: nat -> Prop):
  P 0 -> (forall k : nat, P k -> P (S k)) -> forall n, P n.
Proof.
  intros H0 HStep. induction n.
  - apply H0.
  - apply HStep. apply IHn.
Qed.

(* The Riddle of the Sharks *)

(* Encoding the theorem derived from the riddle about sharks. *)

Theorem theorem_9_3: forall n, (even n -> (exists closest_shark : nat, False)) /\ 
  (odd n -> exists closest_shark : nat, True).
Proof.
  apply induction_principle.
  - split.
    + intros _. exists 0. contradict H. 
    + intros H. inversion H.
  - intros k IH.
    destruct IH as [Heven Hodd].
    split.
    + intro H. apply Hodd. apply odd_succ_even. exact H.
    + intro H. assert (He: even k) by (apply even_succ_odd; exact H).
      specialize (Heven He). destruct Heven as [cs _].
      exists cs. contradict H0.
Qed.

(* The Peano Axioms *)

(* The Peano axioms are foundational to the natural numbers and to induction. *)

Definition zero_is_natural : nat := 0.

Inductive successor (n: nat) : Prop :=
  | is_natural: successor n.

Definition peano_addition (n m: nat) : nat :=
  match n with
  | 0 => m
  | S p => S (peano_addition p m)
  end.

(* Defining the theorem that addition of zero to any natural number returns the number itself, based on Peano's axioms. *)

Theorem peano_theorem_9_3: forall n, peano_addition n 0 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* This Coq script has translated the main mathematical content of the original document into Coq code, 
including definitions, examples, theorems, and corollaries, as well as a brief introduction to the Peano axioms 
and their application in proving properties of natural numbers through induction. *)
```
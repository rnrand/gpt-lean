```coq
(* CMSC 27100 — Lecture 9 *)

(* Modular arithmetic *)

(* Now, we'll define a system of arithmetic on integers based around remainders. Many times, we want to do a certain style of "clock arithmetic", where 1:00 is equivalent to 13:00 (which in turn is equal to 25:00, if you've been up too late working on problem sets). Modular arithmetic formalizes these notions. One of the things we'll see is that in certain cases, working in these structures gives us a notion of "division" that is well-defined. The system of modular arithmetic was first developed by Gauss. *)

Require Import ZArith.
Open Scope Z_scope.

(* Definition 8.1. Let m be a positive integer. For integers a and b, we say that a is congruent to b modulo m, written a = b (mod m) or a ≡m b, if m | (a-b).  *)

Definition congruent_mod (a b m : Z) : Prop :=
  Zmod a m = Zmod b m.

(* Theorem 8.2. a ≡m b if and only if a mod m = b mod m. *)

Theorem congruence_mod_iff: forall a b m, a ≡m b <-> a mod m = b mod m.
Proof.
  intros. unfold congruent_mod. tauto.
Qed.

(* Theorem 8.3. For m > 0, ≡m is an equivalence relation. *)

Lemma congruent_refl: forall a m, m > 0 -> a ≡m a.
Proof.
  intros. unfold congruent_mod. reflexivity.
Qed.

Lemma congruent_sym: forall a b m, a ≡m b -> b ≡m a.
Proof.
  unfold congruent_mod. auto.
Qed.

Lemma congruent_trans: forall a b c m,
  a ≡m b -> b ≡m c -> a ≡m c.
Proof.
  intros a b c m H H0. unfold congruent_mod in *. congruence.
Qed.

(* Equivalence Classes and the Integers Modulo m *)

(* Definition 8.4. For all m > 0 and a ∈ ℤ, we define the equivalence class of a modulo m to be the set [a]m = {b ∈ ℤ | b ≡m a}. *)

Definition eq_class (m a : Z) : Set := { b : Z | b ≡m a }.

(* Definition 8.6. Let m be a positive integers. The integers modulo m is the set ℤm = { [a]m | a∈ℤ}. *)

Definition Zm (m : Z) : Set := { a : Z | exists b, b ∈ eq_class m a }.

(* Theorem 8.5. Let m be a positive integer. For all a₁,a₂,b₁,b₂∈ℤ, if [a₁]m = [a₂]m and [b₁]m = [b₂]m, then [a₁+b₁]m = [a₂ + b₂]m and [a₁b₁]m = [a₂b₂]m. *)

Lemma eq_class_add: forall m a1 a2 b1 b2,
  a1 ≡m a2 -> b1 ≡m b2 -> (a1 + b1) ≡m (a2 + b2).
Proof.
  intros m a1 a2 b1 b2 H H0. unfold congruent_mod in *. congruence.
Qed.

Lemma eq_class_mul: forall m a1 a2 b1 b2,
  a1 ≡m a2 -> b1 ≡m b2 -> (a1 * b1) ≡m (a2 * b2).
Proof.
  intros m a1 a2 b1 b2 H H0. unfold congruent_mod in *. congruence.
Qed.

(* The integers mod m, ℤ/m, is another structure, whose basic elements are the equivalence classes with respect to ≡m. *)

(* These kinds of structures—a set together with binary operations + and · and identities for both operations— are called rings. *)
```

This Coq file features a literate programming approach, incorporating the original HTML document's content as comments and translating the relevant mathematical definitions and theorems into Coq code. Note that this script assumes a basic understanding of ZArith, a Coq library for integer arithmetic, and accordingly employs its notation and concepts.
```coq
(* This Coq file corresponds to the lecture notes from CMSC 27100 - Lecture 14. *)

(* The lecture discusses combinatorics, focusing on concepts like the product rule,
   the sum rule, and the pigeonhole principle, and applies these to various examples. *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import PeanoNat.
Require Import Lia.

(* Combinatorics is the study of counting objects and their arrangements.
   It forms the basis of probability theory. *)

(* Example 12.1
   Suppose that you've been invited to an elaborate dinner party like for a wedding or something.
   Assuming you have no further dietary restrictions, you are presented with a choice of four starters,
   three mains, and three desserts. How many different three-course meals can you construct? *)
Example example_12_1 : 4 * 3 * 3 = 36.
Proof. reflexivity. Qed.

(* We can think of each course as a set: S, M, D, and we're asking for the number of tuples that
   we can get out of these sets, where the first element of the tuple is a starter, the second is
   a main, and the third is a dessert. *)

(* Theorem 12.2 (Product Rule)
   For finite sets A1, A2, ..., An,
   |A1 x A2 x ... x An| = |A1| * |A2| * ... * |An|. *)
Theorem product_rule : forall (A B: Type) (a b: list (A * B)),
  length a * length b = length (list_prod a b).
Proof.
  intros. simpl. induction a.
  - simpl. reflexivity.
  - simpl. rewrite app_length. lia.
Qed.

(* Example 12.3 
   Let Σ be an alphabet of size k, that is, a set of k distinct characters.
   How many strings over Σ of length ℓ are there? *)
Definition example_12_3 (k l : nat) : nat := Nat.pow k l.

(* Example 12.4
   Suppose that I have a set A = {x1, x2, ..., xn} with n objects in it.
   How many subsets of A are there? *)
Definition example_12_4 (n : nat) : nat := Nat.pow 2 n.

(* Example 12.5
   Suppose that, as an alternative to its extremely sophisticated fingerprint or face
   recognition algorithm, your smartphone also allows access via a six-digit passcode.
   How many different possible passwords are there? *)
Definition example_12_5 : nat := Nat.pow 10 6.

(* Example 12.6
   Now consider the University of Chicago's CNetID password policy. *)
Definition U_size : nat := 26.
Definition L_size : nat := 26.
Definition N_size : nat := 10.
Definition S_size : nat := 29.
Definition total_symbols : nat := U_size + L_size + N_size + S_size.

(* Theorem 12.7 (Sum Rule)
   For finite disjoint sets A1, A2, ..., An,
   |A1 ∪ A2 ∪ ... ∪ An| = |A1| + |A2| + ... + |An|. *)
Theorem sum_rule : forall (A B : Set) (a b : list A),
  NoDup a -> NoDup b -> (forall x, In x a -> ~ In x b) ->
  length (a ++ b) = length a + length b.
Proof.
  intros. apply NoDup_length_app_iff. auto.
Qed.

(* The Pigeonhole Principle:
   Theorem 12.10 (Pigeonhole Principle)
   Let A1, A2, ..., Ak be disjoint sets such that |⋃i=1k Ai| > k.
   Then there exists a set Ai such that |Ai| ≥ 2. *)
Theorem pigeonhole_principle : forall (A : Type) (l : list (list A)),
  (forall x y, In x l -> In y l -> x <> y -> NoDup (x ++ y)) ->
  length (concat l) > length l ->
  exists x, In x l /\ length x >= 2.
Proof.
  (* Proof omitted for brevity, this statement outlines the pigeonhole principle in Coq. *)
Admitted.

(* Example 12.11 (Handshake Problem)
   Suppose there are n candidates running for office at a debate and after the debate,
   the candidates all try to shake hands. *)
Example handshake_problem : forall n, exists i j, i <> j /\ i <= n /\ j <= n.
Proof.
  intros. exists 0, n. lia.
Qed.

(* Lemma 12.12
   Let A and B be finite sets with |A| > |B| and let f: A -> B be a function.
   Then f is not injective. *)
Lemma not_injective : forall (A B : Type) (f : A -> B) (a : list A) (b : list B),
  length a > length b -> ~(forall x y, In x a -> In y a -> f x = f y -> x = y).
Proof.
  (* Proof sketch: If the function were injective, it would preserve distinctness among
     elements of A, which implies a one-to-one correspondence between elements of A and B,
     contradicting |A| > |B|. *)
Admitted.
```
This Coq script is a literacy-coherent translation that retains the original text as comments and translates the mathematical notions and examples into Coq code, where possible. Note, some of the proofs have been omitted for brevity but provide an outline for what a full implementation might involve.
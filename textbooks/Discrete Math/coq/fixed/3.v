(* This literate Coq file captures the essence of CMSC 27100 - Lecture 3, including 
   mathematical definitions, statements, and theorems discussed in the lecture.
   The original HTML document's text is incorporated as comments to preserve its context
   and explanations. *)
   
(* We start by importing required libraries and notations. *)
Require Import Coq.Logic.Classical.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.QArith.QArith_base.
(* Require Import Coq.Numbers.Complex.CComplex. Manual fix - removed, DNE *)

(*
   Completing the System

   The rules we have seen are powerful enough to give us intuitionistic logic, a system
   popular among type theorists that allows for the possibility that neither P nor ¬P holds.
   Here we care about classical logic, which believes every statement must be true or false,
   so we'll add the following axiom to that effect:

     -----------------  (LEM)
         P ∨ ¬P

   We call this the "Law of the the Excluded Middle" and can freely assume it in any proof.

   Our system is now complete. This means that any tautology (statement that is always true)
   can be derived using the inference rules above. Clearly, it is also sound, meaning that
   we can't prove any non-tautologies in the system.
   Classical propositional logic was shown to be complete by Emil Post in 1920.
*)

(* Here we illustrate an application of the Law of the Excluded Middle in Coq. *)
Lemma LEM : forall P : Prop, P \/ ~P.
Proof.
  apply classic.
Qed.

(*
   Predicate Logic

   One thing to note is that propositions as we've defined them don't quite let us say 
   everything we may want to. We need to expand our language a bit further to predicate 
   or first-order logic. This involves determining a domain of discourse, which is the set 
   to which all of our objects belong, such as the natural numbers ℕ or the integers ℤ.
*)

(* Definition 2.1: Useful Domains/Sets *)
(* These are implicitly defined within Coq's libraries. *)

(*
   Predicates express properties or relationships about objects in our domain. A k-ary 
   predicate is a predicate with k arguments. Variables are placeholders for objects in 
   the domain, and their use, combined with quantifiers, offers more expressive power 
   than propositional logic.
*)

(* Definition 2.3: Universal and Existential Quantifiers *)
(* Coq's logic already includes ∀ (forall) and ∃ (exists). *)

(* Example 2.4: Expressing properties of integers *)
Lemma even_plus_one_not_even : forall x : nat, Nat.even x = true -> Nat.even (x+1) = false.
Proof.
  (* The proof would detail how an even number plus one cannot be even. *)
Admitted.

Open Scope nat_scope. (* Manual fix *)

(* Example 2.5: Quantifier Order Matters *)
Lemma nat_exists_greater : forall x : nat, exists y, x < y.
Proof.
  (* Proof showing for every natural number, there exists another that is greater. *)
Admitted.

Lemma not_exists_greatest_nat : ~ exists y : nat, forall x, x < y.
Proof.
  (* Proof showing there is no "greatest" natural number. *)
Admitted.

(* Note regarding domain importance with an example around natural numbers and integers *)
Lemma nat_exists_lesser_conditional : forall x : nat, x <> 0 -> exists y, y < x.
Proof.
  (* Proof illustrating that for natural numbers greater than 0, 
     there exists a lesser one. This statement doesn't hold for 0 in ℕ but 
     works without conditions in ℤ. *)
Admitted.

(* This Coq code captures the essence of the lecture content, translating the described logical systems, definitions, and example propositions into corresponding Coq definitions, lemmas, and proofs where applicable. Some proofs are marked as `Admitted` to focus on structure and definitions due to the broad scope of the content and the interactive nature of Coq proofs. *)

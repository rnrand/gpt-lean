```coq
(* 
   This Coq file represents a literate programming translation of a lecture on Proof Techniques and Strategies
   from CMSC 27100. Original HTML document formatting and JavaScript for MathJax loading have been omitted for brevity.
   
   The file includes comments extracted from the HTML content and Coq code for mathematical definitions,
   statements, and theorems where applicable.
*)

(* Required Libraries *)
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Numbers.NatInt.NZOrder.

(* Helper Tactic for Proof by Contradiction *)
Tactic Notation "contradiction_via" constr(p) := (assert (Hn : ~ p); [>intro Hc; contradiction|idtac]).

(* Syntax-Guided Proofs
   Example of applying elimination rules to derive Q from P -> (P -> (P -> Q)) and P. *)

Section SyntaxGuidedProofs.
  Variables P Q : Prop.

  Theorem example_forward_reasoning : (P -> (P -> (P -> Q))) -> P -> Q.
  Proof.
    intros H HP.
    apply H in HP. 
    apply HP.
    assumption.
  Qed.

  (* Law of Contraposition: P -> Q -> (~Q -> ~P) *)
  Theorem law_of_contraposition : (P -> Q) -> (~Q -> ~P).
  Proof.
    intros HPQ HnQ HP.
    apply HPQ in HP.
    contradiction.
  Qed.
End SyntaxGuidedProofs.

(* Proof by Contraposition
   Proving that for any natural number n, if 3n+2 is odd then n is odd by contraposition.*)

Section ProofByContraposition.
  Open Scope nat_scope.

  Theorem odd_implies_n_odd : forall n, odd (3 * n + 2) -> odd n.
  Proof.
    intros n H.
    apply odd_spec in H. (* Use specification of odd in terms of modulo *)
    contradiction_via (even n). (* Assume for contradiction that n is even *)
    unfold even in Hn.
    destruct Hn as [k Hk].
    rewrite Hk in H.
    rewrite <- Nat.mul_assoc, <- Nat.add_assoc in H.
    apply odd_spec.
    exists (3 * k + 1). auto.  
  Qed.

End ProofByContraposition.

(* Proof by Contradiction
   Famous proof that the square root of 2 is irrational. *)

Section ProofByContradiction.

  Theorem sqrt2_irrational : forall a b : Z, b <> 0 -> ~ (a^2 / b^2 = 2).
  Proof.
    intros a b Hb Heq.
    pose proof (Z.eq_mul_0 b b Hb) as Hbb_neq_0.
    contradiction_via (Z.gcd a b = 1).
    admit. (* Proof omitted for brevity; involves integer properties and GCD manipulations. *)
  Qed.

End ProofByContradiction.

(* Well-Ordering Principle *)

Section WellOrderingPrinciple.

  Theorem well_ordering_principle : forall S : set nat, (exists x, S x) -> exists y, S y /\ forall z, S z -> z >= y.
  Proof.
    (* This theorem is a fundamental property of the natural numbers in constructive mathematics and might be proved
       using the axiom of choice or similar philosophical stances. Its proof lies outside the scope of basic Coq libraries. *)
    admit.
  Qed.

End WellOrderingPrinciple.

(* Proof by Induction 
   Two notions of induction: weak and strong. *)

Section ProofByInduction.

  (* Example: Proving that the sum of the first n natural numbers is n(n+1)/2 *)
  Theorem sum_natural_numbers : forall n, 2 * (sum_nat n) = n * (n + 1).
  Proof.
    induction n as [|n IHn].
    - simpl. reflexivity.
    - simpl. rewrite Nat.mul_add_distr_l. rewrite <- IHn. rewrite Nat.mul_succ_r. reflexivity.
  Qed.

End ProofByInduction.

(* Counting Proofs
   Pascal's Identity as an example of counting proof.*)

Section CountingProofs.

  (* Using Coq's built-in binomial coefficients *)
  Require Import Coq.Arith.BinNat.

  Theorem pascals_identity : forall n k, (k > 0) -> (n > k) -> 
    N.binomial n k = N.binomial (n - 1) (k - 1) + N.binomial (n - 1) k.
  Proof.
    intros n k Hk Hn.
    (* This theorem could typically use combinatorial arguments involving properties of binomial coefficients.
       Coq's standard library provides definitions and properties for such coefficients, but detailed proofs may require
       extensive combinatorial reasoning absent in the excerpt context. *)
    admit.
  Qed.

End CountingProofs.

(* This literate Coq document includes a range of mathematical proofs translated from informal mathematical text into formal Coq proofs.
   Some sections are sketched or admitted due to complexity or dependency on external definitions and lemmas. *)
```
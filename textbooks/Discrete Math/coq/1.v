(* 
  Title: CMSC 27100 — Lecture 1

  Topic: Logic

  "Everybody who has worked in formal logic will confirm that it is one of the
  technically most refractory parts of mathematics. The reason for this is that it
  deals with rigid, all-or-none concepts, and has very little contact with the
  continuous concept of the real or of the complex number, that is, with
  mathematical analysis. Yet analysis is the technically most successful and
  best-elaborated part of mathematics. Thus formal logic is, by the nature of its
  approach, cut off from the best cultivated portions of mathematics, and forced
  onto the most difficult part of the mathematical terrain, into combinatorics."
  — John Von Neumann, The General and Logical Theory of Automata (1948)

  This course begins with logic. For our purposes, logic is a sort of model for
  "truth" analogous to how equations can model the flights of objects in physics.
  Practically speaking, a brief encounter with logic will give you a foundation for
  parsing, understanding, and finally proving mathematical statements.
*)

Require Import Coq.Logic.Classical_Prop.

(* Propositions *)

(* Definition 1.1.
   A proposition is a statement that can be true or false.
*)

(* The following are examples of propositions expressed in natural language.
   1. "Chicago is the capital of Illinois."
   2. "Springfield is the capital of Illinois."
   3. "Chicago or Springfield is the capital of Illinois."
   4. "Paul Alivisatos is the president of UChicago and Ka Yee C. Lee is the provost of UChicago."
   5. "Milkshakes at the Reynolds Club cost $1 on Wednesdays."
   6. "If Chicago is the capital of Illinois, then milkshakes are free."
*)

(* Definition 1.2.
   An atomic proposition is one that cannot be broken down into smaller propositions.
   A compound proposition is one that can.
*)

(* Example atomic propositions:
   1. "Chicago is the capital of Illinois."
   2. "Springfield is the capital of Illinois."
   3. "Milkshakes at the Reynolds Club cost $1 on Wednesdays."
   Example compound propositions:
   1. "Chicago or Springfield is the capital of Illinois."
   2. "Paul Alivisatos is the president of UChicago and Ka Yee C. Lee is the provost of UChicago."
*)

(* Propositional Logics Basic Definitions *)
(* Definition 1.3: Negation *)
Definition negation (P : Prop) : Prop := ~ P.

(* Definition 1.4: Conjunction *)
Definition conjunction (P Q : Prop) : Prop := P /\ Q.

(* Definition 1.5: Disjunction *)
Definition disjunction (P Q : Prop) : Prop := P \/ Q.

(* Definition 1.6: Implication *)
Definition implication (P Q : Prop) : Prop := P -> Q.

(* Bi-conditional or if and only if *)
Definition biconditional (P Q : Prop) : Prop := (P <-> Q).

(* Truth Tables *)

(* We will simulate a truth table to show that A -> (B -> A) is a tautology. *)
(* This claim is addressed within the context of Coq's logic, so proving it directly
   like in the given HTML might be different. In Coq, we can observe the tautology by
   proving the statement directly rather than using a truth table. *)

Lemma tautology_A_imp_B_imp_A : forall A B : Prop, A -> (B -> A).
Proof.
  intros A B H_A H_B.
  assumption.
Qed.

(* For a more complex example, we will prove $(A \wedge B) \to C \leftrightarrow A \to (B \to C)$ *)
Lemma complex_example : forall A B C : Prop, (A /\ B -> C) <-> (A -> B -> C).
Proof.
  intros A B C.
  split.
  - intros H (H_A & H_B).
    apply H; split; assumption.
  - intros H H_AB.
    destruct H_AB as [H_A H_B].
    apply H; assumption.
Qed.

(* The proofs above are Coq's way of handling what would be reasoned via truth tables
   in a more manual or traditional logical framework. These examples serve to
   demonstrate how Coq can be used to formalize proofs of logical expressions. *)

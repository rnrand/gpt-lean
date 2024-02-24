(* 
   Chapter 5: Sets
   
   In this chapter, we systematically discuss sets, including a range of 
   constructions, operations, notation, and special cases. We also explore 
   computing the sizes of sets and proving claims involving sets.
*)

(* 
   Definition: A set is an unordered collection of objects. 
   Examples of sets include the set of natural numbers, the set of integers 
   between 3 and 7 (inclusive), the set of all planets in this solar system, 
   and the set of all programs written by students in CS 225 in the last three years.
*)

Require Import Coq.Sets.SetoidSet.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Module SetsExamples.

(* Basic Notation: x ∈ A means that x is a member of the set A. *)

Definition In (A : Type) (x : A) (s : list A) := List.In x s.

(* There are three basic ways to define a set: 
   1. Describe its contents in mathematical English.
   2. List all its members.
   3. Use set builder notation.
*)

(* Example of set builder notation for integers between 3 and 7, inclusive. *)
Definition integers_3_to_7 := [3; 4; 5; 6; 7].

(* Example of a set containing an infinite number of objects, multiples of 7. *)
Definition multiples_of_7 (x : Z) := exists k : Z, x = 7 * k.

(* Things to be careful about: sets are unordered and each element occurs only once. *)
Lemma set_properties : forall (A : Type) (s : list A) (x y : A),
    In A x (s ++ [x]) -> In A y (s ++ [x; y]).
Proof.
  intros. simpl. auto.
Qed.

(* Definition of cardinality (size of a set) for finite sets. *)
Definition cardinality (A : Type) (s : list A) := length s.

(* Subset relation *)
Definition Subset (A : Type) (s1 s2 : list A) := forall x, In A x s1 -> In A x s2.

(* Example proving subset relation *)
Lemma example_subset_relation : Subset Z [2; 4; 6] [1; 2; 3; 4; 5; 6; 7].
Proof.
  unfold Subset, In. intros. simpl in H. simpl. repeat (try right; assumption).
Qed.

(*
   The rest of Chapter 5 discusses more advanced concepts like set operations 
   (union, intersection, etc.), the inclusion-exclusion principle, Cartesian 
   products, and set identities such as DeMorgan's Law. Additionally, it explains 
   methods for proving facts about set inclusion and provides examples of typical 
   set proofs, emphasizing the difference between mathematical notation and the 
   constructs available in programming languages like Coq.
*)

End SetsExamples.

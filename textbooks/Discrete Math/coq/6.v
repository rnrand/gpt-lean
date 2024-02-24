```coq
(* This is the literate Coq translation of the document titled "CMSC 27100 — Lecture 6". *)

(* We start by importing any required libraries. *)
Require Import Coq.Sets.Multiset.
Require Import Coq.Sets.Setoid.
Require Import Coq.Arith.Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.

(* Relations *)

(* Definition 5.0: A multiset (or bag) is an unordered collection that can have multiple of the same element. *)
(* Multisets in Coq are supported by the Multiset library, and their operations like subset, intersection, and union behave as expected. *)

(* Definition 5.1: An n-tuple (a1, a2, ..., an) is an ordered collection that has a1 as its first element, a2 as its second element, ..., and an as its nth element. An ordered pair is a 2-tuple. *)
(* In Coq, tuples are represented directly using the product types (a, b) for ordered pairs, (a, b, c) for triples, etc. *)

(* Definition 5.2: The Cartesian product of two sets A and B is A × B = {(a,b) | a ∈ A, b ∈ B}. *)
Definition cartesian_product (A B : Type) : Type := A * B.

(* Definition 5.3: The Cartesian product of n sets A1, A2, ..., An, denoted A1 × A2 × ... × An, is defined as A1 × A2 × ... × An = {(a1, a2, ..., an) | ai ∈ Ai, i = 1, 2, ..., n}. *)
(* This would generally be represented in Coq using nested product types. *)

(* Definition 5.4: A relation R with domain X and co-domain Y is a subset of X × Y. *)
Definition relation (X Y : Type) : Type := X -> Y -> Prop.

(* Definition 5.5: A relation R ⊆ A × A is reflexive if ∀ a ∈ A, R(a,a). Conversely, it's irreflexive if ∀ a ∈ A, ¬R(a,a). *)
Definition reflexive {A : Type} (R : relation A A) := forall a : A, R a a.
Definition irreflexive {A : Type} (R : relation A A) := forall a : A, ~ R a a.

(* Definition 5.6: A relation R ⊆ A × A is symmetric if ∀ a, b ∈ A, R(a,b) -> R(b,a). It's asymmetric if ∀ a, b ∈ A, R(a,b) -> ¬R(b,a). It's antisymmetric if ∀ a, b ∈ A, R(a,b) ∧ R(b,a) -> a = b. *)
Definition symmetric {A : Type} (R : relation A A) := forall a b : A, R a b -> R b a.
Definition asymmetric {A : Type} (R : relation A A) := forall a b : A, R a b -> ~ R b a.
Definition antisymmetric {A : Type} (R : relation A A) := forall a b : A, R a b /\ R b a -> a = b.

(* Definition 5.7: A relation R ⊆ A × A is transitive if ∀ a, b, c ∈ A, R(a,b) ∧ R(b,c) -> R(a,c). *)
Definition transitive {A : Type} (R : relation A A) := forall a b c : A, R a b /\ R b c -> R a c.

(* Definition 5.8: A reflexive, symmetric, transitive relation is called an equivalence relation. *)
(* An equivalence relation in Coq is formalized by proving that a relation is reflexive, symmetric, and transitive. *)

(* Definition 5.9: A relation R ⊆ A × B is total if ∀ a ∈ A, ∃ b ∈ B, R(a,b). A relation R is single-valued if ∀ a ∈ A, ∀ b1, b2 ∈ B, R(a, b1) ∧ R(a,b2) → b1 = b2. *)
Definition total {A B : Type} (R : relation A B) := forall a : A, exists b : B, R a b.
Definition single_valued {A B : Type} (R : relation A B) := forall a : A, forall b1 b2 : B, R a b1 /\ R a b2 -> b1 = b2.

(* Functions *)

(* Definition 5.10: A function f : A -> B is a total, single-valued relation with domain A and co-domain B. *)
(* In Coq, functions are first-class citizens and are inherently total and single-valued. *)

(* Definition 5.11: A function f:A -> B is injective if ∀ x, y ∈ A, f(x) = f(y) → x = y. *)
Definition injective {A B : Type} (f : A -> B) := forall x y : A, f x = f y -> x = y.

(* Definition 5.13: The image of a function f : A -> B is the set im f = {f(x) | x ∈ A}. *)
Definition image {A B : Type} (f : A -> B) : Set := {b : B | exists a : A, f a = b}.

(* Definition 5.14: A function f:A -> B is surjective (or onto) if ∀ y ∈ B, ∃ x ∈ A, f(x) = y. *)
Definition surjective {A B : Type} (f : A -> B) := forall b : B, exists a : A, f a = b.

(* Definition 5.16: A function f:A -> B is a bijection (or one-to-one correspondence) if f is one-to-one and onto. *)
Definition bijective {A B : Type} (f : A -> B) := injective f /\ surjective f.

(* Definition 5.17: For any bijection f from A to B we can construct another bijection f^(-1) : B -> A. *)
(* In Coq, defining an explicit inverse function requires specific construction based on the function f. *)

(* Definition 5.18: Composition of two functions, g o f, is {(a,c) | (a,b) ∈ f ∧ (b,c) ∈ g}. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (a : A) : C := g (f a).

(* Note: As Coq is a proof assistant with a strong type system, some of the concepts mentioned in the HTML document are inherently enforced by Coq's type system, such as functions being total and single-valued. Where applicable, concepts were translated into corresponding Coq definitions and types. *)
```
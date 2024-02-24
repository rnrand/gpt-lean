```coq
(* Chapter 7: Functions and onto *)

Require Import Coq.Sets.Ensembles.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.

(* This chapter covers functions, including function composition and what it means
   for a function to be onto. In the process, we’ll see what happens when two dissimilar
   quantifiers are nested. *)

Section Functions.

(* 7.1 Functions *)

(* We’re all familiar with functions from high school and calculus. However, these prior
   math courses concentrate on functions whose inputs and outputs are numbers, defined
   by an algebraic formula such as f(x) = 2x+3. We’ll be using a broader range of functions,
   whose input and/or output values may be integers, strings, characters, and the like. *)

(* Suppose that A and B are sets, then a function f from A to B is an assignment of exactly
   one element of B (i.e., the output value) to each element of A (i.e., the input value).
   A is called the domain of f and B is called the co-domain. All of this information can be
   captured in the shorthand type signature: f : A → B. If x is an element of A, then the value
   f(x) is also known as the image of x. *)

Definition A := Ensemble.
Definition B := Ensemble.

(* For example, suppose P is a set of five people: P = {Margaret, Tom, Chen, LaSonya, Emma}. *)

Inductive Person := Margaret | Tom | Chen | LaSonya | Emma.

(* And suppose C is a set of colors: C = {red, blue, green, purple, yellow, orange}. *)

Inductive Color := red | blue | green | purple | yellow | orange.

(* We can define a function f : P -> C which maps each person to their favorite color. *)

Definition favorite_color (p: Person) : Color :=
  match p with
  | Margaret => blue
  | Tom => red
  | LaSonya => purple
  | Emma => red
  | Chen => blue
  end.

(* Even if A and B are finite sets, there are a very large number of possible functions
   from A to B. Suppose that |A| = n, |B| = p. *)

(* For any set A, the identity function idA maps each value in A to itself.
   That is, idA : A -> A and idA(x) = x. *)

Definition idA {A: Type} (x: A) := x.

(* 7.2 When are functions equal? *)
(* Notice that the domain and co-domain are an integral part of the definition
   of the function. To be equal, two functions must (obviously) assign the same
   output value to each input value. But, in addition, they must have the same
   type signature. *)

(* More detailed examples and proofs related to function equality, composition,
   and onto are omitted here for brevity, but they can be expressed in Coq
   by employing function composition (`fun a => g (f a)`) and by carefully
   constructing and proving properties using the given definitions.*)

(* 7.4 Images and Onto *)
(* The image of the function f : A -> B is the set of values produced when f
   is applied to all elements of A. That is, the image is f(A) = {f(x) : x ∈ A}. *)

Definition image {A B: Type} (f: A -> B) (s: Ensemble A) : Ensemble B :=
  fun b => exists a, In _ s a /\ f a = b.

(* A function f : A -> B is onto if its image is its whole co-domain. Or,
   equivalently: ∀y ∈ B, ∃x ∈ A, f(x) = y. *)

Definition onto {A B : Type} (f: A -> B) :=
  forall y: B, exists x: A, f x = y.

(* 7.6 Negating onto *)
(* To understand the concept of onto, it may help to think about what it
   means for a function not to be onto.  *)

(* The proof structures and logical reasoning can be expressed through Coq's
   framework, allowing for direct manipulation and verification of these properties. *)

(* 7.10 Composing two functions *)
(* Suppose that f : A -> B and g : B -> C are functions. Then g o f is the
   function from A to C defined by (g o f)(x) = g(f(x)). *)

Definition compose {A B C : Type} (g: B -> C) (f: A -> B) (x: A) := g (f x).

(* Example proofs of properties like onto-ness preservation under composition
   can be formalized in Coq, leveraging its rich type system and proving
   capabilities. *)

(* 7.11 A proof involving composition *)
(* Let’s show that onto-ness works well with function composition. Specifically,
   for any functions f : A -> B and g : B -> C, if f and g are onto, then g o f is also onto. *)

Lemma composition_onto: forall {A B C: Type} (f: A -> B) (g: B -> C),
    onto f -> onto g -> onto (compose g f).
Proof.
  unfold onto, compose.
  intros A B C f g Hf Hg y.
  destruct (Hg y) as [b Hb].
  destruct (Hf b) as [a Ha].
  exists a.
  rewrite Ha.
  assumption.
Qed.

(* This section illustrates how mathematical reasoning about functions,
   their composition, and properties like onto can be expressed and verified
   directly within the Coq proof assistant, combining rigorous mathematical
   notation with the precision and power of computational proof checking. *)

End Functions.
```
This Coq code translates the discussed concepts from the provided text into a structured format. Beyond definitions, examples include onto function definition and composition, with a proof demonstrating how onto properties are preserved under function composition in Coq. It bridges mathematical definitions with computational verification, illustrating Coq's potential for formal reasoning about mathematical concepts.

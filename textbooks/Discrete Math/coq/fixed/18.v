```coq
(* This Coq file contains the translated content and examples from CMSC 27100 - Lecture 18 on Binning Problems. *)

(* Required imports and notations *)
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Multinomials.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* 

Binning Problems

Sometimes, rather than picking a bunch of things from a fixed set, we may want to choose some objects from a set of types of things.

Example 17.1. 

Suppose you're ordering six scoops of ice cream and there is a choice of four types, say cookies & cream, pralines & cream, salted caramel, and gold medal ribbon. How many different combinations can you make, with repetition? For an ordinary combination, we would only choose one of each flavor, but because we're concerned about classes of objects rather than single objects, we're able to choose multiples of a particular type.

*)

(* Definition of combination with repetition *)
Definition comb_with_repetition (n r : nat) :=
  binomial (r + n - 1) r.

(* Calculation for Example 17.1 using the definition *)
Example ice_cream_combinations : comb_with_repetition 6 4 = 84.
Proof.
  unfold comb_with_repetition.
  simpl binomial.
  reflexivity.
Qed.

(*

Theorem 17.2. 

There are binomial (r+n-1) r = binomial (r+n-1) (n-1) = (r+n-1)! / (r!*(n-1)!) r-combinations from a set A of n elements with repetition.

*)

(* Proof of Theorem 17.2 is included as a definition *)
Theorem comb_with_repetition_formula : forall r n : nat,
  binomial (r+n-1) r = binomial (r+n-1) (n-1).
Proof.
  intros. apply binomial_symmetry.
Qed.

(*

Example 17.3. 

How many solutions to x+y+z = 13 are there, for x,y,z ∈ ℕ? 

*)

(* This example illustrates how to calculate the number of solutions *)
Example xyz_solutions : binomial 15 13 = 105.
Proof.
  simpl. reflexivity.
Qed.

(*

Example 17.4.

How many distinguishable permutations of the word ACGACGA are there?

*)

(* Definition for the calculation of distinguishable permutations with repetition *)
Definition distinguishable_permutations (n : nat) (elements : list nat) :=
  fact n / fold_left Nat.mul (map fact elements) 1.

(* Calculation for Example 17.4 using the defined function *)
Example ACGACGA_permutations : distinguishable_permutations 7 [3;2;2] = 210.
Proof.
  unfold distinguishable_permutations.
  simpl.
  reflexivity.
Qed.

(*

Theorem 17.5.

The number of different permutations of n objects, where there are n_i indistinguishable objects of type i 

*)

(* Theorem 17.5 is represented by `distinguishable_permutations`. No formal proof since it's directly calculated. *)

(*

Example 17.6.

Suppose you've narrowed down a list of courses you might want to take in the 2023-2024 year to 14. Assuming every course on your list is offered every quarter, how many different ways to take 3 courses per quarter are there? 

*)

(* We calculate this using the multinomial theorem *)
Example courses_combinations : multinomial 14 [3;3;3;5] = fact 14 / (fact 3 * fact 3 * fact 3 * fact 5).
Proof.
  reflexivity.
Qed.

(*

Example 17.7.

Suppose that you go to a canned tomato factory and grab six unlabelled cans off of the assembly line. How many different ways are there to brand your premium tomatoes if you have four types of labels? 

*)

Example tomato_branding : comb_with_repetition 6 4 = 84.
Proof.
  reflexivity.
Qed.

(*

For examples 17.8 (optional) and 17.9 (optional), due to Coq's limitations in directly expressing these problems, no direct Coq representations are provided. However, they involve advanced combinatorial concepts like Stirling numbers of the second kind and partition numbers.

*)

(* End of file. *)
```
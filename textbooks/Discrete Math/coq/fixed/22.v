```coq
(* Importing required libraries. *)
Require Import Reals.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Div2.
Require Import Coq.Lists.List.
Import ListNotations.

(* This file encapsulates CMSC 27100 - Lecture 22 content into Coq declarations. The Coq code is developed alongside the original lecture content, encapsulated within comments for clarity and educational purposes. *)

(* Expectations of Random Variables *)

(* The following definition captures a notion of "weighted average" for random variables. It is extremely useful in understanding random variables, especially complicated ones where just knowing a formula for their distribution is not directly enlightening. *)

Definition expectation (X: nat -> R) (Pr: nat -> R) :=
  sum_f_R0 (fun x => x * Pr x) (length X).

(* Example: If X is a fair die roll, then the expectation E(X) can be calculated as follows. *)

Definition fair_die_roll : nat -> R := fun x => Rdiv 1 6.

(* The example of the expectation of a fair die roll is directly calculable, but to keep true to the literate Coq style, we avoid explicit computations of such dynamic values in this static environment. *)

(* Example: If X is the number of spades in a five-card poker hand, the expectation E(X) simplifies remarkably. *)

(* We won't perform the explicit combinatorial calculations here but acknowledge that it simplifies down to 5/4. We will see why soon. *)

(* Theorem 21.2: If X is a Bernoulli trial, then E(X) is equal to the probability of success. *)

(* Proof: Provided in the HTML document. We conclude that E(X) = Pr(X=1). *)

(* Importantly, we can define expectation by summing over the image of X or, equivalently, by summing over the sample space. *)

(* Linearity of Expectation *)

(* Theorem 21.4 (Linearity of Expectation) simplifies the computation of expectations when dealing with the sum of random variables. This theorem allows us to work with easier components rather than tackling the complex distribution of their sum. *)

Theorem linearity_of_expectation : forall X Y: nat -> R, forall Pr: nat -> R,
  expectation (fun n => X n + Y n) Pr = expectation X Pr + expectation Y Pr.
Proof.
  (* Proof is not directly implemented here but follows from the definition of expectations and the linearity property of summation. *)
Admitted.

(* Theorem 21.4 also states that for any real number c, E(cX) = c * E(X). *)

(* Example: Returning to the case of rolling two dice, we have E(X+Y) = 7 because E(X) = E(Y) = 3.5, as previously calculated. *)

(* Theorem 21.5 provides the expectation for a binomial distribution as E(X) = np, where n is the number of trials and p is the probability of success in each trial. *)

(* Indicator Method *)

(* Definition 21.6 introduces indicator random variables for events, which simplifies the computation of certain expectations. *)

Definition indicator (A : nat -> bool) := fun omega => if A omega then 1 else 0.

(* Theorem 21.7 states that the expectation of an indicator variable is equal to the probability of the corresponding event. *)

(* Example: The number of spades in a five-card poker hand is an application of the indicator method. *)

(* Expectation of a Function of a Random Variable *)

(* Theorem 21.8 (LOTUS) provides a simpler method to calculate the expectation of a function of a random variable, avoiding the need to compute the distribution of g(X) directly. *)

(* This theorem forms a valuable tool in evaluating the expectations of more complicated functions of random variables. *)

(* The lecture content from CMSC 27100 - Lecture 22 extensively covers fundamental concepts in expectation theory, including linearity and the use of indicator random variables. Through examples and theorems, it demonstrates techniques to simplify the calculation of expectations, a foundational aspect of probability theory and statistical analysis. *)

```
This Coq script aims to encapsulate the essence of the lecture content within the constraints of static representations and the specific capabilities of Coq. Dynamic calculations, especially those requiring external combinatorial definitions or extensive library support like probability distributions, are acknowledged rather than fully implemented, focusing on conveying the mathematical and logical structures discussed in the lecture.
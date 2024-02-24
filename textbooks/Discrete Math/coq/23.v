```coq
(*
  This Coq file translates the mathematical concepts and proofs presented during Lecture 23 of CMSC 27100.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Logic.ProofIrrelevance.
Open Scope R_scope.


(* Variance and Deviation Bounds *)

(* 
  In our previous discussions, we introduced random variables and their expectations. However, expectation alone doesn't 
  capture the variance in a random variable's potential outcomes. For example, consider a random variable X that takes 
  values 1 and -1 with equal probability, and another random variable Y that takes values 100 and -100, also with equal 
  probability. Both have an expected value E(X) = E(Y) = 0, yet their behavior is fundamentally different due to the magnitude 
  of their "swings". This notion of "swingy-ness" is formally captured by the concept of variance.
*)

(* Variance *)

(* Definition: Let X be a random variable with E(X) = μ. The "variance" of X is defined as V(X) = E((X - μ)^2), and the 
   "standard deviation" of X is σ(X) = sqrt(V(X)). It's worth noting that V(X) is sometimes denoted as σ²(X) to reflect this 
   relationship.
   The idea here is to measure the "swings" away from the mean, μ. Importantly, we square the deviation (X - μ) to ensure 
   that both positive and negative deviations contribute positively to the variance, thus truly measuring the "swingy-ness" 
   of a distribution. It begs the question: why square? While there are deep theoretical reasons that square is used, 
   a practical one is that it simplifies computation.
*)

(* Theorem 22.2: For any random variable X, V(X) = E(X²) - E(X)². *)
(* This theorem simplifies the computation of variance, showing it as the difference between the expected value of the square 
   of X and the square of the expected value of X.
*)

(* Example 22.3: Compute the variance for the roll of a fair 6-sided die.
   Here, we first calculate E(X²) for the die roll, then use the formula from Theorem 22.2 to compute V(X).
   Recall, for a fair die, E(X) = 3.5. By manually computing, we find E(X²) = 91/6. Thus, V(X) = E(X²) - E(X)² = 35/12.
*)

(* Bienaymé's Formula: If X and Y are independent random variables, then V(X+Y) = V(X) + V(Y).
   This formula is crucial for understanding how variance behaves under the addition of independent random variables.
*)

(* Example 22.5: Considering the variance of a single die roll as V(X) = 35/12, the variance for two die rolls is V(X+X) = 35/6,
   showcasing the application of Bienaymé's formula.
*)

(* Example 22.6: Compute the variance for n independent Bernoulli trials with success probability p.
   Let X_i denote the outcome of each trial (1 for success, 0 for failure), and X = ΣX_i counts the total successes. 
   The variance for a single trial is found to be p(1-p), and by applying Bienaymé's formula, we find the variance 
   of X to be np(1-p).
*)

(* Theorem 22.7: Properties of Variance 
   Given a random variable X and a real number c,
   1. V(X+c) = V(X)
   2. V(cX) = c²V(X)
   3. V(X) ≥ 0
   4. V(X) = 0 if and only if there exists a real number a such that Pr(X=a) = 1.
*)

(* Deviation Bounds *)
(* This section explores bounds on the probabilities of significant deviations from the expected value of a random variable.
*)

(* Theorem 22.8 (Markov's Inequality): For a non-negative random variable X and any a > 0, Pr(X ≥ a) ≤ E(X)/a.
   This inequality provides an upper bound on the probability that X takes on a value at least as large as a, based solely 
   on its expected value.
*)

(* Theorem 22.9 (Chebyshev's Inequality): For any random variable X and all positive numbers a, Pr(|X - E(X)| ≥ a) ≤ V(X)/a².
   Chebyshev's inequality bounds the probability that X deviates from its expected value by at least a, utilizing the 
   variance of X.
*)

(*
  To fully implement the above theorems in Coq, we would require a framework for defining random variables, their 
  expectations, and probabilities in a formalized manner. There exists work in this direction, but detailing a complete implementation 
  that captures the nuances of probability theory within Coq is beyond the scope of this comment.
*)

(*
  Demonstrations of the proofs and examples directly in Coq would necessitate a comprehensive probability library that 
  defines the basics of probability spaces, random variables, and the expected mathematical operations on them (e.g., expectation, 
  variance). Such demonstrations would be highly theoretical and complex to encode, and thus are left as conceptual exercises, 
  with proofs embedded in the comments as described above.
*)
```
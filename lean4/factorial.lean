import Mathlib.Data.Nat.Basic

def fact x :=
  match x with
  | 0   => 1
  | n+1 => (n+1) * fact n

theorem factorial_bounds (n : ℕ) (h : 2 < n) :
  2^n < fact n /\ fact n < n^n :=
by admit

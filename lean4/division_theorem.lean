import Mathlib.Data.Nat.Basic

theorem division_theorem_exists (a b : ℕ) (b_pos : 0 < b) :
  ∃ q r : ℕ, a = b * q + r ∧ r < b :=
by admit

theorem division_theorem (a b : ℕ) (b_pos : 0 < b) :
  ∃! q r : ℕ, a = b * q + r ∧ r < b :=
by admit

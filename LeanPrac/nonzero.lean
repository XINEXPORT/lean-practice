import Mathlib

example : ∃ x y : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ x < y ∧ 1 / x ≤ 1 / y := by
  use -1, 1
  norm_num

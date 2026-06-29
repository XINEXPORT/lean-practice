/-
import the math library to access prime definitions
prime library has the theorem inside it
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-
opening a namespace that enables prime
hover your mouse over prime for more info
-/
open Nat

/-
begin block is now ':= by' in Lean4 version
end block is now the whitespace indentation after the 'by' clause
theorem name: infinitude_of_primes
-/
theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  --this is an example of a tactic which are the steps of the theorem
  --you can click before and after the tactic to see what has changed
  intro N

  let M := N ! + 1
  let p := minFac M

  have pp : Nat.Prime p := by
    refine Nat.minFac_prime ?_
    have : factorial N > 0 := factorial_pos N
    omega

  use p
  constructor
  · by_contra h
    have h₁ : p ∣ factorial N + 1 := by exact minFac_dvd M
    have h₂ : p ∣ factorial N := by
      exact (Prime.dvd_factorial pp).mpr (by exact Nat.le_of_not_ge h)
    have h₃ : p ∣ 1 := by exact (Nat.dvd_add_iff_right h₂).mpr h₁
    exact pp.not_dvd_one h₃
  · exact (irreducible_iff_nat_prime p).mp pp

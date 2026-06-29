/-
import the math library to access prime definitions
prime library has the theorem inside it
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorial.Basic
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

  have pp : Nat.Prime p := sorry

  use p
  constructor
  { by_contra h
    have h1 : p ∣ factorial N + 1 := library_search
    have h2 : p ∣ factorial N := refine pp.dvd_fact.mpr
    have h3 : p ∣ 1 := by library_search
    library_search }
  { library_search }

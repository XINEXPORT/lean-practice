import Mathlib.Tactic

/-
Proposition: (p ∨ q → r) ↔ (p → r) ∧ (q → r)

Proof:
(⇒) Assume h : p ∨ q → r.
  - To show p → r: assume p (hp). Then p ∨ q holds (left disjunct),
    so h applied to it gives r.
  - To show q → r: assume q (hq). Then p ∨ q holds (right disjunct),
    so h applied to it gives r.
  Hence (p → r) ∧ (q → r).

(⇐) Assume h : (p → r) ∧ (q → r) and p ∨ q (hpq).
  By case analysis on p ∨ q (hpq):
  - If p holds (hp), the first component of h applied to it gives r.
  - If q holds (hq), the second component of h applied to it gives r.
  In either case r holds.
-/

example (p q r : Prop) : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) := by
  constructor
  · intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq
  · intro h hpq
    cases hpq with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

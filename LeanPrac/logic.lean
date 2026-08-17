import Mathlib.Tactic

-- De Morgan's law for three variables
example (p q r : Prop) : ¬(p ∨ q ∨ r) ↔ ¬p ∧ ¬q ∧ ¬r := by
  tauto

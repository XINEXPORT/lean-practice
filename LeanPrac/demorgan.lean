import Mathlib.Tactic

-- De Morgan's law for three variables: ¬(p ∨ q ∨ r) ↔ ¬p ∧ ¬q ∧ ¬r
-- `tauto` case-splits on all propositional possibilities, i.e. the truth table.
example (p q r : Prop) : ¬(p ∨ q ∨ r) ↔ ¬p ∧ ¬q ∧ ¬r := by
  tauto

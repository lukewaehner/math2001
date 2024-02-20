import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


-- De Morgan's Law
#truth_table ¬(P ∨ Q)
#truth_table (¬P ∧ ¬Q)


example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  sorry



-- Exercise 5.1.7 #11
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  sorry


-- Exercise 5.3.6 #2
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  sorry

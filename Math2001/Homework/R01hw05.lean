/- Adapted by David Swinarski from files originally created by Heather Macbeth.
Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
--import Mathlib.Data.Real.Basic
--import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Rel
--import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 5

Don't forget to compare with the text version
for clearer statements and any special instructions.

Questions 1-5 do not have Lean components.-/



@[autograded 4]
theorem problem6 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  intro h
  obtain h1 | h2 := h
  right
  apply h1
  left
  apply h2
  intro h3
  obtain h4 | h5 := h3
  right
  apply h4
  left
  apply h5


@[autograded 5]
theorem problem7 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  intro ha
  obtain ⟨ a1, a2 ⟩ := ha
  obtain ⟨ a, haa ⟩ := a1
  use a
  constructor
  apply haa
  apply a2

  intro hb
  obtain ⟨ b1, b2 ⟩ := hb
  obtain ⟨ bb1, bb2 ⟩ := b2
  constructor
  use b1
  use bb1
  use bb2


@[autograded 4]
theorem problem8 : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by
  constructor
  intro ha

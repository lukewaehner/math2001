/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init



section
local infix:50 "∼" => fun (x y : ℝ) ↦ (x - y) ^ 2 ≤ 1

#check (· ∼ ·)


example : Reflexive (· ∼ ·) := by
  sorry

example : Symmetric (· ∼ ·) := by
  sorry


example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry


example : ¬ Transitive (· ∼ ·) := by
  sorry

end

/- Adapted by David Swinarski from files originally created by Heather Macbeth.  Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
--import Library.Theory.ParityModular

math2001_init

namespace Int

-- Examples for today:
-- 4.1.5, 4.1.6, 4.2.1, 4.3.4, 4.4.3, 4.5.2, 4.5.3



-- Example 4.1.5
example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  sorry



-- Example 4.1.6
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  sorry



-- Example 4.2.1
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  sorry



-- Example 4.3.4
example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  sorry



-- Example 4.4.3
example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  sorry



-- Example 4.5.2
example : ¬ 3 ∣ 13 := by
  sorry



-- Example 4.5.3
example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  sorry

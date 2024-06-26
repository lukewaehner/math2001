/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import AutograderLib

open Function

math2001_init

set_option pp.funBinderTypes true

/-! # Homework 8

Don't forget to compare with the pdf version
for clearer statements and any special instructions.
-/


-- Do 1a or 1b, but not both
-- Comment out or delete the unused portion
@[autograded 4]
theorem problem1a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro b
  use (b/2)
  calc
    2*(b/2) = b := by ring

-- @[autograded 4]
-- theorem problem1b : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
--   sorry

namespace Int

-- Do 2a or 2b, but not both
-- Comment out or delete the unused portion
-- @[autograded 5]
-- theorem problem2a : Surjective (fun (x : ℤ) ↦ 2 * x) := by
--   sorry

@[autograded 5]
theorem problem2b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  have ha := le_or_succ_le a 0
  obtain h1 | h2 := ha
  apply ne_of_lt
  calc
    2*a <= 2 * 0 := by rel[h1]
    _ < 1 := by extra
  apply ne_of_gt
  calc
    2 * a >= 2 * 1 := by rel[h2]
    _ = 1+1 := by ring
    _ > 1 := by extra


end Int


-- Do 3a or 3b, but not both
-- Comment out or delete the unused portion
@[autograded 5]
theorem problem3a : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  dsimp [Injective]
  intro a b c d e
  have h2: a c = a d := by addarith[e]
  apply b at h2
  apply h2

-- @[autograded 5]
-- theorem problem3b : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
--   sorry


@[autograded 5]
theorem problem4 {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
    dsimp [Surjective]
    intro c
    obtain ⟨b, h1⟩  := hg c
    obtain ⟨a, h2⟩  := hf b
    use a
    calc
      (g ∘ f) a = g (f a) := by rfl
      _ = g (b) := by rw[h2]
      _ = c := by rw[h1]


-- Do 5a or 5b, but not both
-- Comment out or delete the unused portion
@[autograded 4]
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  dsimp [Injective]
  intro a b h1
  have h2 : -3*a = -3*b := by addarith[h1]
  cancel -3 at h2

  dsimp [Surjective]
  intro b
  use ((4-b)/3)
  calc
    4 - 3 * ((4-b) / 3) = b := by ring


-- @[autograded 4]
-- theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
--   sorry


@[autograded 4]
theorem problem6 : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by
  dsimp [Surjective]
  intro c
  use (c, 1)
  ring

@[autograded 4]
theorem problem7 : ¬ Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective]
  push_neg
  use (0,0,0)
  use (2, -4, 2)
  constructor
  numbers
  numbers

@[autograded 4]
theorem problem8 : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc
    -1 < 0 := by numbers
    _ <= x.1^ 2 + x.2 ^ 2 := by extra


@[autograded 4]
theorem problem9 : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (b+a,a)
  constructor
  · ext ⟨ r , s ⟩
    dsimp
    ring
  · ext ⟨ a, b ⟩
    dsimp
    ring

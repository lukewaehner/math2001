/- Adapted by David Swinarski from files originally created by Heather Macbeth. Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def q (x : ℝ) : ℝ := 2*x + 5


#check @q -- infoview displays `q : ℝ → ℝ`


example : Injective q := by
  sorry


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  sorry


 example : Surjective q := by
  sorry


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  sorry


example : Bijective q := by
  sorry



--def q (x : ℝ) : ℝ := 2*x + 5
def r (x : ℝ) : ℝ := x^2+1
def s (x : ℝ) : ℝ := 4*x^2+20*x+26



example : r ∘ q = s := by
  sorry




def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

#check @q -- infoview displays `q : ℝ → ℝ`

def t (x : ℝ) : ℝ := (x-5)/2


#check @t -- infoview displays `q : ℝ → ℝ`

example : Inverse q t := by
  sorry

/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Real.StarOrdered

/-! Convexity of the two real hinge functions. -/
@[expose] public section

open Set

lemma convexOn_hinge_right (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ => max (z - a) 0) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  change max (u * x + v * y - a) 0 ≤
    u * max (x - a) 0 + v * max (y - a) 0
  refine max_le ?_ ?_
  · calc
      u * x + v * y - a = u * (x - a) + v * (y - a) := by
        have ha : u * a + v * a = a := by
          calc
            u * a + v * a = (u + v) * a := by ring
            _ = a := by rw [huv, one_mul]
        calc
          u * x + v * y - a = u * x + v * y - (u * a + v * a) := by rw [ha]
          _ = u * (x - a) + v * (y - a) := by ring
      _ ≤ u * max (x - a) 0 + v * max (y - a) 0 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
  · exact add_nonneg
      (mul_nonneg hu (le_max_right _ _))
      (mul_nonneg hv (le_max_right _ _))

lemma convexOn_hinge_left (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ => max (a - z) 0) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  change max (a - (u * x + v * y)) 0 ≤
    u * max (a - x) 0 + v * max (a - y) 0
  refine max_le ?_ ?_
  · calc
      a - (u * x + v * y) = u * (a - x) + v * (a - y) := by
        have ha : u * a + v * a = a := by
          calc
            u * a + v * a = (u + v) * a := by ring
            _ = a := by rw [huv, one_mul]
        calc
          a - (u * x + v * y) = (u * a + v * a) - (u * x + v * y) := by rw [ha]
          _ = u * (a - x) + v * (a - y) := by ring
      _ ≤ u * max (a - x) 0 + v * max (a - y) 0 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
  · exact add_nonneg
      (mul_nonneg hu (le_max_right _ _))
      (mul_nonneg hv (le_max_right _ _))

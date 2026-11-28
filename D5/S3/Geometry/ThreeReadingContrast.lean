/- GID: D5/S3/Geometry/ThreeReadingContrast
   generality: G
   mirror-B: none(waiver:covered-by-three-reading-contrast-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attainable differences between two nonnegative readings of a normalized three-point Gram form. -/

module

import OmegaBuild.Commands
public import Mathlib.Algebra.Order.Ring.Basic
meta import Mathlib.Tactic.Linarith.Frontend

/-!
Omega original.

Attainable differences between two nonnegative readings of a normalized three-point Gram form.
-/

compile_only_with_mathlib

public section

namespace Omega.Geometry.ThreeReadingContrast

/-- At fixed mutual reading `r`, the differences `d` between nonnegative readings
against a third point are exactly those satisfying `r ^ 2 + d ^ 2 ≤ 1`.
The Gram form is required to be nonnegative on every weight vector over `R`. -/
theorem exists_nonnegative_readings_iff {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (r d : R) :
    (∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a - b = d ∧
      ∀ x y z : R, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)) ↔
    r ^ 2 + d ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl, gram⟩
    have hr : r ≤ 1 := by nlinarith only [gram 1 (-1) 0]
    rcases le_total b a with hab | hba
    · have residual := gram 1 (-r) (-(a - b))
      have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) hb) (sub_nonneg.mpr hab)
      nlinarith only [residual, correction]
    · have residual := gram (-r) 1 (a - b)
      have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) ha) (sub_nonneg.mpr hba)
      nlinarith only [residual, correction]
  · intro hd
    have slack : 0 ≤ 1 - r ^ 2 - d ^ 2 := by linarith
    rcases le_total 0 d with h | h
    · refine ⟨d, 0, h, le_rfl, sub_zero _, ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (y + r * x), sq_nonneg (z + d * x), mul_nonneg slack (sq_nonneg x)]
    · refine ⟨0, -d, le_rfl, neg_nonneg.mpr h, by rw [zero_sub, neg_neg], ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (x + r * y), sq_nonneg (z - d * y), mul_nonneg slack (sq_nonneg y)]

end Omega.Geometry.ThreeReadingContrast

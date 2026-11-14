/- GID: D5/S3/Analytic/Convexity/StrictConcaveSymmetricSum
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/StrictConcaveSymmetricSum
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: Strict concavity orders symmetric pairs with a common center. -/

import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-! Symmetric sums of a strictly concave real function on the positive half-line. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum

open Set

/-- Strict concavity compares two symmetric pairs with the same center.
    Both inner points are strict convex combinations of the outer pair. -/
theorem strictConcave_symmetric_sum {h : ℝ → ℝ}
    (hh : StrictConcaveOn ℝ (Ioi (0 : ℝ)) h)
    {r s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) :
    h (r - t) + h (r + t) < h (r - s) + h (r + s) := by
  have ht : 0 < t := hs.trans_lt hst
  have hden : 0 < 2 * t := by positivity
  let α := (t + s) / (2 * t)
  let β := (t - s) / (2 * t)
  have hα : 0 < α := div_pos (by linarith) hden
  have hβ : 0 < β := div_pos (sub_pos.mpr hst) hden
  have hab : α + β = 1 := by dsimp [α, β]; field_simp [ne_of_gt ht]; ring
  have hx : r - t ∈ Ioi (0 : ℝ) := sub_pos.mpr htr
  have hy : r + t ∈ Ioi (0 : ℝ) := by change 0 < r + t; linarith
  have hxy : r - t ≠ r + t := by linarith
  have hm : α * (r - t) + β * (r + t) = r - s := by
    dsimp [α, β]
    field_simp [ne_of_gt ht]
    ring
  have hp : β * (r - t) + α * (r + t) = r + s := by
    dsimp [α, β]
    field_simp [ne_of_gt ht]
    ring
  have h₁ := hh.2 hx hy hxy hα hβ hab
  have h₂ := hh.2 hx hy hxy hβ hα (by linarith : β + α = 1)
  simp only [smul_eq_mul, hm, hp] at h₁ h₂
  have hsum :
      (α * h (r - t) + β * h (r + t)) +
        (β * h (r - t) + α * h (r + t)) = h (r - t) + h (r + t) := by
    calc
      _ = (α + β) * h (r - t) + (α + β) * h (r + t) := by ring
      _ = _ := by rw [hab]; ring
  rw [← hsum]
  exact add_lt_add h₁ h₂

end D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum

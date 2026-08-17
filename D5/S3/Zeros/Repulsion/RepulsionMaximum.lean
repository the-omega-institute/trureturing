/- GID: D5/S3/Zeros/Repulsion/RepulsionMaximum
   generality: G
   mirror-B: D5/B/S3/Zeros/Repulsion/RepulsionMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive rational repulsion profile attains its exact square-root maximum. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace D5.S3.Zeros.Repulsion.RepulsionMaximum

/-- The profile `a / (w + u) - b / w` on positive `w` has the exact
maximum `(sqrt a - sqrt b)^2 / u` when `0 < b < a` and `0 < u`. -/
theorem repulsion_profile_has_exact_maximum (a b u : ℝ)
    (hab : b < a) (hb : 0 < b) (hu : 0 < u) :
    IsGreatest
      {y : ℝ | ∃ w : ℝ, 0 < w ∧ y = a / (w + u) - b / w}
      ((Real.sqrt a - Real.sqrt b) ^ 2 / u) := by
  let A := Real.sqrt a
  let B := Real.sqrt b
  have ha : 0 < a := lt_trans hb hab
  have hA : 0 < A := by simp [A, Real.sqrt_pos.2 ha]
  have hB : 0 < B := by simp [B, Real.sqrt_pos.2 hb]
  have hAsq : A ^ 2 = a := by simpa [A] using Real.sq_sqrt ha.le
  have hBsq : B ^ 2 = b := by simpa [B] using Real.sq_sqrt hb.le
  have hBA : B < A := by nlinarith
  have hdiff : 0 < A - B := sub_pos.mpr hBA
  have hidentity (w : ℝ) (hw : w ≠ 0) (hwu : w + u ≠ 0) :
      (A - B) ^ 2 / u - (a / (w + u) - b / w) =
        ((A - B) * w - B * u) ^ 2 / (u * w * (w + u)) := by
    rw [← hAsq, ← hBsq]
    field_simp [hu.ne', hw, hwu]
    ring
  change IsGreatest
    {y : ℝ | ∃ w : ℝ, 0 < w ∧ y = a / (w + u) - b / w}
    ((A - B) ^ 2 / u)
  constructor
  · let w₀ := B * u / (A - B)
    have hw₀ : 0 < w₀ := div_pos (mul_pos hB hu) hdiff
    have hw₀u : 0 < w₀ + u := add_pos hw₀ hu
    have hnum : (A - B) * w₀ - B * u = 0 := by
      dsimp [w₀]
      field_simp [hdiff.ne']
      ring
    refine ⟨w₀, hw₀, ?_⟩
    have heq := hidentity w₀ hw₀.ne' hw₀u.ne'
    rw [hnum] at heq
    have heq_zero :
        (A - B) ^ 2 / u - (a / (w₀ + u) - b / w₀) = 0 := by
      simpa using heq
    exact sub_eq_zero.mp heq_zero
  · rintro y ⟨w, hw, rfl⟩
    have hwu : 0 < w + u := add_pos hw hu
    have heq := hidentity w hw.ne' hwu.ne'
    have hden : 0 < u * w * (w + u) := mul_pos (mul_pos hu hw) hwu
    have hnonneg :
        0 ≤ ((A - B) * w - B * u) ^ 2 / (u * w * (w + u)) :=
      div_nonneg (sq_nonneg _) hden.le
    linarith

end D5.S3.Zeros.Repulsion.RepulsionMaximum

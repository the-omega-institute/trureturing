/- GID: D5/S3/Fourier/GoldenReciprocityFixedPoint
   generality: I
   mirror-B: D5/B/S3/Fourier/GoldenReciprocityFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden reciprocity determines the value at the reciprocal fixed point. -/

/- Library-search audit trail (2026-08-17):
   * D5 searches found the related reciprocal-antisymmetry theorem
     `metallic_reciprocal_symmetry_forces_balance`, but no affine reciprocity
     theorem or equivalent conclusion.
   * Pinned Mathlib supplies `Real.goldenRatio_irrational`,
     `Real.inv_goldenRatio`, and `Real.goldenRatio_add_goldenConj`; these are
     applied below instead of re-proving the golden fixed-point identities.
   * Loogle returned no declarations for the combined `Function.Periodic` and
     `Real.goldenRatio` query (HTTP 200). LeanSearch `/api/search` returned
     HTTP 404, and no local `loogle` executable is installed.
-/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Ring.Periodic

namespace D5.S3.Fourier.GoldenReciprocityFixedPoint

/-- Let `c` be unit-periodic and let `g` satisfy the irrational-point
reciprocity law `g(x) = x * c(x) + c(x⁻¹)`. At the reciprocal golden ratio,
the reciprocal argument is one period away, so the law becomes a scalar
equation and determines `c` there exactly. -/
theorem golden_reciprocity_fixed_point (c g : ℝ → ℝ)
    (hperiodic : Function.Periodic c 1)
    (hreciprocity : ∀ x : ℝ, Irrational x →
      g x = x * c x + c (x⁻¹)) :
    c Real.goldenRatio⁻¹ * (Real.goldenRatio⁻¹ + 1) =
        g Real.goldenRatio⁻¹ ∧
      c Real.goldenRatio⁻¹ =
        g Real.goldenRatio⁻¹ / Real.goldenRatio := by
  let x := Real.goldenRatio⁻¹
  have hx_irrational : Irrational x := by
    exact Real.goldenRatio_irrational.inv
  have hphi : Real.goldenRatio = x + 1 := by
    simp only [x, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hx_inv : x⁻¹ = x + 1 := by
    calc
      x⁻¹ = Real.goldenRatio := by simp [x]
      _ = x + 1 := hphi
  have hc_inv : c (x⁻¹) = c x := by
    rw [hx_inv]
    exact hperiodic x
  have hfactor : c x * (x + 1) = g x := by
    rw [hreciprocity x hx_irrational, hc_inv]
    ring
  have hfactor_phi : c x * Real.goldenRatio = g x := by
    rw [hphi]
    exact hfactor
  have hvalue : c x = g x / Real.goldenRatio := by
    calc
      c x = (c x * Real.goldenRatio) / Real.goldenRatio := by
        exact (eq_div_iff Real.goldenRatio_ne_zero).2 rfl
      _ = g x / Real.goldenRatio := by rw [hfactor_phi]
  exact ⟨hfactor, hvalue⟩

#print axioms golden_reciprocity_fixed_point

end D5.S3.Fourier.GoldenReciprocityFixedPoint

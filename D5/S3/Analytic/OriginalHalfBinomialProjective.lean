/- GID: D5/S3/Analytic/OriginalHalfBinomialProjective
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialProjective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual third-order regularity and Schwarzian of the original complementary period ratio on the full lens. -/

import D5.S3.Analytic.AbelRatioSchwarzian
import D5.S3.Analytic.OriginalHalfBinomialWronskian

/-! The literal original period ratio is the native instance of the Abel-ratio
inference. All ODE, differentiability and nonvanishing data are obtained from
the existing original-period results and the two strict lens inequalities. -/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace D5.S3.Analytic.OriginalHalfBinomialProjective

open OriginalHalfBinomialPeriod (period)
open OriginalHalfBinomialWronskian (tau)
open AbelRatioSchwarzian (preSchwarzian schwarzian)

private def lens : Set ℂ := {r | ‖r‖ < 1 ∧ ‖1 - r‖ < 1}

private lemma lens_open : IsOpen lens :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const)

private lemma lens_factors {r : ℂ} (hr : r ∈ lens) : r ≠ 0 ∧ 1 - r ≠ 0 := by
  constructor
  · intro he
    simpa [he] using hr.2
  · intro he
    have h1 : r = 1 := by linear_combination -he
    simpa [h1] using hr.1

/-- Nonzero actual first derivative, actual second and third derivative
regularity, and the exact Schwarzian. The only endpoint premises are membership
in the full open lens. -/
theorem original_tau_projective {r : ℂ} (hr : ‖r‖ < 1) (hc : ‖1 - r‖ < 1) :
    deriv tau r ≠ 0 ∧
      HasDerivAt (deriv tau)
        ((-(1 - 2 * r) / (r * (1 - r)) - 2 * (deriv period r / period r)) *
          deriv tau r) r ∧
      DifferentiableAt ℂ (deriv (deriv tau)) r ∧
      preSchwarzian tau r =
        -(1 - 2 * r) / (r * (1 - r)) - 2 * (deriv period r / period r) ∧
      schwarzian tau r = (1 - r + r ^ 2) / (2 * r ^ 2 * (1 - r) ^ 2) := by
  let A : ℂ → ℂ := fun z => z * (1 - z)
  let p : ℂ → ℂ := fun z => (1 - 2 * z) / A z
  let q : ℂ → ℂ := fun z => -1 / (4 * A z)
  let W : ℂ → ℂ := fun z => -Complex.I / ((Real.pi : ℂ) * A z)
  have hA0 (z : ℂ) (hz : z ∈ lens) : A z ≠ 0 :=
    mul_ne_zero (lens_factors hz).1 (lens_factors hz).2
  have hA (z : ℂ) : HasDerivAt A (1 - 2 * z) z := by
    convert (hasDerivAt_id z).mul ((hasDerivAt_id z).const_sub 1) using 1
    · rfl
    · dsimp
      ring
  have hp (z : ℂ) (hz : z ∈ lens) :
      HasDerivAt p ((-2 * A z - (1 - 2 * z) ^ 2) / A z ^ 2) z := by
    convert (((hasDerivAt_id z).const_mul 2).const_sub 1).div (hA z) (hA0 z hz)
      using 1
    · funext w
      dsimp [p]
    · dsimp
      ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hy (z : ℂ) (hz : z ∈ lens) := OriginalHalfBinomialPeriod.picard_fuchs hz.1
  have hy0 (z : ℂ) (hz : z ∈ lens) :=
    D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero hz.1
  have hW (z : ℂ) (hz : z ∈ lens) : HasDerivAt W (-p z * W z) z := by
    have hd := (hasDerivAt_const z (-Complex.I)).div ((hA z).const_mul (Real.pi : ℂ))
      (mul_ne_zero hpi (hA0 z hz))
    convert hd using 1
    dsimp [p, W]
    field_simp [hpi, hA0 z hz]
    <;> ring
  have hW0 (z : ℂ) (hz : z ∈ lens) : W z ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (mul_ne_zero hpi (hA0 z hz))
  have ht (z : ℂ) (hz : z ∈ lens) : HasDerivAt tau (W z / period z ^ 2) z := by
    convert (OriginalHalfBinomialWronskian.original_tau_hasDerivAt hz.1 hz.2).2 using 1
    dsimp [W, A]
    field_simp [hpi, (lens_factors hz).1, (lens_factors hz).2, hy0 z hz]
    <;> ring
  have hODE (z : ℂ) (hz : z ∈ lens) :
      deriv (deriv period) z + p z * deriv period z + q z * period z = 0 := by
    dsimp [p, q]
    field_simp [hA0 z hz]
    dsimp [A]
    linear_combination 4 * (hy z hz).2.2
  have h := AbelRatioSchwarzian.abel_ratio_schwarzian lens lens_open period p q W tau
    (fun z hz => ⟨(hy z hz).1, (hy z hz).2.1⟩) hy0
    (fun z hz => (hp z hz).differentiableAt) hW hW0 ht hODE (show r ∈ lens from ⟨hr, hc⟩)
  have hpr : deriv p r = (-2 * A r - (1 - 2 * r) ^ 2) / A r ^ 2 :=
    (hp r ⟨hr, hc⟩).deriv
  refine ⟨h.1, ?_, h.2.2.1.differentiableAt, ?_, ?_⟩
  · simpa only [p, A, neg_div] using h.2.1
  · simpa only [p, A, neg_div] using h.2.2.2.1
  · rw [h.2.2.2.2, hpr]
    dsimp [p, q, A]
    obtain ⟨hr0, hc0⟩ := lens_factors (show r ∈ lens from ⟨hr, hc⟩)
    field_simp [hr0, hc0]
    <;> ring

end D5.S3.Analytic.OriginalHalfBinomialProjective

/- GID: D5/S3/Weil/ZetaAnalytic/ProjectiveRayleighRouche
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/ProjectiveRayleighRouche
   mirror-E: none(waiver:variational-to-analytic-boundary-bridge)
   anchors: []
   digest: Transfer a proved projective eigenline enclosure through bounded linear readouts to the existing rectangle zero-count theorem. -/

import D5.S3.Weil.ZetaLinear.ProjectiveRayleighCapture
import D5.S3.Weil.ZetaAnalytic.RoucheZeroCount
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# From the actual variational enclosure to a rectangle zero count

The readout is a genuine bounded linear functional on the Hilbert space at
each spectral parameter. Its parameter dependence must satisfy the stated
analyticity assumptions. The boundary lower estimate is retained explicitly.
This module neither manufactures a completed-zeta function nor assumes that
its boundary is automatically protected by a spectral gap.

The intended Fourier application needs its actual fixed-support L2 readout
and its operator norm bound. A symbolic family of functionals does not by
itself discharge that identification or the rectangle boundary inequality.
The existing rectangle Rouché theorem owns multiplicity counting throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaAnalytic.ProjectiveRayleighRouche

open Complex Set Topology BigOperators
open D5.S3.Weil.ZetaLinear.ProjectiveRayleighCapture
open D5.S3.Weil.ZetaAnalytic.RoucheZeroCount

/-- Squared Hilbert-space error propagates through a bounded linear readout.
Keeping the squared form avoids introducing a numerical square-root oracle. -/
theorem bounded_linear_readout_error_sq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : H →L[ℂ] ℂ) (x y : H) (radiusSq : ℝ)
    (herror : ‖x - y‖ ^ 2 ≤ radiusSq) :
    ‖L x - L y‖ ^ 2 ≤ ‖L‖ ^ 2 * radiusSq := by
  have hnorm : ‖L x - L y‖ ≤ ‖L‖ * ‖x - y‖ := by
    simpa only [map_sub] using L.le_opNorm (x - y)
  have hsquare : ‖L x - L y‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖x - y‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact hsquare.trans (mul_le_mul_of_nonneg_left herror (sq_nonneg _))

/-- An actual boundary margin converts the squared error into the strict
pointwise inequality consumed by the repository's Rouché theorem. -/
theorem bounded_linear_readout_rouche_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : H →L[ℂ] ℂ) (x y : H) (radiusSq : ℝ)
    (herror : ‖x - y‖ ^ 2 ≤ radiusSq)
    (hboundary : ‖L‖ ^ 2 * radiusSq < ‖L y‖ ^ 2) :
    ‖L x - L y‖ < ‖L y‖ := by
  have hsq := (bounded_linear_readout_error_sq L x y radiusSq herror).trans_lt
    hboundary
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A complex operator-domain Rayleigh enclosure supplies the error term in
an actual rectangle zero-count comparison. The candidate's boundary margin
and the two analytic zero lists remain explicit and are not inferred from
low energy. Zeros are counted by the existing analytic multiplicity owner. -/
theorem projective_rayleigh_rectangle_zero_count
    {H D : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D)
    (lower upper threshold eigenvalue : ℝ)
    (symmetricOnDomain : ∀ x y : D,
      ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (candidateNormalized : ‖ι k‖ = 1)
    (eigenvectorNonzero : ι u ≠ 0)
    (eigenEquation : A u = (eigenvalue : ℂ) • ι u)
    (eigenLower : lower ≤ eigenvalue)
    (eigenBelowThreshold : eigenvalue < threshold)
    (candidateUpper : (⟪ι k, A k⟫_ℂ).re ≤ upper)
    (upperBelowThreshold : upper < threshold)
    (complementCoercive : ∀ f : D,
      ⟪ι k, ι f⟫_ℂ = 0 →
        threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (readout : ℂ → H →L[ℂ] ℂ) (z w : ℂ)
    (hre : z.re < w.re) (him : z.im < w.im)
    (huAnalytic : AnalyticOnNhd ℂ
      (fun s => readout s (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u))) (Rectangle z w))
    (hkAnalytic : AnalyticOnNhd ℂ
      (fun s => readout s (ι k)) (Rectangle z w))
    (boundaryMargin : ∀ s ∈ RectangleBorder z w,
      ‖readout s‖ ^ 2 * ((upper - lower) / (threshold - lower)) <
        ‖readout s (ι k)‖ ^ 2)
    (Zu Zk : Finset ℂ)
    (hZu : ∀ s ∈ Rectangle z w,
      readout s (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u)) = 0 ↔ s ∈ Zu)
    (hZusub : (Zu : Set ℂ) ⊆ Rectangle z w)
    (hZk : ∀ s ∈ Rectangle z w, readout s (ι k) = 0 ↔ s ∈ Zk)
    (hZksub : (Zk : Set ℂ) ⊆ Rectangle z w) :
    ⟪ι k, ι u⟫_ℂ ≠ 0 ∧
      (∑ ρ ∈ Zu, analyticOrderNatAt
        (fun s => readout s (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u))) ρ) =
      ∑ ρ ∈ Zk, analyticOrderNatAt (fun s => readout s (ι k)) ρ := by
  obtain ⟨ha, _, herr, _⟩ := projective_rayleigh_enclosure ι A k u
    lower upper threshold eigenvalue symmetricOnDomain candidateNormalized
    eigenvectorNonzero eigenEquation eigenLower eigenBelowThreshold candidateUpper
    upperBelowThreshold complementCoercive
  have herror :
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) - ι k‖ ^ 2 ≤
        (upper - lower) / (threshold - lower) := by
    simpa only [map_sub] using herr
  refine ⟨ha, ?_⟩
  apply rectangle_zero_count_eq_of_norm_sub_lt hre him huAnalytic hkAnalytic
    (fun s hs => bounded_linear_readout_rouche_bound (readout s)
      (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u)) (ι k)
      ((upper - lower) / (threshold - lower)) herror (boundaryMargin s hs))
    Zu Zk hZu hZusub hZk hZksub

#print axioms bounded_linear_readout_error_sq
#print axioms bounded_linear_readout_rouche_bound
#print axioms projective_rayleigh_rectangle_zero_count

end D5.S3.Weil.ZetaAnalytic.ProjectiveRayleighRouche

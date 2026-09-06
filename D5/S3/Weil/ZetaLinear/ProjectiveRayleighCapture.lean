/- GID: D5/S3/Weil/ZetaLinear/ProjectiveRayleighCapture
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/ProjectiveRayleighCapture
   mirror-E: none(waiver:operator-domain-variational-estimate)
   anchors: []
   digest: A Rayleigh enclosure and codimension-one coercivity control the aligned complex eigenline with denominator threshold minus lower. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Projective Rayleigh capture on an actual operator domain

The domain `D` is only a complex module. Both its embedding and the operator
act from `D` to the Hilbert space; no bounded endomorphism of that Hilbert
space is substituted for an unbounded operator. The eigenvector need not
be normalized, but its embedded vector must be nonzero.

The stronger complex/projective estimate stated on paper in PR #5602 is
proved from the operator equation and symmetry. In particular, neither a
small operator residual nor the desired projective-distance bound is an
input. The exact prime-three consequence uses the scalar endpoints stored
in PR #5602 at b02e0787252c1239cf18c6f39652048a45793f39. It does not prove
their still-separate identification with the arithmetic Weil operator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.ProjectiveRayleighCapture

open scoped ComplexConjugate

/-- Align an eigenvector by its actual candidate overlap. The shifted
operator annihilates the eigenvector, yielding the exact sharp variational
bound before replacing its eigenvalue and candidate energy by endpoints. -/
theorem projective_rayleigh_enclosure
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
        threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    ⟪ι k, ι u⟫_ℂ ≠ 0 ∧
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k)‖ ^ 2 ≤
        ((⟪ι k, A k⟫_ℂ).re - eigenvalue) / (threshold - eigenvalue) ∧
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k)‖ ^ 2 ≤
        (upper - lower) / (threshold - lower) ∧
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k)‖ ^ 2 < 1 := by
  let B : D →ₗ[ℂ] H := A - (eigenvalue : ℂ) • ι
  have applyB (v : D) : B v = A v - (eigenvalue : ℂ) • ι v := rfl
  have symmetricB (x y : D) :
      ⟪ι x, B y⟫_ℂ = ⟪B x, ι y⟫_ℂ := by
    rw [applyB, applyB, inner_sub_right, inner_sub_left,
      inner_smul_right, inner_smul_left, symmetricOnDomain x y]
    simp
  have Bu : B u = 0 := by
    rw [applyB, eigenEquation, sub_self]
  have energyB (v : D) :
      (⟪ι v, B v⟫_ℂ).re =
        (⟪ι v, A v⟫_ℂ).re - eigenvalue * ‖ι v‖ ^ 2 := by
    rw [applyB, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.sub_re, Complex.ofReal_re]
  have eigenEnergy :
      (⟪ι u, A u⟫_ℂ).re = eigenvalue * ‖ι u‖ ^ 2 := by
    have h := energyB u
    rw [Bu, inner_zero_right] at h
    simp only [Complex.zero_re] at h
    linarith
  let alpha : ℂ := ⟪ι k, ι u⟫_ℂ
  have alphaNonzero : alpha ≠ 0 := by
    intro hz
    have hu := complementCoercive u hz
    rw [eigenEnergy] at hu
    have hnorm : 0 < ‖ι u‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr eigenvectorNonzero)
    have hgap := mul_pos (sub_pos.mpr eigenBelowThreshold) hnorm
    nlinarith
  let f : D := alpha⁻¹ • u - k
  have imageF : ι f = alpha⁻¹ • ι u - ι k := by simp [f]
  have actionF : B f = -B k := by simp [f, Bu]
  have orthogonal : ⟪ι k, ι f⟫_ℂ = 0 := by
    rw [imageF, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, candidateNormalized]
    change alpha⁻¹ * alpha - (1 : ℂ) ^ 2 = 0
    rw [inv_mul_cancel₀ alphaNonzero]
    ring
  have crossVanishes : ⟪ι u, B k⟫_ℂ = 0 := by
    rw [symmetricB u k, Bu, inner_zero_left]
  have shiftedIdentity : ⟪ι f, B f⟫_ℂ = ⟪ι k, B k⟫_ℂ := by
    rw [imageF, actionF, inner_sub_left, inner_smul_left]
    simp only [inner_neg_right, crossVanishes, neg_zero, mul_zero,
      zero_sub, neg_neg]
  have realIdentity := congrArg Complex.re shiftedIdentity
  rw [energyB f, energyB k, candidateNormalized] at realIdentity
  have gapBound :
      (threshold - eigenvalue) * ‖ι f‖ ^ 2 ≤
        (⟪ι k, A k⟫_ℂ).re - eigenvalue := by
    have hf := complementCoercive f orthogonal
    nlinarith [realIdentity]
  have gapPositive : 0 < threshold - eigenvalue :=
    sub_pos.mpr eigenBelowThreshold
  have errorBelowOne : ‖ι f‖ ^ 2 < 1 := by
    by_contra h
    have hge : 1 ≤ ‖ι f‖ ^ 2 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hge gapPositive.le
    simp only [mul_one] at hmul
    linarith
  have endpointGapPositive : 0 < threshold - lower := by
    linarith
  have endpointClear :
      (threshold - lower) * ‖ι f‖ ^ 2 ≤ upper - lower := by
    have hprod : 0 ≤ (eigenvalue - lower) * (1 - ‖ι f‖ ^ 2) :=
      mul_nonneg (sub_nonneg.mpr eigenLower)
        (sub_nonneg.mpr errorBelowOne.le)
    nlinarith [gapBound]
  refine ⟨alphaNonzero, ?_, ?_, errorBelowOne⟩
  · apply (le_div_iff₀ gapPositive).mpr
    simpa only [mul_comm] using gapBound
  · apply (le_div_iff₀ endpointGapPositive).mpr
    simpa only [mul_comm] using endpointClear

/-- Exact arithmetic used by the fixed `a=log(3)/2` certificate. The endpoint
numbers are data, not assertions about a particular operator. -/
theorem prime_three_projective_ratio :
    ((560909 / 10000000000000 : ℝ) - 103 / 2000000000) /
        (1 / 200000 - 103 / 2000000000) = 15303 / 16495000 ∧
      (15303 / 16495000 : ℝ) < (61 / 2000) ^ 2 := by
  norm_num

/-- Consume the actual scalar values recorded by the prime-three computation.
Every analytic operator hypothesis remains explicit; the last variational
and arithmetic implication is supplied by this theorem. -/
theorem prime_three_projective_mode_capture
    {H D : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D) (eigenvalue : ℝ)
    (symmetricOnDomain : ∀ x y : D,
      ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (candidateNormalized : ‖ι k‖ = 1)
    (eigenvectorNonzero : ι u ≠ 0)
    (eigenEquation : A u = (eigenvalue : ℂ) • ι u)
    (eigenLower : (103 / 2000000000 : ℝ) ≤ eigenvalue)
    (eigenBelowThreshold : eigenvalue < 1 / 200000)
    (candidateUpper : (⟪ι k, A k⟫_ℂ).re ≤ 560909 / 10000000000000)
    (complementCoercive : ∀ f : D,
      ⟪ι k, ι f⟫_ℂ = 0 →
        (1 / 200000 : ℝ) * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    ⟪ι k, ι u⟫_ℂ ≠ 0 ∧
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k)‖ ^ 2 ≤ 15303 / 16495000 ∧
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k)‖ < 61 / 2000 := by
  obtain ⟨ha, _, hb, _⟩ := projective_rayleigh_enclosure ι A k u
    (103 / 2000000000) (560909 / 10000000000000) (1 / 200000) eigenvalue
    symmetricOnDomain candidateNormalized eigenvectorNonzero eigenEquation
    eigenLower eigenBelowThreshold candidateUpper (by norm_num) complementCoercive
  rw [prime_three_projective_ratio.1] at hb
  refine ⟨ha, hb, ?_⟩
  have hsq := hb.trans_lt prime_three_projective_ratio.2
  have hnorm := norm_nonneg (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k))
  nlinarith

#print axioms projective_rayleigh_enclosure
#print axioms prime_three_projective_ratio
#print axioms prime_three_projective_mode_capture

end D5.S3.Weil.ZetaLinear.ProjectiveRayleighCapture

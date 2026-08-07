/- GID: D5/S3/Quantum/RobertsonSchrodinger
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Preserve the Gram remainder in the Robertson-Schrodinger identity. -/

/-
Library search (mathlib v4.31.0, offline, 2026-08-07):

* `rg "robertson|schrodinger|uncertainty" Mathlib` found no packaged
  Robertson-Schrodinger theorem.
* `norm_inner_le_norm` in `Analysis.InnerProductSpace.Basic` is the packaged
  Cauchy-Schwarz inequality used below.
* `Complex.sq_norm` and `Complex.normSq_apply` identify the squared complex
  norm with the sum of the squared real and imaginary parts.
* `LinearMap.IsSymmetric` and `IsSymmetric.im_inner_self_apply` in
  `Analysis.InnerProductSpace.Symmetric` supply the self-adjointness relation
  and reality of expectations.
-/

import Mathlib.Analysis.InnerProductSpace.Symmetric

namespace D5.S3.Quantum.RobertsonSchrodinger

open scoped InnerProductSpace

/-- The two-vector Gram identity, with its nonnegative wedge remainder kept explicit. -/
theorem gram_wedge_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : E) :
    let G := ‖u‖ ^ 2 * ‖v‖ ^ 2 - ‖⟪u, v⟫_ℂ‖ ^ 2
    ‖u‖ ^ 2 * ‖v‖ ^ 2 = ‖⟪u, v⟫_ℂ‖ ^ 2 + G ∧ 0 ≤ G := by
  dsimp
  constructor
  · ring
  · apply sub_nonneg.mpr
    calc
      ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (norm_inner_le_norm _ _)
      _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring

/-- For symmetric complex-linear operators and a unit vector, the centered vectors satisfy
the Robertson-Schrodinger identity with its Gram remainder, while the real and imaginary
inner-product components give the symmetric covariance and normalized commutator expectation. -/
theorem robertson_schrodinger {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E →ₗ[ℂ] E) (psi : E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hpsi : ‖psi‖ = 1) :
    let u := A psi - ⟪ psi, A psi ⟫_ℂ • psi
    let v := B psi - ⟪ psi, B psi ⟫_ℂ • psi
    let covariance : ℝ :=
      (1 / 2) * (⟪ psi, (A * B + B * A) psi ⟫_ℂ).re -
        (⟪ psi, A psi ⟫_ℂ).re * (⟪ psi, B psi ⟫_ℂ).re
    let commutatorHalf : ℂ :=
      (1 / (2 * Complex.I)) * ⟪ psi, (A * B - B * A) psi ⟫_ℂ
    let G := ‖u‖ ^ 2 * ‖v‖ ^ 2 - ‖⟪ u, v ⟫_ℂ‖ ^ 2
    ‖u‖ ^ 2 * ‖v‖ ^ 2 = covariance ^ 2 + ‖commutatorHalf‖ ^ 2 + G ∧
      0 ≤ G ∧
      (⟪ u, v ⟫_ℂ).re = covariance ∧
      ((⟪ u, v ⟫_ℂ).im : ℂ) = commutatorHalf := by
  dsimp
  have hA_im : (⟪ psi, A psi ⟫_ℂ).im = 0 := hA.im_inner_self_apply psi
  have hB_im : (⟪ psi, B psi ⟫_ℂ).im = 0 := hB.im_inner_self_apply psi
  have hA_apply_im : (⟪ A psi, psi ⟫_ℂ).im = 0 := hA.im_inner_apply_self psi
  have hpsi_inner : ⟪ psi, psi ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have hcenter_re :
      (⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
        B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).re =
        (⟪ A psi, B psi ⟫_ℂ).re -
          (⟪ psi, A psi ⟫_ℂ).re * (⟪ psi, B psi ⟫_ℂ).re := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    rw [hA psi psi, hpsi_inner]
    simp [Complex.mul_re, hA_im, hB_im]
    ring
  have hBA_re : (⟪ B psi, A psi ⟫_ℂ).re = (⟪ A psi, B psi ⟫_ℂ).re := by
    have hre := congrArg Complex.re (inner_conj_symm (A psi) (B psi))
    simpa only [Complex.conj_re] using hre
  have hsymmetric_re :
      (⟪ psi, (A * B + B * A) psi ⟫_ℂ).re =
        2 * (⟪ A psi, B psi ⟫_ℂ).re := by
    change (⟪ psi, A (B psi) + B (A psi) ⟫_ℂ).re =
      2 * (⟪ A psi, B psi ⟫_ℂ).re
    rw [inner_add_right, ← hA psi (B psi), ← hB psi (A psi)]
    simp only [Complex.add_re]
    rw [hBA_re]
    ring
  have hcovariance :
      (⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
        B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).re =
        (1 / 2) * (⟪ psi, (A * B + B * A) psi ⟫_ℂ).re -
          (⟪ psi, A psi ⟫_ℂ).re * (⟪ psi, B psi ⟫_ℂ).re := by
    rw [hcenter_re, hsymmetric_re]
    ring
  have hcenter_im :
      (⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
        B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).im =
        (⟪ A psi, B psi ⟫_ℂ).im := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    rw [hA psi psi, hpsi_inner]
    simp [Complex.mul_im, hA_im, hB_im, hA_apply_im]
  have hBA_im : (⟪ B psi, A psi ⟫_ℂ).im = -(⟪ A psi, B psi ⟫_ℂ).im := by
    have him := congrArg Complex.im (inner_conj_symm (A psi) (B psi))
    simp only [Complex.conj_im] at him
    linarith
  have hcommutator :
      ((⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
        B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).im : ℂ) =
        (1 / (2 * Complex.I)) * ⟪ psi, (A * B - B * A) psi ⟫_ℂ := by
    rw [hcenter_im]
    change ((⟪ A psi, B psi ⟫_ℂ).im : ℂ) =
      (1 / (2 * Complex.I)) * ⟪ psi, A (B psi) - B (A psi) ⟫_ℂ
    rw [inner_sub_right, ← hA psi (B psi), ← hB psi (A psi),
      (inner_conj_symm (B psi) (A psi)).symm]
    apply Complex.ext
    · simp only [Complex.ofReal_re, one_div, mul_inv_rev, Complex.inv_I, neg_mul,
        inner_conj_symm, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.inv_re,
        Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', zero_mul, Complex.I_im,
        Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, mul_zero, sub_self,
        Complex.sub_re, Complex.mul_im, one_mul, zero_add, Complex.sub_im, zero_sub, neg_neg]
      rw [hBA_im]
      ring
    · simp only [Complex.ofReal_im, one_div, mul_inv_rev, Complex.inv_I, neg_mul,
        inner_conj_symm, Complex.neg_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
        Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', zero_mul,
        Complex.I_im, Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, mul_zero,
        sub_self, Complex.sub_im, one_mul, zero_add, Complex.sub_re, zero_eq_neg,
        mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
      rw [hBA_re]
      ring
  have hgram := gram_wedge_identity
    (A psi - ⟪ psi, A psi ⟫_ℂ • psi)
    (B psi - ⟪ psi, B psi ⟫_ℂ • psi)
  dsimp only at hgram
  refine ⟨?_, hgram.2, hcovariance, hcommutator⟩
  calc
    ‖A psi - ⟪ psi, A psi ⟫_ℂ • psi‖ ^ 2 *
        ‖B psi - ⟪ psi, B psi ⟫_ℂ • psi‖ ^ 2 =
        ‖⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
          B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ‖ ^ 2 +
          (‖A psi - ⟪ psi, A psi ⟫_ℂ • psi‖ ^ 2 *
            ‖B psi - ⟪ psi, B psi ⟫_ℂ • psi‖ ^ 2 -
            ‖⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
              B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ‖ ^ 2) := hgram.1
    _ = (⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
          B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).re ^ 2 +
        (⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
          B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).im ^ 2 +
          (‖A psi - ⟪ psi, A psi ⟫_ℂ • psi‖ ^ 2 *
            ‖B psi - ⟪ psi, B psi ⟫_ℂ • psi‖ ^ 2 -
            ‖⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
              B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ‖ ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    _ = ((1 / 2) * (⟪ psi, (A * B + B * A) psi ⟫_ℂ).re -
          (⟪ psi, A psi ⟫_ℂ).re * (⟪ psi, B psi ⟫_ℂ).re) ^ 2 +
        ‖(1 / (2 * Complex.I)) * ⟪ psi, (A * B - B * A) psi ⟫_ℂ‖ ^ 2 +
          (‖A psi - ⟪ psi, A psi ⟫_ℂ • psi‖ ^ 2 *
            ‖B psi - ⟪ psi, B psi ⟫_ℂ • psi‖ ^ 2 -
            ‖⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
              B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ‖ ^ 2) := by
      rw [hcovariance]
      have hnorm := congrArg norm hcommutator
      simp only [Complex.norm_real, Real.norm_eq_abs] at hnorm
      have him_sq :
          (⟪ A psi - ⟪ psi, A psi ⟫_ℂ • psi,
            B psi - ⟪ psi, B psi ⟫_ℂ • psi ⟫_ℂ).im ^ 2 =
            ‖(1 / (2 * Complex.I)) * ⟪ psi, (A * B - B * A) psi ⟫_ℂ‖ ^ 2 := by
        rw [← sq_abs, hnorm]
      rw [him_sq]

end D5.S3.Quantum.RobertsonSchrodinger

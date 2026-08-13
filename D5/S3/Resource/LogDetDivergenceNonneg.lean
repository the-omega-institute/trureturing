/- GID: D5/S3/Resource/LogDetDivergenceNonneg
   generality: G
   mirror-B: D5/B/S3/Resource/LogDetDivergenceNonneg
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove nonnegativity of the log-determinant divergence for positive-definite matrices. -/

import D5.S3.Resource.LogDetDivergence

namespace D5.S3.Resource.LogDetDivergence

open scoped ComplexOrder MatrixOrder

theorem logDetDivergence_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hρ : rho.PosSemidef) (hρu : IsUnit rho)
    (hσ : sigma.PosSemidef) (hσu : IsUnit sigma) :
    0 ≤ logDetDivergence rho sigma := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hρ_pos : rho.PosDef := hρ.posDef_iff_isUnit.mpr hρu
  let s : Matrix n n ℂ := CFC.sqrt sigma
  let A : Matrix n n ℂ := s⁻¹ * rho * s⁻¹
  have hsigma_nonneg : (0 : Matrix n n ℂ) ≤ sigma :=
    Matrix.nonneg_iff_posSemidef.mpr hσ
  have hs_sq : s * s = sigma := by
    exact CFC.sqrt_mul_sqrt_self sigma hsigma_nonneg
  have hs_star : Matrix.conjTranspose s = s := by
    simpa [s, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg sigma).isSelfAdjoint.star_eq
  have hs_unit : IsUnit s := by
    change IsUnit (CFC.sqrt sigma)
    exact (CFC.isUnit_sqrt_iff sigma hsigma_nonneg).mpr hσu
  have hs_inv_unit : IsUnit s⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hs_unit
  have hs_inv_mul : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s (by
    exact (Matrix.isUnit_iff_isUnit_det s).mp hs_unit)
  have hs_mul_inv : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s (by
    exact (Matrix.isUnit_iff_isUnit_det s).mp hs_unit)
  have hs_isHermitian : s.IsHermitian := hs_star
  have hs_inv_star : Matrix.conjTranspose (s⁻¹) = s⁻¹ := by
    exact hs_isHermitian.inv
  have hA_pos : A.PosDef := by
    rw [show A = star (s⁻¹) * rho * s⁻¹ by simp [A, Matrix.star_eq_conjTranspose, hs_inv_star]]
    exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hs_inv_unit).mpr hρ_pos
  have hsigma_inv : sigma⁻¹ = s⁻¹ * s⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hs_sq]
    calc
      s * s * (s⁻¹ * s⁻¹) = s * (s * s⁻¹) * s⁻¹ := by noncomm_ring
      _ = s * s⁻¹ := by simp only [hs_mul_inv, Matrix.mul_one]
      _ = 1 := hs_mul_inv
  have hsim : sigma⁻¹ * rho = s⁻¹ * A * s := by
    simp [A, hsigma_inv, Matrix.mul_assoc, hs_inv_mul]
  have htrace : (sigma⁻¹ * rho).trace.re = A.trace.re := by
    rw [hsim]
    exact congrArg Complex.re <| calc
      (s⁻¹ * A * s).trace = (s * s⁻¹ * A).trace := Matrix.trace_mul_cycle _ _ _
      _ = A.trace := by simp [hs_mul_inv]
  have hdet : (sigma⁻¹ * rho).det.re = A.det.re := by
    have hsdet : s.det * (s⁻¹).det = 1 := by
      rw [← Matrix.det_mul, hs_mul_inv, Matrix.det_one]
    have hdet_complex : (s⁻¹ * A * s).det = A.det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        (s⁻¹).det * A.det * s.det = A.det * (s.det * (s⁻¹).det) := by ring
        _ = A.det := by rw [hsdet, mul_one]
    rw [hsim]
    exact congrArg Complex.re hdet_complex
  let e := hA_pos.isHermitian
  have htraceA : A.trace.re = ∑ i, e.eigenvalues i := by
    have h := Matrix.IsHermitian.trace_eq_sum_eigenvalues e
    rw [h]
    simp
  have hdetA : A.det.re = ∏ i, e.eigenvalues i := by
    have h := Matrix.IsHermitian.det_eq_prod_eigenvalues e
    rw [h]
    calc
      (∏ i, (e.eigenvalues i : ℂ)).re =
          (↑(∏ i, e.eigenvalues i) : ℂ).re := by
            exact congrArg Complex.re
              (Complex.ofReal_prod (s := Finset.univ) e.eigenvalues).symm
      _ = ∏ i, e.eigenvalues i := Complex.ofReal_re _
  have hlogprod : Real.log (∏ i, e.eigenvalues i) = ∑ i, Real.log (e.eigenvalues i) := by
    apply Real.log_prod
    intro i hi
    exact (ne_of_gt (hA_pos.eigenvalues_pos i))
  have hterms : ∀ i, 0 ≤ e.eigenvalues i - Real.log (e.eigenvalues i) - 1 := by
    intro i
    have hi := Real.log_le_sub_one_of_pos (hA_pos.eigenvalues_pos i)
    linarith
  have hsum : 0 ≤ ∑ i, (e.eigenvalues i - Real.log (e.eigenvalues i) - 1) := by
    exact Finset.sum_nonneg fun i hi => hterms i
  have heq : (∑ i, (e.eigenvalues i - Real.log (e.eigenvalues i) - 1)) =
      (∑ i, e.eigenvalues i) - ∑ i, Real.log (e.eigenvalues i) - (Fintype.card n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [logDetDivergence, htrace, hdet, htraceA, hdetA, hlogprod]
  rw [← heq]
  exact hsum

end D5.S3.Resource.LogDetDivergence

#print axioms D5.S3.Resource.LogDetDivergence.logDetDivergence_nonneg

/- GID: D5/S3/Resource/LogDet/CongruenceGeometry
   generality: G
   mirror-B: D5/B/S3/Resource/LogDet/CongruenceGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove congruence invariance, a three-point law, and log-det asymmetry. -/

import D5.S3.Resource.LogDetDivergence

namespace D5.S3.Resource.LogDet.CongruenceGeometry

open scoped ComplexOrder
open D5.S3.Resource.LogDetDivergence
open Matrix

theorem logDetDivergence_conjugate_congr {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma T : Matrix n n ℂ) (hT : IsUnit T.det) :
    logDetDivergence (T * rho * Tᴴ) (T * sigma * Tᴴ) =
      logDetDivergence rho sigma := by
  fail_if_success ((try simp); done)
  have hT_matrix : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  have hTstar_matrix : IsUnit Tᴴ := (Matrix.isUnit_conjTranspose T).mpr hT_matrix
  have hTstar : IsUnit (Tᴴ).det := (Matrix.isUnit_iff_isUnit_det Tᴴ).mp hTstar_matrix
  have hsim : (T * sigma * Tᴴ)⁻¹ * (T * rho * Tᴴ) =
      Tᴴ⁻¹ * (sigma⁻¹ * rho) * Tᴴ := by
    calc
      (T * sigma * Tᴴ)⁻¹ * (T * rho * Tᴴ) =
          Tᴴ⁻¹ * (T * sigma)⁻¹ * (T * rho * Tᴴ) := by
            rw [Matrix.mul_inv_rev]
      _ = Tᴴ⁻¹ * (sigma⁻¹ * T⁻¹) * (T * rho * Tᴴ) := by
            rw [Matrix.mul_inv_rev]
      _ = Tᴴ⁻¹ * sigma⁻¹ * (T⁻¹ * T) * rho * Tᴴ := by noncomm_ring
      _ = Tᴴ⁻¹ * (sigma⁻¹ * rho) * Tᴴ := by
            rw [Matrix.nonsing_inv_mul T hT]
            simp [Matrix.mul_assoc]
  have htrace : (Tᴴ⁻¹ * (sigma⁻¹ * rho) * Tᴴ).trace = (sigma⁻¹ * rho).trace := by
    calc
      (Tᴴ⁻¹ * (sigma⁻¹ * rho) * Tᴴ).trace =
          (Tᴴ * Tᴴ⁻¹ * (sigma⁻¹ * rho)).trace := Matrix.trace_mul_cycle _ _ _
      _ = (sigma⁻¹ * rho).trace := by rw [Matrix.mul_nonsing_inv Tᴴ hTstar]; simp
  have hdet : (Tᴴ⁻¹ * (sigma⁻¹ * rho) * Tᴴ).det = (sigma⁻¹ * rho).det := by
    have hTstar_det : Tᴴ.det * Tᴴ⁻¹.det = 1 := by
      rw [← Matrix.det_mul, Matrix.mul_nonsing_inv Tᴴ hTstar, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      Tᴴ⁻¹.det * (sigma⁻¹ * rho).det * Tᴴ.det =
          (sigma⁻¹ * rho).det * (Tᴴ.det * Tᴴ⁻¹.det) := by ring
      _ = (sigma⁻¹ * rho).det := by rw [hTstar_det, mul_one]
  unfold logDetDivergence
  rw [hsim, htrace, hdet]

theorem logDetDivergence_three_point {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma tau : Matrix n n ℂ) (hr : rho.PosDef) (hs : sigma.PosDef)
    (ht : tau.PosDef) :
    logDetDivergence rho sigma + logDetDivergence sigma tau -
        logDetDivergence rho tau =
      ((sigma⁻¹ - tau⁻¹) * (rho - sigma)).trace.re := by
  fail_if_success ((try simp); done)
  rw [barrier_bregman_link rho sigma hr hs, barrier_bregman_link sigma tau hs ht,
    barrier_bregman_link rho tau hr ht]
  have hmatrix : (sigma⁻¹ - tau⁻¹) * (rho - sigma) =
      sigma⁻¹ * (rho - sigma) + tau⁻¹ * (sigma - tau) - tau⁻¹ * (rho - tau) := by
    noncomm_ring
  rw [hmatrix, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
  ring

theorem exists_logDetDivergence_ne_swap :
    ∃ rho sigma : Matrix (Fin 1) (Fin 1) ℂ,
      rho.PosDef ∧ sigma.PosDef ∧
        logDetDivergence rho sigma ≠ logDetDivergence sigma rho := by
  fail_if_success ((try simp); done)
  let rho : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal fun _ => 2
  let sigma : Matrix (Fin 1) (Fin 1) ℂ := 1
  have hrho : rho.PosDef := by
    dsimp [rho]
    rw [Matrix.posDef_diagonal_iff]
    intro i
    norm_num
  have hsigma : sigma.PosDef := by
    exact Matrix.PosDef.one
  refine ⟨rho, sigma, hrho, hsigma, ?_⟩
  intro heq
  have heq' : (2 : ℝ) - Real.log 2 = (2 : ℝ)⁻¹ + Real.log 2 := by
    simpa [rho, sigma, logDetDivergence, Matrix.trace_fin_one_of,
      Matrix.det_fin_one_of] using heq
  have hlog : (3 : ℝ) / 2 - 2 * Real.log 2 = 0 := by
    norm_num at heq' ⊢
    linarith
  have hpos : 0 < (3 : ℝ) / 2 - 2 * Real.log 2 := by
    have hhi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  linarith

end D5.S3.Resource.LogDet.CongruenceGeometry

#print axioms D5.S3.Resource.LogDet.CongruenceGeometry.logDetDivergence_conjugate_congr
#print axioms D5.S3.Resource.LogDet.CongruenceGeometry.logDetDivergence_three_point
#print axioms D5.S3.Resource.LogDet.CongruenceGeometry.exists_logDetDivergence_ne_swap

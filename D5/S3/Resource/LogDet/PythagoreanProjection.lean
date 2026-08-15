/- GID: D5/S3/Resource/LogDet/PythagoreanProjection
   generality: G
   mirror-B: D5/B/S3/Resource/LogDet/PythagoreanProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the log-det Pythagorean projection law and its congruence transport. -/

import D5.S3.Resource.LogDet.CongruenceGeometry

namespace D5.S3.Resource.LogDet.PythagoreanProjection

open scoped ComplexOrder
open D5.S3.Resource.LogDetDivergence
open D5.S3.Resource.LogDet.CongruenceGeometry
open Matrix

def IsLogDetProjectionCertificate {n : Type*} [Fintype n] [DecidableEq n]
    (C : Set (Matrix n n ℂ)) (rho sigma : Matrix n n ℂ) : Prop :=
  sigma ∈ C ∧ sigma.PosDef ∧
    ∀ tau ∈ C, tau.PosDef → ((sigma⁻¹ - tau⁻¹) * (rho - sigma)).trace.re ≤ 0

def congruenceImage {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℂ) (C : Set (Matrix n n ℂ)) : Set (Matrix n n ℂ) :=
  (T * · * Tᴴ) '' C

theorem IsLogDetProjectionCertificate.pythagorean {n : Type*} [Fintype n]
    [DecidableEq n] {C : Set (Matrix n n ℂ)} {rho sigma : Matrix n n ℂ}
    (hcert : IsLogDetProjectionCertificate C rho sigma) (hr : rho.PosDef) :
    ∀ tau ∈ C, tau.PosDef →
      logDetDivergence rho sigma + logDetDivergence sigma tau ≤
        logDetDivergence rho tau := by
  fail_if_success ((try simp); done)
  intro tau htau ht
  have hthree := logDetDivergence_three_point rho sigma tau hr hcert.2.1 ht
  have hpair := hcert.2.2 tau htau ht
  linarith

theorem logDetDivergence_pythagorean_eq_iff {n : Type*} [Fintype n]
    [DecidableEq n] (rho sigma tau : Matrix n n ℂ) (hr : rho.PosDef)
    (hs : sigma.PosDef) (ht : tau.PosDef) :
    logDetDivergence rho sigma + logDetDivergence sigma tau =
        logDetDivergence rho tau ↔
      ((sigma⁻¹ - tau⁻¹) * (rho - sigma)).trace.re = 0 := by
  fail_if_success ((try simp); done)
  have hthree := logDetDivergence_three_point rho sigma tau hr hs ht
  constructor <;> intro h <;> linarith

theorem IsLogDetProjectionCertificate.congruence {n : Type*} [Fintype n]
    [DecidableEq n] {C : Set (Matrix n n ℂ)} {rho sigma : Matrix n n ℂ}
    (hcert : IsLogDetProjectionCertificate C rho sigma) (T : Matrix n n ℂ)
    (hT : IsUnit T.det) :
    IsLogDetProjectionCertificate (congruenceImage T C)
      (T * rho * Tᴴ) (T * sigma * Tᴴ) := by
  fail_if_success ((try simp); done)
  have hT_matrix : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  have hTstar_matrix : IsUnit Tᴴ := (Matrix.isUnit_conjTranspose T).mpr hT_matrix
  have hTstar : IsUnit (Tᴴ).det :=
    (Matrix.isUnit_iff_isUnit_det Tᴴ).mp hTstar_matrix
  have hTinv_mul : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hTstar_mul_inv : Tᴴ * Tᴴ⁻¹ = 1 := Matrix.mul_nonsing_inv Tᴴ hTstar
  have hinv : ∀ A : Matrix n n ℂ, (T * A * Tᴴ)⁻¹ = Tᴴ⁻¹ * A⁻¹ * T⁻¹ := by
    intro A
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  refine ⟨⟨sigma, hcert.1, rfl⟩, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using
      (hT_matrix.posDef_star_right_conjugate_iff (x := sigma)).mpr hcert.2.1
  · intro transformed htransformed htransformed_pos
    rcases htransformed with ⟨tau, htau, rfl⟩
    have ht : tau.PosDef := by
      have hiff : (T * tau * Tᴴ).PosDef ↔ tau.PosDef := by
        simpa [Matrix.star_eq_conjTranspose] using
          (hT_matrix.posDef_star_right_conjugate_iff (x := tau))
      exact hiff.mp htransformed_pos
    have hpair_matrix :
        (((T * sigma * Tᴴ)⁻¹ - (T * tau * Tᴴ)⁻¹) *
            ((T * rho * Tᴴ) - (T * sigma * Tᴴ))) =
          Tᴴ⁻¹ * ((sigma⁻¹ - tau⁻¹) * (rho - sigma)) * Tᴴ := by
      rw [hinv sigma, hinv tau]
      calc
        (Tᴴ⁻¹ * sigma⁻¹ * T⁻¹ - Tᴴ⁻¹ * tau⁻¹ * T⁻¹) *
              (T * rho * Tᴴ - T * sigma * Tᴴ) =
            Tᴴ⁻¹ * (sigma⁻¹ - tau⁻¹) * (T⁻¹ * T) *
              (rho - sigma) * Tᴴ := by
                noncomm_ring
        _ = Tᴴ⁻¹ * ((sigma⁻¹ - tau⁻¹) * (rho - sigma)) * Tᴴ := by
              rw [hTinv_mul]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hpair_trace :
        (((T * sigma * Tᴴ)⁻¹ - (T * tau * Tᴴ)⁻¹) *
              ((T * rho * Tᴴ) - (T * sigma * Tᴴ))).trace.re =
          ((sigma⁻¹ - tau⁻¹) * (rho - sigma)).trace.re := by
      rw [hpair_matrix]
      exact congrArg Complex.re <| calc
        (Tᴴ⁻¹ * ((sigma⁻¹ - tau⁻¹) * (rho - sigma)) * Tᴴ).trace =
            (Tᴴ * Tᴴ⁻¹ * ((sigma⁻¹ - tau⁻¹) * (rho - sigma))).trace :=
              Matrix.trace_mul_cycle _ _ _
        _ = ((sigma⁻¹ - tau⁻¹) * (rho - sigma)).trace := by
              rw [hTstar_mul_inv]
              simp
    rw [hpair_trace]
    exact hcert.2.2 tau htau ht

end D5.S3.Resource.LogDet.PythagoreanProjection

#print axioms D5.S3.Resource.LogDet.PythagoreanProjection.IsLogDetProjectionCertificate.pythagorean
#print axioms D5.S3.Resource.LogDet.PythagoreanProjection.logDetDivergence_pythagorean_eq_iff
#print axioms D5.S3.Resource.LogDet.PythagoreanProjection.IsLogDetProjectionCertificate.congruence

/- GID: D5/S3/Observer/BlockStructure/JetPencilFiniteExpansion
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/JetPencilFiniteExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nilpotent jet pencil has finite resolvent and traceless powers. -/

import D5.S3.Analytic.Adelic.JetResolventSemisimplification
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Nilpotent.Basic

/- Library-search audit trail (2026-09-02):
   * D5 searches for nilpotent shifts, jet pencils, finite resolvent series,
     and traces of matrix powers found the exact public definitions
     `nilpotentJetShift` and `jetPencil` in `JetResolventSemisimplification`.
     That module proves a determinant lemma privately and exposes the trace of
     the inverse, but it does not state the matrix inverse series or the traces
     of all positive shift powers. The definitions are imported rather than
     duplicated here.
   * The fixed two-dimensional modules `PowerTraceSimilarityCountermodel`,
     `RamifiedConjugateJet`, and `IdentityJordanGeneratorContrast` do not cover
     the general `Fin m` pencil or its finite inverse expansion.
   * Pinned Mathlib exact hits `Matrix.det_of_isLowerTriangular`,
     `Matrix.charpoly_of_isUpperTriangular`, `Matrix.aeval_self_charpoly`,
     `Matrix.isNilpotent_trace_of_isNilpotent`, `mul_neg_geom_sum`, and
     `Matrix.nonsing_inv_mul` are applied below. No packaged theorem states all
     visible source clauses for this concrete shift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.BlockStructure.JetPencilFiniteExpansion

open Polynomial
open scoped BigOperators Matrix
open D5.S3.Analytic.Adelic.JetResolventSemisimplification

/-- The finite series displayed for the inverse of the jet pencil. Scalar
division is represented by inverse scalar multiplication on matrices. -/
noncomputable def jetResolventSeries (m : Nat) (rho s : Complex) :
    Matrix (Fin m) (Fin m) Complex :=
  ∑ k ∈ Finset.range m,
    ((s - rho) ^ (k + 1))⁻¹ • (nilpotentJetShift m) ^ k

private theorem nilpotentJetShift_transpose_upperTriangular (m : Nat) :
    (nilpotentJetShift m)ᵀ.IsUpperTriangular := by
  intro i j hji
  have hval : j.val < i.val := hji
  have hne : ¬ j.val = i.val + 1 := by omega
  simp [nilpotentJetShift, hne]

private theorem nilpotentJetShift_charpoly (m : Nat) :
    (nilpotentJetShift m).charpoly = X ^ m := by
  rw [← Matrix.charpoly_transpose]
  rw [Matrix.charpoly_of_isUpperTriangular _
    (nilpotentJetShift_transpose_upperTriangular m)]
  simp [nilpotentJetShift]

private theorem nilpotentJetShift_pow_card (m : Nat) :
    (nilpotentJetShift m) ^ m = 0 := by
  have hCayley := Matrix.aeval_self_charpoly (nilpotentJetShift m)
  rw [nilpotentJetShift_charpoly] at hCayley
  simpa using hCayley

/-- The determinant of the lower-triangular jet pencil is the product of its
constant diagonal entries. This clause does not require `s ≠ rho`. -/
theorem jet_pencil_determinant (m : Nat) (rho s : Complex) :
    (jetPencil m rho s).det = (s - rho) ^ m := by
  have hLower : (jetPencil m rho s).IsLowerTriangular := by
    intro i j hji
    have hij : i < j := by simpa using hji
    simp [jetPencil, nilpotentJetShift, Matrix.smul_apply, hij.ne]
    omega
  rw [Matrix.det_of_isLowerTriangular (jetPencil m rho s) hLower]
  simp [jetPencil, nilpotentJetShift, Matrix.smul_apply]

/-- Every positive power of the finite nilpotent shift has trace zero. -/
theorem nilpotent_jet_shift_trace_power (m k : Nat) (hk : 1 ≤ k) :
    Matrix.trace ((nilpotentJetShift m) ^ k) = 0 := by
  have hNilpotent : IsNilpotent (nilpotentJetShift m) :=
    ⟨m, nilpotentJetShift_pow_card m⟩
  have hPowerNilpotent : IsNilpotent ((nilpotentJetShift m) ^ k) :=
    hNilpotent.pow_of_pos (by omega)
  exact isNilpotent_iff_eq_zero.mp
    (Matrix.isNilpotent_trace_of_isNilpotent hPowerNilpotent)

private theorem jetResolventSeries_eq_geom (m : Nat) (rho s : Complex) :
    jetResolventSeries m rho s =
      (s - rho)⁻¹ •
        ∑ k ∈ Finset.range m,
          ((s - rho)⁻¹ • nilpotentJetShift m) ^ k := by
  simp only [jetResolventSeries]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_pow, smul_smul]
  congr 1
  rw [pow_succ, mul_inv_rev, inv_pow]

private theorem jetPencil_factor (m : Nat) (rho s : Complex) (hs : s ≠ rho) :
    jetPencil m rho s =
      (s - rho) •
        (1 - (s - rho)⁻¹ • nilpotentJetShift m) := by
  simp [jetPencil, smul_sub, smul_smul, sub_ne_zero.mpr hs]

/-- Off the spectral point, the nonsingular inverse is the finite geometric
series in powers of the nilpotent shift. -/
theorem jet_pencil_inverse_finite_series (m : Nat) (rho s : Complex)
    (hs : s ≠ rho) :
    (jetPencil m rho s)⁻¹ = jetResolventSeries m rho s := by
  let B : Matrix (Fin m) (Fin m) Complex :=
    (s - rho)⁻¹ • nilpotentJetShift m
  let G : Matrix (Fin m) (Fin m) Complex :=
    ∑ k ∈ Finset.range m, B ^ k
  have hBpow : B ^ m = 0 := by
    dsimp only [B]
    rw [smul_pow, nilpotentJetShift_pow_card, smul_zero]
  have hGeom : (1 - B) * G = 1 := by
    dsimp only [G]
    rw [mul_neg_geom_sum, hBpow, sub_zero]
  have hFactor : jetPencil m rho s = (s - rho) • (1 - B) := by
    simpa only [B] using jetPencil_factor m rho s hs
  have hSeries : jetResolventSeries m rho s = (s - rho)⁻¹ • G := by
    simpa only [B, G] using jetResolventSeries_eq_geom m rho s
  have hRightInverse : jetPencil m rho s * ((s - rho)⁻¹ • G) = 1 := by
    rw [hFactor, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hGeom]
    simp [sub_ne_zero.mpr hs]
  have hUnit : IsUnit (jetPencil m rho s).det := by
    rw [jet_pencil_determinant]
    exact isUnit_iff_ne_zero.mpr
      (pow_ne_zero m (sub_ne_zero.mpr hs))
  calc
    (jetPencil m rho s)⁻¹ = (jetPencil m rho s)⁻¹ * 1 := by simp
    _ = (jetPencil m rho s)⁻¹ *
        (jetPencil m rho s * ((s - rho)⁻¹ • G)) := by rw [hRightInverse]
    _ = ((jetPencil m rho s)⁻¹ * jetPencil m rho s) *
        ((s - rho)⁻¹ • G) := by rw [Matrix.mul_assoc]
    _ = (s - rho)⁻¹ • G := by rw [Matrix.nonsing_inv_mul _ hUnit, one_mul]
    _ = jetResolventSeries m rho s := hSeries.symm

/-- The visible jet-to-mass clauses: the unconditional determinant and
traceless-power identities, and the finite inverse series off the spectral point. -/
theorem jet_pencil_finite_expansion (m : Nat) (rho s : Complex) :
    (jetPencil m rho s).det = (s - rho) ^ m ∧
      (∀ k : Nat, 1 ≤ k →
        Matrix.trace ((nilpotentJetShift m) ^ k) = 0) ∧
      (s ≠ rho →
        (jetPencil m rho s)⁻¹ = jetResolventSeries m rho s) := by
  exact ⟨jet_pencil_determinant m rho s,
    nilpotent_jet_shift_trace_power m,
    jet_pencil_inverse_finite_series m rho s⟩

private theorem positive_numeric_witness :
    jetPencil 2 1 3 = !![(2 : Complex), 0; -1, 2] ∧
      (jetPencil 2 1 3).det = 4 ∧
      Matrix.trace (nilpotentJetShift 2) = 0 ∧
      (jetPencil 2 1 3)⁻¹ =
        !![(1 / 2 : Complex), 0; 1 / 4, 1 / 2] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jetPencil, nilpotentJetShift, Matrix.smul_apply]
  · rw [jet_pencil_determinant]
    norm_num
  · norm_num [Matrix.trace_fin_two, nilpotentJetShift]
  · rw [jet_pencil_inverse_finite_series 2 1 3 (by norm_num)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jetResolventSeries, nilpotentJetShift, Matrix.smul_apply,
        Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem singular_numeric_witness :
    jetPencil 1 0 0 = 0 ∧
      (jetPencil 1 0 0).det = 0 ∧
      ¬(0 : Complex) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [jetPencil, nilpotentJetShift, Matrix.smul_apply]
  · rw [jet_pencil_determinant]
    norm_num
  · simp

private theorem trace_guard_numeric_witness :
    ¬(1 ≤ (0 : Nat)) ∧
      Matrix.trace ((nilpotentJetShift 2) ^ 0) = (2 : Complex) ∧
      Matrix.trace ((nilpotentJetShift 2) ^ 0) ≠ 0 := by
  norm_num [Matrix.trace_fin_two]

#print axioms jet_pencil_finite_expansion

end D5.S3.Observer.BlockStructure.JetPencilFiniteExpansion

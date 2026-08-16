/- GID: D5/S3/Quantum/Sharpness/ExceptionalPointOverlap
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/ExceptionalPointOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two PT eigenbranches have overlap min(delta/kappa, kappa/delta). -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/- Library-search audit trail (2026-08-17):
   * Repository search found only a governance note recording the formula, with no declaration.
   * Pinned-Mathlib searches for exceptional points, non-Hermitian eigenvector overlap, and
     normalized inner products found no exact theorem.
   * The Lean skill smart search returned no declaration for `eigenvector overlap` or
     `normalized inner product`; Loogle was reachable but those conceptual queries were not valid
     type patterns and returned no candidate declaration. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Sharpness.ExceptionalPointOverlap

/-- The two explicit right-eigenvector branches of the PT block `kappa X - i delta Z`.
The real-radical form is used before the exceptional point and the imaginary-radical form after
it. -/
def branchVector (delta kappa : Real) (positive : Bool) : Fin 2 -> Complex :=
  if delta <= kappa then
    ![(kappa : Complex), Complex.I * delta +
      (if positive then (Real.sqrt (kappa ^ 2 - delta ^ 2) : Complex)
       else -(Real.sqrt (kappa ^ 2 - delta ^ 2) : Complex))]
  else
    ![(kappa : Complex), Complex.I *
      (delta + if positive then Real.sqrt (delta ^ 2 - kappa ^ 2)
       else -Real.sqrt (delta ^ 2 - kappa ^ 2))]

/-- The Hermitian inner product on explicit two-component branch vectors. -/
def hermitianInner (v w : Fin 2 -> Complex) : Complex :=
  ∑ i, star (v i) * w i

/-- The squared Euclidean norm of an explicit two-component branch vector. -/
def squaredNorm (v : Fin 2 -> Complex) : Real :=
  ∑ i, Complex.normSq (v i)

/-- Absolute Hermitian overlap divided by the product of the two Euclidean norms. -/
def normalizedBranchOverlap (delta kappa : Real) : Real :=
  norm (hermitianInner (branchVector delta kappa true) (branchVector delta kappa false)) /
    Real.sqrt
      (squaredNorm (branchVector delta kappa true) *
        squaredNorm (branchVector delta kappa false))

/-- Across both PT phases, the normalized eigenbranch overlap is the smaller coupling ratio. -/
theorem exceptional_point_branch_overlap (delta kappa : Real)
    (hdelta : 0 < delta) (hkappa : 0 < kappa) :
    normalizedBranchOverlap delta kappa = min (delta / kappa) (kappa / delta) := by
  by_cases hphase : delta <= kappa
  · let r := Real.sqrt (kappa ^ 2 - delta ^ 2)
    have hradicand : 0 <= kappa ^ 2 - delta ^ 2 := by nlinarith
    have hr_sq : r ^ 2 = kappa ^ 2 - delta ^ 2 := Real.sq_sqrt hradicand
    have hplus :
        branchVector delta kappa true =
          ![(kappa : Complex), Complex.I * delta + (r : Complex)] := by
      simp [branchVector, hphase, r]
    have hminus :
        branchVector delta kappa false =
          ![(kappa : Complex), Complex.I * delta - (r : Complex)] := by
      simp [branchVector, hphase, r]
      ring
    have hinner :
        hermitianInner (branchVector delta kappa true) (branchVector delta kappa false) =
          Complex.mk (2 * delta ^ 2) (2 * r * delta) := by
      rw [hplus, hminus]
      apply Complex.ext <;> simp [hermitianInner, Fin.sum_univ_two] <;>
        nlinarith [hr_sq]
    have hnorm_plus : squaredNorm (branchVector delta kappa true) = 2 * kappa ^ 2 := by
      rw [hplus]
      simp [squaredNorm, Fin.sum_univ_two, Complex.normSq_apply]
      nlinarith [hr_sq]
    have hnorm_minus : squaredNorm (branchVector delta kappa false) = 2 * kappa ^ 2 := by
      rw [hminus]
      simp [squaredNorm, Fin.sum_univ_two, Complex.normSq_apply]
      nlinarith [hr_sq]
    have hinner_norm :
        norm (hermitianInner (branchVector delta kappa true)
          (branchVector delta kappa false)) = 2 * delta * kappa := by
      rw [hinner, Complex.norm_def]
      have hnorm_sq :
          Complex.normSq (Complex.mk (2 * delta ^ 2) (2 * r * delta)) =
            (2 * delta * kappa) ^ 2 := by
        simp [Complex.normSq_apply]
        nlinarith [hr_sq]
      rw [hnorm_sq, Real.sqrt_sq]
      positivity
    have hdenominator :
        Real.sqrt
            (squaredNorm (branchVector delta kappa true) *
              squaredNorm (branchVector delta kappa false)) =
          2 * kappa ^ 2 := by
      rw [hnorm_plus, hnorm_minus]
      rw [show (2 * kappa ^ 2) * (2 * kappa ^ 2) = (2 * kappa ^ 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have hoverlap : normalizedBranchOverlap delta kappa = delta / kappa := by
      rw [normalizedBranchOverlap, hinner_norm, hdenominator]
      field_simp
    have hratio : delta / kappa <= kappa / delta := by
      apply (div_le_div_iff₀ hkappa hdelta).2
      nlinarith
    rw [hoverlap, min_eq_left hratio]
  · have hlt : kappa < delta := lt_of_not_ge hphase
    let mu := Real.sqrt (delta ^ 2 - kappa ^ 2)
    have hradicand : 0 <= delta ^ 2 - kappa ^ 2 := by nlinarith
    have hmu_sq : mu ^ 2 = delta ^ 2 - kappa ^ 2 := Real.sq_sqrt hradicand
    have hplus :
        branchVector delta kappa true =
          ![(kappa : Complex), Complex.I * (delta + mu)] := by
      simp [branchVector, hphase, mu]
    have hminus :
        branchVector delta kappa false =
          ![(kappa : Complex), Complex.I * (delta - mu)] := by
      simp [branchVector, hphase, mu]
      ring
    have hinner :
        hermitianInner (branchVector delta kappa true) (branchVector delta kappa false) =
          Complex.mk (2 * kappa ^ 2) 0 := by
      rw [hplus, hminus]
      apply Complex.ext
      · simp [hermitianInner, Fin.sum_univ_two]
        nlinarith [hmu_sq]
      · simp [hermitianInner, Fin.sum_univ_two]
    have hnorm_plus :
        squaredNorm (branchVector delta kappa true) = 2 * delta * (delta + mu) := by
      rw [hplus]
      simp [squaredNorm, Fin.sum_univ_two, Complex.normSq_apply]
      nlinarith [hmu_sq]
    have hnorm_minus :
        squaredNorm (branchVector delta kappa false) = 2 * delta * (delta - mu) := by
      rw [hminus]
      simp [squaredNorm, Fin.sum_univ_two, Complex.normSq_apply]
      nlinarith [hmu_sq]
    have hinner_norm :
        norm (hermitianInner (branchVector delta kappa true)
          (branchVector delta kappa false)) = 2 * kappa ^ 2 := by
      rw [hinner, Complex.norm_def]
      have hnorm_sq :
          Complex.normSq (Complex.mk (2 * kappa ^ 2) 0) = (2 * kappa ^ 2) ^ 2 := by
        simp [Complex.normSq_apply]
        ring
      rw [hnorm_sq, Real.sqrt_sq]
      positivity
    have hdenominator :
        Real.sqrt
            (squaredNorm (branchVector delta kappa true) *
              squaredNorm (branchVector delta kappa false)) =
          2 * delta * kappa := by
      rw [hnorm_plus, hnorm_minus]
      have hproduct :
          (2 * delta * (delta + mu)) * (2 * delta * (delta - mu)) =
            (2 * delta * kappa) ^ 2 := by
        nlinarith [hmu_sq]
      rw [hproduct, Real.sqrt_sq]
      positivity
    have hoverlap : normalizedBranchOverlap delta kappa = kappa / delta := by
      rw [normalizedBranchOverlap, hinner_norm, hdenominator]
      field_simp
    have hratio : kappa / delta <= delta / kappa := by
      apply (div_le_div_iff₀ hdelta hkappa).2
      nlinarith
    rw [hoverlap, min_eq_right hratio]

#print axioms exceptional_point_branch_overlap

end D5.S3.Quantum.Sharpness.ExceptionalPointOverlap

/- GID: D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite diagonal spectra admit fermionic and truncated bosonic occupation expansions. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/- Library-search audit trail (2026-09-02):
   * Six repository routes found no existing Bosonic/Fermionic determinant or occupation theorem.
   * Exact atom, receipt, digest, generalized-body, and in-flight branch searches were negative.
   * Pinned Mathlib supplies `Matrix.det_diagonal`, `Fintype.prod_sum`,
     `Fin.sum_univ_eq_sum_range`, and `geom_sum_mul_neg`; they are applied directly below.
   * The source's infinite determinant and series require operator and convergence hypotheses that
     it does not state. This module gives the exact finite-spectrum and finite-cutoff form. -/

namespace D5.S3.Quantum.FockSpace.FiniteOccupationPartitionFunctions

open scoped BigOperators

/-- The finite spectral operator with eigenvalue list `e`. -/
def diagonalSpectrum {K : Type*} [Zero K] {d : Nat} (e : Fin d → K) :
    Matrix (Fin d) (Fin d) K :=
  Matrix.diagonal e

/-- Fermionic occupations have values in `Fin 2`, so every mode is used at most once. -/
def fermionicPartition {K : Type*} [CommSemiring K] {d : Nat}
    (x : K) (e : Fin d → K) : K :=
  ∑ occupation : Fin d → Fin 2, ∏ i, (x * e i) ^ (occupation i).val

/-- The bosonic partition function truncated to occupations at most `N`. -/
def bosonicPartitionTrunc {K : Type*} [CommSemiring K] {d : Nat}
    (N : Nat) (x : K) (e : Fin d → K) : K :=
  ∑ occupation : Fin d → Fin (N + 1), ∏ i, (x * e i) ^ (occupation i).val

/-- On a finite diagonal spectrum, the fermionic determinant is exactly the sum over binary
occupations. -/
theorem fermionic_determinant_eq_occupation_sum {K : Type*} [CommRing K] {d : Nat}
    (x : K) (e : Fin d → K) :
    Matrix.det (1 + x • diagonalSpectrum e) = fermionicPartition x e := by
  have hdiagonal :
      (1 + x • diagonalSpectrum e : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => 1 + x * e i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalSpectrum]
    · simp [diagonalSpectrum, hij]
  rw [hdiagonal, Matrix.det_diagonal]
  unfold fermionicPartition
  rw [← Fintype.prod_sum (fun i (occupation : Fin 2) =>
    (x * e i) ^ occupation.val)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fin.sum_univ_two]

/-- A finite product of geometric sums is exactly the sum over bounded bosonic occupations. -/
theorem bosonic_trunc_eq_product_geometric_sums {K : Type*} [CommSemiring K] {d : Nat}
    (N : Nat) (x : K) (e : Fin d → K) :
    bosonicPartitionTrunc N x e =
      ∏ i, ∑ occupation : Fin (N + 1), (x * e i) ^ occupation.val := by
  unfold bosonicPartitionTrunc
  exact (Fintype.prod_sum fun i (occupation : Fin (N + 1)) =>
    (x * e i) ^ occupation.val).symm

/-- Multiplying the bosonic cutoff by the finite denominator leaves the exact geometric
remainder. This identity has no convergence or division side condition. -/
theorem bosonic_trunc_mul_determinant {K : Type*} [CommRing K] {d : Nat}
    (N : Nat) (x : K) (e : Fin d → K) :
    bosonicPartitionTrunc N x e * Matrix.det (1 - x • diagonalSpectrum e) =
      ∏ i, (1 - (x * e i) ^ (N + 1)) := by
  have hdiagonal :
      (1 - x • diagonalSpectrum e : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => 1 - x * e i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalSpectrum]
    · simp [diagonalSpectrum, hij]
  rw [bosonic_trunc_eq_product_geometric_sums, hdiagonal, Matrix.det_diagonal,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.sum_univ_eq_sum_range]
  exact geom_sum_mul_neg (x * e i) (N + 1)

/-- When every spectral denominator is nonzero, the cutoff is the inverse determinant times the
exact finite remainder. The hypothesis explicitly excludes Lean's totalized division at zero. -/
theorem bosonic_trunc_eq_inverse_determinant_mul_remainder {K : Type*} [Field K]
    {d : Nat} (N : Nat) (x : K) (e : Fin d → K)
    (hdenominator : ∀ i, 1 - x * e i ≠ 0) :
    bosonicPartitionTrunc N x e =
      (∏ i, (1 - (x * e i) ^ (N + 1))) / Matrix.det (1 - x • diagonalSpectrum e) := by
  have hdiagonal :
      (1 - x • diagonalSpectrum e : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => 1 - x * e i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalSpectrum]
    · simp [diagonalSpectrum, hij]
  have hdet : Matrix.det (1 - x • diagonalSpectrum e) ≠ 0 := by
    rw [hdiagonal, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdenominator i
  exact (eq_div_iff hdet).2 (bosonic_trunc_mul_determinant N x e)

/-- At one mode with `x = e = 1`, binary occupation gives `2`, while occupation through `2`
gives `3`. This concrete witness separates the two state rules. -/
theorem one_mode_fermionic_bosonic_witness :
    fermionicPartition (d := 1) (1 : Nat) (fun _ => 1) = 2 ∧
      bosonicPartitionTrunc (d := 1) 2 (1 : Nat) (fun _ => 1) = 3 := by
  constructor
  · unfold fermionicPartition
    rw [← Fintype.prod_sum (fun i (occupation : Fin 2) =>
      ((1 : Nat) * (fun _ : Fin 1 => 1) i) ^ occupation.val)]
    norm_num [Fin.sum_univ_one, Fin.sum_univ_two]
  · unfold bosonicPartitionTrunc
    rw [← Fintype.prod_sum (fun i (occupation : Fin 3) =>
      ((1 : Nat) * (fun _ : Fin 1 => 1) i) ^ occupation.val)]
    norm_num [Fin.sum_univ_one, Fin.sum_univ_three]

#print axioms fermionic_determinant_eq_occupation_sum
#print axioms bosonic_trunc_eq_product_geometric_sums
#print axioms bosonic_trunc_mul_determinant
#print axioms bosonic_trunc_eq_inverse_determinant_mul_remainder
#print axioms one_mode_fermionic_bosonic_witness

end D5.S3.Quantum.FockSpace.FiniteOccupationPartitionFunctions

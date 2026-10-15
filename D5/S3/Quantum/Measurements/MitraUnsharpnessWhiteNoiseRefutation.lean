/- GID: D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.claim; result=D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.result; claim=D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.claim
   digest: A four-outcome diagonal qubit POVM refutes Mitra's white-noise conjecture. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation

noncomputable section

def opNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) M‖

def IsPOVM {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ i, (A i).PosSemidef) ∧
  (∑ i, A i) = 1

def X {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, opNorm (A i) • A i

def xMin
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian) : ℝ :=
  min (hM.eigenvalues 0) (hM.eigenvalues 1)

private theorem X_isHermitian {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsPOVM A) :
    (X A).IsHermitian := by
  change
    (∑ i : Fin n, opNorm (A i) • A i)ᴴ =
      ∑ i : Fin n, opNorm (A i) • A i
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact
    ((hA.1 i).isHermitian.smul
      (IsSelfAdjoint.all (opNorm (A i)))).eq

def sigma1 {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsPOVM A) : ℝ :=
  xMin (X A) (X_isHermitian A hA) - 1 / (n : ℝ)

def sigma2 {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsPOVM A) : ℝ :=
  (∑ i, opNorm (A i)) / (n : ℝ) -
    xMin (X A) (X_isHermitian A hA)

def sigma1Prime {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (X A)).re / 2 - 1 / (n : ℝ)

def sigma2Prime {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (∑ i, opNorm (A i)) / (n : ℝ) -
    (Matrix.trace (X A)).re / 2

def E {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  opNorm (1 - X A)

def EPrime {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace
    (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (1 - X A))).re

def noisy {n : ℕ}
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (l : ℝ) : Fin n → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i =>
    l • A i + ((1 - l) / (n : ℝ)) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)

def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (hA : IsPOVM A),
      sigma2 A hA ≤ sigma1 A hA ∧
      sigma2Prime A ≤ sigma1Prime A ∧
      (∀ l : ℝ, l ∈ Set.Icc 0 1 →
        E A ≤ E (noisy A l)) ∧
      (∀ l : ℝ, l ∈ Set.Icc 0 1 →
        EPrime A ≤ EPrime (noisy A l))

def diag2 (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(u : ℂ), (v : ℂ)]

def witness : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![diag2 (12 / 40) (1 / 40),
    diag2 (13 / 40) (1 / 40),
    diag2 (14 / 40) (1 / 40),
    diag2 (1 / 40) (37 / 40)]

private theorem opNorm_diag2
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    opNorm (diag2 u v) = max u v := by
  rw [opNorm, diag2, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (show 0 ≤ max u v by positivity)).mpr
    intro i
    fin_cases i
    · simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    · simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  · rcases le_total u v with huv | hvu
    · rw [max_eq_right huv]
      have h := norm_le_pi_norm (![ (u : ℂ), (v : ℂ)] : Fin 2 → ℂ) (1 : Fin 2)
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv] using h
    · rw [max_eq_left hvu]
      have h := norm_le_pi_norm (![ (u : ℂ), (v : ℂ)] : Fin 2 → ℂ) (0 : Fin 2)
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] using h

private theorem xMin_eq_of_eq_diag2
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian)
    (u v : ℝ)
    (hD : M = diag2 u v) :
    xMin M hM = min u v := by
  unfold xMin
  let a : ℝ := hM.eigenvalues 0
  let b : ℝ := hM.eigenvalues 1
  have hsC : Matrix.trace M = ∑ i, (hM.eigenvalues i : ℂ) :=
    hM.trace_eq_sum_eigenvalues
  have hsR : a + b = u + v := by
    have htr : Matrix.trace M = (u + v : ℂ) := by
      rw [hD, diag2]
      simp [Matrix.trace_diagonal]
    have h := congrArg Complex.re hsC
    rw [htr] at h
    simpa [a, b, Fin.sum_univ_succ] using h.symm
  have hpC : Matrix.det M = ∏ i, (hM.eigenvalues i : ℂ) :=
    hM.det_eq_prod_eigenvalues
  have hpR : a * b = u * v := by
    have hdet : Matrix.det M = (u * v : ℂ) := by
      rw [hD, diag2]
      simp [Matrix.det_diagonal, Fin.prod_univ_succ]
    have h := congrArg Complex.re hpC
    rw [hdet] at h
    simpa [a, b, Fin.prod_univ_succ] using h.symm
  have hroot : (a - u) * (a - v) = 0 := by
    linear_combination a * hsR - hpR
  rcases mul_eq_zero.mp hroot with hau | hav
  · have hau' : a = u := sub_eq_zero.mp hau
    have hbv : b = v := by linarith [hsR]
    simp [a, b, hau', hbv]
  · have hav' : a = v := sub_eq_zero.mp hav
    have hbu : b = u := by linarith [hsR]
    simp [a, b, hav', hbu, min_comm]

end

end D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation

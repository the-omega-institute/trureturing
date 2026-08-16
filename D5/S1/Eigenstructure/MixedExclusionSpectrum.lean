/- GID: D5/S1/Eigenstructure/MixedExclusionSpectrum
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/MixedExclusionSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Colored nearest-neighbor exclusion has a quadratic law and a fermionic trace term. -/

import D5.S1.Recurrence.TraceMap

/- Provenance: the weighted no-adjacent-position recurrence is
   `D5.S1.Recurrence.TraceMap.wordSum_succ_succ`.  A pinned-mathlib search found no
   theorem packaging the two-color transfer spectrum and trace identity; the proof uses
   `spectrum.units_conjugate`, `Matrix.spectrum_diagonal`, and `Matrix.trace_units_conj`. -/

namespace D5.S1.Eigenstructure.MixedExclusionSpectrum

open D5.S1.Recurrence.TraceMap
open Polynomial

/-- The two-state transfer matrix for `m` colors subject to nearest-neighbor exclusion. -/
def mixedTransfer (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, m; 1, 0]

/-- The three-state transfer matrix that distinguishes the two occupied colors. -/
def twoColorTransfer : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 1; 1, 0, 0; 1, 0, 0]

private def twoColorEigenvalues : Fin 3 → ℚ :=
  ![2, -1, 0]

private def twoColorEigenbasis : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2, -1, 0; 1, 1, 1; 1, 1, -1]

private def twoColorEigenbasisInv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / 3, 1 / 6, 1 / 6; -1 / 3, 1 / 3, 1 / 3; 0, 1 / 2, -1 / 2]

private def twoColorEigenbasisUnit : (Matrix (Fin 3) (Fin 3) ℚ)ˣ where
  val := twoColorEigenbasis
  inv := twoColorEigenbasisInv
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoColorEigenbasis, twoColorEigenbasisInv, Matrix.mul_apply,
        Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoColorEigenbasis, twoColorEigenbasisInv, Matrix.mul_apply,
        Fin.sum_univ_succ]

private theorem twoColorTransfer_eq_conjugate :
    twoColorTransfer =
      (twoColorEigenbasisUnit : Matrix (Fin 3) (Fin 3) ℚ) *
        Matrix.diagonal twoColorEigenvalues *
          (↑twoColorEigenbasisUnit⁻¹ : Matrix (Fin 3) (Fin 3) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoColorTransfer, twoColorEigenbasisUnit, twoColorEigenbasis,
      twoColorEigenbasisInv, twoColorEigenvalues, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.diagonal_apply, Fin.sum_univ_succ]

private theorem mixedTransfer_charpoly (m : ℤ) :
    Matrix.charpoly (mixedTransfer m) = X ^ 2 - X - C m := by
  rw [Matrix.charpoly_fin_two]
  simp [mixedTransfer, Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

private theorem twoColorTransfer_spectrum :
    spectrum ℚ twoColorTransfer = Set.range twoColorEigenvalues := by
  rw [twoColorTransfer_eq_conjugate, spectrum.units_conjugate, spectrum_diagonal]

private theorem twoColorTransfer_trace_pow (n : ℕ) :
    Matrix.trace (twoColorTransfer ^ n) = 2 ^ n + (-1) ^ n + 0 ^ n := by
  rw [twoColorTransfer_eq_conjugate, Units.conj_pow,
    Matrix.trace_units_conj, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [twoColorEigenvalues, Fin.sum_univ_succ]
  ring

/-- Colored nearest-neighbor exclusion has characteristic equation `lambda^2 = lambda + m`.
For two colors, distinguishing the colors adds a zero eigenvalue while the nonzero spectrum is
`{2, -1}`, so every positive-period trace differs from the free binary count by `(-1)^n`. -/
theorem mixed_exclusion_recurrence_and_two_color_spectrum
    (m K n : ℕ) (hn : 0 < n) :
    wordSum (fun _ => (m : ℝ)) (K + 2) =
        wordSum (fun _ => (m : ℝ)) (K + 1) +
          (m : ℝ) * wordSum (fun _ => (m : ℝ)) K ∧
      Matrix.charpoly (mixedTransfer (m : ℤ)) = X ^ 2 - X - C (m : ℤ) ∧
      spectrum ℚ twoColorTransfer = Set.range ![(2 : ℚ), -1, 0] ∧
      Matrix.trace (twoColorTransfer ^ n) - 2 ^ n = (-1) ^ n := by
  refine ⟨wordSum_succ_succ (fun _ => (m : ℝ)) K, mixedTransfer_charpoly (m : ℤ), ?_, ?_⟩
  · simpa [twoColorEigenvalues] using twoColorTransfer_spectrum
  · rw [twoColorTransfer_trace_pow]
    simp [Nat.ne_of_gt hn]

#print axioms mixed_exclusion_recurrence_and_two_color_spectrum

end D5.S1.Eigenstructure.MixedExclusionSpectrum

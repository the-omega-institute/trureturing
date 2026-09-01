/- GID: D5/S3/Observer/GoldenCoding/GoldenFusionModularTime
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenFusionModularTime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Squared Fibonacci fusion has reciprocal golden spectrum and reflected logarithmic time. -/

import D5.S1.Scale.FibonacciEigen
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Current-tree name and body-shape searches found the conjugate Fibonacci
     convention, its characteristic data, its Lorentz form, and golden scale
     logarithms, but no theorem combining the source matrix, positive square,
     reciprocal eigenbasis, and both reflection identities.
   * `D5.S1.Scale.FibonacciEigen` supplies the canonical golden-ratio facts used
     below; the source convention is transposed across the antidiagonal and is
     therefore stated explicitly.
   * Pinned Mathlib supplies `Matrix.PosDef`, nonsingular matrix inversion,
     `Real.log_inv`, and `Real.log_pow`. Its Hermitian functional calculus was
     inspected, but the source puts the logarithm identities in the eigenbasis,
     where the faithful logarithm is the explicit diagonal spectral logarithm. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.GoldenCoding.GoldenFusionModularTime

/-- The Fibonacci fusion convention used by the source. -/
def fusionMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 1]

/-- Two fusion steps, before its entries are simplified. -/
def fusionSquare : Matrix (Fin 2) (Fin 2) ℝ :=
  fusionMatrix ^ 2

/-- The reciprocal two-point spectrum with expanding scale `r`. -/
noncomputable def reciprocalSpectrum (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r, 0; 0, r⁻¹]

/-- The diagonal spectral logarithm of the reciprocal spectrum. -/
noncomputable def reciprocalSpectralLog (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.log r, 0; 0, Real.log r⁻¹]

/-- Logarithmic time written in its antisymmetric diagonal form. -/
noncomputable def modularGenerator (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.log r, 0; 0, -Real.log r]

/-- The eigenline exchange. -/
def eigenlineSwap : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- A positive reciprocal spectrum is inverted by exchanging its eigenlines,
and its nonzero spectral logarithm changes sign under the same exchange. -/
theorem reciprocal_diagonal_modular_time (r : ℝ) (hr : 1 < r) :
    (reciprocalSpectrum r).PosDef ∧
      modularGenerator r = reciprocalSpectralLog r ∧
      eigenlineSwap * reciprocalSpectrum r * eigenlineSwap =
        (reciprocalSpectrum r)⁻¹ ∧
      eigenlineSwap * modularGenerator r * eigenlineSwap =
        -modularGenerator r ∧
      modularGenerator r ≠ 0 := by
  have hrPos : 0 < r := lt_trans (by norm_num) hr
  have hrNe : r ≠ 0 := hrPos.ne'
  have hSpectrumPos : (reciprocalSpectrum r).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [reciprocalSpectrum]
    · intro x hx
      simp [reciprocalSpectrum, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
        Pi.star_apply]
      by_cases hxZero : x 0 = 0
      · have hxOne : x 1 ≠ 0 := by
          intro hxOne
          apply hx
          funext i
          fin_cases i
          · exact hxZero
          · exact hxOne
        rw [hxZero]
        norm_num
        nlinarith [mul_pos (inv_pos.mpr hrPos) (sq_pos_of_ne_zero hxOne)]
      · nlinarith [mul_pos hrPos (sq_pos_of_ne_zero hxZero),
          mul_nonneg (inv_pos.mpr hrPos).le (sq_nonneg (x 1))]
  have hLog : modularGenerator r = reciprocalSpectralLog r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [modularGenerator, reciprocalSpectralLog, Real.log_inv]
  have hInverse :
      (reciprocalSpectrum r)⁻¹ = !![r⁻¹, 0; 0, r] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reciprocalSpectrum, Matrix.mul_apply, Fin.sum_univ_two, hrNe]
  have hSpectrumReflection :
      eigenlineSwap * reciprocalSpectrum r * eigenlineSwap =
        (reciprocalSpectrum r)⁻¹ := by
    rw [hInverse]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eigenlineSwap, reciprocalSpectrum, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hGeneratorReflection :
      eigenlineSwap * modularGenerator r * eigenlineSwap =
        -modularGenerator r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eigenlineSwap, modularGenerator, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hGeneratorNonzero : modularGenerator r ≠ 0 := by
    intro hZero
    have hEntry := congr_fun (congr_fun hZero (0 : Fin 2)) (0 : Fin 2)
    change Real.log r = 0 at hEntry
    exact (Real.log_pos hr).ne' hEntry
  exact ⟨hSpectrumPos, hLog, hSpectrumReflection,
    hGeneratorReflection, hGeneratorNonzero⟩

/-- The source Fibonacci fusion matrix has determinant `-1`; its square is the
positive-definite determinant-one matrix `[[1,1],[1,2]]` with eigenvalues
`phi^2` and `phi^-2`. In that eigenbasis, the spectral logarithm is nonzero and
the eigenline exchange sends both the squared evolution and its logarithm to
their inverse and negative, respectively. -/
theorem golden_fusion_modular_time :
    Matrix.det fusionMatrix = -1 ∧
      fusionSquare = !![1, 1; 1, 2] ∧
      Matrix.det fusionSquare = 1 ∧
      fusionSquare.PosDef ∧
      fusionSquare *ᵥ ![1, Real.goldenRatio] =
        Real.goldenRatio ^ 2 • ![1, Real.goldenRatio] ∧
      fusionSquare *ᵥ ![Real.goldenRatio, -1] =
        (Real.goldenRatio ^ 2)⁻¹ • ![Real.goldenRatio, -1] ∧
      (reciprocalSpectrum (Real.goldenRatio ^ 2)).PosDef ∧
      modularGenerator (Real.goldenRatio ^ 2) =
        reciprocalSpectralLog (Real.goldenRatio ^ 2) ∧
      eigenlineSwap * reciprocalSpectrum (Real.goldenRatio ^ 2) *
          eigenlineSwap =
        (reciprocalSpectrum (Real.goldenRatio ^ 2))⁻¹ ∧
      eigenlineSwap * modularGenerator (Real.goldenRatio ^ 2) *
          eigenlineSwap =
        -modularGenerator (Real.goldenRatio ^ 2) ∧
      modularGenerator (Real.goldenRatio ^ 2) ≠ 0 := by
  have hSquare : fusionSquare = !![1, 1; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fusionSquare, fusionMatrix, pow_two, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hSquarePos : fusionSquare.PosDef := by
    rw [hSquare, Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    · intro x hx
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply]
      by_cases hxOne : x 1 = 0
      · have hxZero : x 0 ≠ 0 := by
          intro hxZero
          apply hx
          funext i
          fin_cases i
          · exact hxZero
          · exact hxOne
        rw [hxOne]
        norm_num
        exact hxZero
      · nlinarith [sq_nonneg (x 0 + x 1), sq_pos_of_ne_zero hxOne]
  have hPhiInvSq :
      (Real.goldenRatio ^ 2)⁻¹ = 2 - Real.goldenRatio := by
    have hPhiInv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    rw [← inv_pow, hPhiInv]
    nlinarith [Real.goldenRatio_sq]
  have hExpanding :
      fusionSquare *ᵥ ![1, Real.goldenRatio] =
        Real.goldenRatio ^ 2 • ![1, Real.goldenRatio] := by
    rw [hSquare]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      nlinarith [Real.goldenRatio_sq]
  have hContracting :
      fusionSquare *ᵥ ![Real.goldenRatio, -1] =
        (Real.goldenRatio ^ 2)⁻¹ • ![Real.goldenRatio, -1] := by
    rw [hSquare, hPhiInvSq]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      nlinarith [Real.goldenRatio_sq]
  have hScale : 1 < Real.goldenRatio ^ 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hModular := reciprocal_diagonal_modular_time
    (Real.goldenRatio ^ 2) hScale
  refine ⟨by norm_num [fusionMatrix, Matrix.det_fin_two], hSquare,
    ?_, hSquarePos, hExpanding, hContracting, hModular⟩
  rw [hSquare]
  norm_num [Matrix.det_fin_two]

-- A concrete positive scale makes every displayed spectral value nondegenerate.
example :
    (1 : ℝ) < 2 ∧
      reciprocalSpectrum 2 = !![2, 0; 0, 1 / 2] ∧
      eigenlineSwap * reciprocalSpectrum 2 * eigenlineSwap =
        !![1 / 2, 0; 0, 2] ∧
      modularGenerator 2 ≠ 0 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [reciprocalSpectrum]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [eigenlineSwap, reciprocalSpectrum, Matrix.mul_apply,
        Fin.sum_univ_two]
  · intro hZero
    have hEntry := congr_fun (congr_fun hZero (0 : Fin 2)) (0 : Fin 2)
    change Real.log 2 = 0 at hEntry
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

-- At scale one the strict premise fails and the claimed nonzero time split collapses exactly.
example :
    ¬ (1 : ℝ) < 1 ∧
      reciprocalSpectrum 1 = 1 ∧
      modularGenerator 1 = 0 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [reciprocalSpectrum]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [modularGenerator]

#print axioms reciprocal_diagonal_modular_time
#print axioms golden_fusion_modular_time

end D5.S3.Observer.GoldenCoding.GoldenFusionModularTime

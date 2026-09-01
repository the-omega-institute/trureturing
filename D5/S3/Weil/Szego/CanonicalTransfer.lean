/- GID: D5/S3/Weil/Szego/CanonicalTransfer
   generality: G
   mirror-B: D5/B/S3/Weil/Szego/CanonicalTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized Szego transfer matrix has determinant one and preserves J. -/

import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom is residual-open with empty `coverage_gids`, has no formalization
     receipt, and its neighboring parts 967 and 969 are likewise unbound.
   * D5 searches for Szego, Verblunsky, OPUC, CMV, SU11, J-unitary matrices,
     and transfer matrices found no matching complex transfer. The nearest
     modules concern a different real Chebyshev matrix and offline-zero monodromy.
   * Pinned Mathlib and all installed third-party packages have no Szego or
     SU(1,1) declaration. Mathlib supplies `Matrix.det_fin_two`,
     `Matrix.det_smul`, `Circle.coe_inv_eq_conj`, complex norm-square lemmas,
     and explicit conjugate-transpose multiplication, which are used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Szego.CanonicalTransfer

open Complex
open scoped ComplexConjugate

/-- The positive normalization attached to a Verblunsky coefficient. -/
def szegoRho (alpha : ℂ) : ℝ :=
  Real.sqrt (1 - Complex.normSq alpha)

/-- The unnormalized-phase Szego transfer matrix. -/
def szegoTransfer (alpha z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((szegoRho alpha : ℂ)⁻¹) •
    !![z, -conj alpha; -alpha * z, 1]

/-- The signature matrix defining the Hermitian form of type `(1, 1)`. -/
def signatureMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The determinant-one and `J`-unitary defining identities for `SU(1,1)`. -/
def IsSpecialUnitary11 (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Matrix.det A = 1 ∧
    Matrix.conjTranspose A * signatureMatrix * A = signatureMatrix

/-- The determinant-one normalization, parametrized by the chosen unit-circle
square root `w`. On the circle, `conj w = w⁻¹`, so this is formula (968.3). -/
def normalizedSzegoTransfer (alpha : ℂ) (w : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((szegoRho alpha : ℂ)⁻¹) •
    !![(w : ℂ), -conj alpha * conj (w : ℂ);
       -alpha * (w : ℂ), conj (w : ℂ)]

private theorem normSq_lt_one_of_norm_lt_one {alpha : ℂ} (hAlpha : ‖alpha‖ < 1) :
    Complex.normSq alpha < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg alpha]

/-- The Verblunsky disk condition makes the real normalization strictly positive. -/
theorem szego_rho_pos {alpha : ℂ} (hAlpha : ‖alpha‖ < 1) :
    0 < szegoRho alpha := by
  exact Real.sqrt_pos.2 (sub_pos.mpr (normSq_lt_one_of_norm_lt_one hAlpha))

private theorem szego_rho_sq {alpha : ℂ} (hAlpha : ‖alpha‖ < 1) :
    szegoRho alpha ^ 2 = 1 - Complex.normSq alpha := by
  exact Real.sq_sqrt (sub_nonneg.mpr (normSq_lt_one_of_norm_lt_one hAlpha).le)

private theorem szego_numerator_det (alpha z : ℂ) :
    Matrix.det !![z, -conj alpha; -alpha * z, 1] =
      ((1 - Complex.normSq alpha : ℝ) : ℂ) * z := by
  rw [Matrix.det_fin_two]
  change z * 1 - (-conj alpha) * (-alpha * z) =
    ((1 - Complex.normSq alpha : ℝ) : ℂ) * z
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- Formula (968.2) has determinant equal to its spectral phase. -/
theorem szego_transfer_det {alpha : ℂ} (hAlpha : ‖alpha‖ < 1) (z : ℂ) :
    Matrix.det (szegoTransfer alpha z) = z := by
  have hRhoNe : (szegoRho alpha : ℂ) ≠ 0 := by
    exact_mod_cast (szego_rho_pos hAlpha).ne'
  have hRhoSq :
      (szegoRho alpha : ℂ) ^ 2 = ((1 - Complex.normSq alpha : ℝ) : ℂ) := by
    exact_mod_cast szego_rho_sq hAlpha
  rw [szegoTransfer, Matrix.det_smul, Fintype.card_fin, szego_numerator_det, ← hRhoSq]
  field_simp

private theorem special_unitary_11_of_standard_entries (a b : ℂ)
    (hNorm : a * conj a - b * conj b = 1) :
    IsSpecialUnitary11 !![a, b; conj b, conj a] := by
  have hNorm' : conj a * a - b * conj b = 1 := by
    calc
      conj a * a - b * conj b = a * conj a - b * conj b := by ring
      _ = 1 := hNorm
  have hNormNeg : conj b * b - a * conj a = -1 := by
    calc
      conj b * b - a * conj a = -(a * conj a - b * conj b) := by ring
      _ = -1 := by rw [hNorm]
  constructor
  · simpa [Matrix.det_fin_two] using hNorm
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signatureMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two] <;>
      first | assumption | ring

/-- Formula (968.3) is determinant one and preserves the signature `(1, -1)`. -/
theorem normalized_szego_transfer_mem_su11 {alpha : ℂ} (hAlpha : ‖alpha‖ < 1)
    (w : Circle) :
    IsSpecialUnitary11 (normalizedSzegoTransfer alpha w) := by
  let r : ℂ := (szegoRho alpha : ℂ)⁻¹
  let a : ℂ := r * (w : ℂ)
  let b : ℂ := -r * conj alpha * conj (w : ℂ)
  have hRhoNe : szegoRho alpha ≠ 0 := (szego_rho_pos hAlpha).ne'
  have hNormEntries : Complex.normSq a - Complex.normSq b = 1 := by
    dsimp [a, b, r]
    simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_conj,
      Complex.normSq_inv, Complex.normSq_ofReal, Circle.normSq_coe]
    have hRhoMul :
        szegoRho alpha * szegoRho alpha = 1 - Complex.normSq alpha := by
      simpa [pow_two] using szego_rho_sq hAlpha
    have hDen : 1 - Complex.normSq alpha ≠ 0 := by
      rw [← hRhoMul]
      exact mul_ne_zero hRhoNe hRhoNe
    rw [hRhoMul]
    field_simp [hDen]
  have hEntries : a * conj a - b * conj b = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj]
    exact_mod_cast hNormEntries
  have hMatrix :
      normalizedSzegoTransfer alpha w =
        !![a, b; conj b, conj a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [normalizedSzegoTransfer, a, b, r] <;> ring
  rw [hMatrix]
  exact special_unitary_11_of_standard_entries a b hEntries

/-- The source's determinant and `SU(1,1)` claims, with `w² = z` recording the
chosen local square root on the unit circle. -/
theorem canonical_szego_su11_transfer
    {alpha : ℂ} (hAlpha : ‖alpha‖ < 1) (z : ℂ) (w : Circle)
    (_hw : (w : ℂ) ^ 2 = z) :
    0 < szegoRho alpha ∧
      Matrix.det (szegoTransfer alpha z) = z ∧
      IsSpecialUnitary11 (normalizedSzegoTransfer alpha w) := by
  exact ⟨szego_rho_pos hAlpha, szego_transfer_det hAlpha z,
    normalized_szego_transfer_mem_su11 hAlpha w⟩

#print axioms canonical_szego_su11_transfer

/-- At the central Verblunsky coefficient, the transfer is diagonal. -/
theorem zero_szego_transfer_certificate (z : ℂ) :
    szegoRho 0 = 1 ∧
      szegoTransfer 0 z = !![z, 0; 0, 1] ∧
      Matrix.det (szegoTransfer 0 z) = z := by
  constructor
  · norm_num [szegoRho]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [szegoTransfer, szegoRho]
  · exact szego_transfer_det (by norm_num) z

/-- The explicit coefficient `alpha = 1/2` and phase `z = 2` have
`rho = sqrt 3 / 2`, the displayed four entries, and determinant two. -/
theorem half_szego_transfer_certificate :
    szegoRho (1 / 2 : ℂ) = Real.sqrt 3 / 2 ∧
      szegoTransfer (1 / 2 : ℂ) 2 =
        !![((4 / Real.sqrt 3 : ℝ) : ℂ), ((-1 / Real.sqrt 3 : ℝ) : ℂ);
           ((-2 / Real.sqrt 3 : ℝ) : ℂ), ((2 / Real.sqrt 3 : ℝ) : ℂ)] ∧
      Matrix.det (szegoTransfer (1 / 2 : ℂ) 2) = 2 := by
  have hAlpha : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hRho : szegoRho (1 / 2 : ℂ) = Real.sqrt 3 / 2 := by
    have hNormSq : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
      norm_num [Complex.normSq_apply]
    rw [szegoRho, hNormSq]
    norm_num
  constructor
  · exact hRho
  constructor
  · rw [szegoTransfer, hRho]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Complex.conj_ofNat] <;>
      field_simp [Complex.conj_ofNat] <;>
      ring
  · exact szego_transfer_det hAlpha 2

#print axioms half_szego_transfer_certificate

end D5.S3.Weil.Szego.CanonicalTransfer

/- GID: D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The scalar Gram discrepancy gives a dimension independent indexed spectral bound. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound

/-! Scalar discrepancy bounds pass from row Grams to column Grams. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinPsiMap
open D5.S3.Quantum.Matrix.LinGProperty
open D5.S3.Quantum.Schatten
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 800000 in
private theorem column_discrepancy {n : ℕ}
    (E : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ((δ : ℂ) • 1 - E * Eᴴ).PosSemidef) :
    ((δ : ℂ) • 1 - Eᴴ * E).PosSemidef := by
  let Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromRows E 0
  have hc : Zᴴ * Z = Eᴴ * E := by
    simp [Z, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hr : Z * Zᴴ = fromBlocks (E * Eᴴ) 0 0 (0 : Matrix (Fin n) (Fin n) ℂ) := by
    dsimp [Z]
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols]
    simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hz : ((δ : ℂ) • 1 - Z * Zᴴ).PosSemidef := by
    rw [hr]
    have hI := hE.mul_mul_conjTranspose_same
      (fromRows (1 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin n) ℂ))
    have hJ := (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hδ)).mul_mul_conjTranspose_same
      (fromRows (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ))
    have hh := hI.add hJ
    convert hh using 1
    simp only [conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
      conjTranspose_zero, fromRows_mul, fromRows_mul_fromCols, Matrix.one_mul,
      Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero]
    ext (i | i) (j | j) <;> simp [fromBlocks, Matrix.one_apply, Matrix.sub_apply]

  have hn : ‖Z * Zᴴ‖ ≤ δ := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hδ
      (posSemidef_self_mul_conjTranspose Z).nonneg).mpr
    rw [Algebra.algebraMap_eq_smul_one]
    change ((δ : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) - Z * Zᴴ).PosSemidef
    convert hz using 1
  have heq : ‖Zᴴ * Z‖ = ‖Z * Zᴴ‖ := by
    change ‖star Z * Z‖ = ‖Z * star Z‖
    rw [CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star]
  have hn' : ‖Zᴴ * Z‖ ≤ δ := by rw [heq]; exact hn
  have ho := (CStarAlgebra.norm_le_iff_le_algebraMap _ hδ
    (posSemidef_conjTranspose_mul_self Z).nonneg).mp hn'
  rw [Algebra.algebraMap_eq_smul_one] at ho
  change ((δ : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) - Zᴴ * Z).PosSemidef at ho
  rw [hc] at ho
  convert ho using 1

/-- A scalar ceiling on the block discrepancy controls every indexed singular value. -/
theorem gram_discrepancy_bound {n : ℕ}
    (A X B : Matrix (Fin n) (Fin n) ℂ)
    (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdisc : ((δ : ℂ) • 1 - (A + B - X - Xᴴ)).PosSemidef)
    (hAp : A.PosSemidef) (hBp : B.PosSemidef)
    (j : Fin (Fintype.card (Fin n))) :
    2 * singularValuesSorted X j ≤
      (hAp.1.add hBp.1).eigenvalues₀ j +
        δ / 2 := by
  classical
  let W := fromBlocks A X Xᴴ B
  let D := fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) X Xᴴ 0
  let J := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0
    (-1 : Matrix (Fin n) (Fin n) ℂ)
  let k : Fin (Fintype.card (Fin n ⊕ Fin n)) :=
    ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩
  have hD : D.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have h2D : ((2 : ℂ) • D).IsHermitian := hD.smul (by simp [IsSelfAdjoint])
  have hflip : (W - (2 : ℂ) • D).PosSemidef := by
    have h := hW.mul_mul_conjTranspose_same J
    convert h using 1
    dsimp [W, D, J]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    ext i l
    rcases i with i | i <;> rcases l with l | l <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply, Matrix.smul_apply] <;> ring
  have hfirst := eigenvalues_zero_mono_finite h2D hW.1 hflip k
  rw [eigenvalues_zero_smul_finite D hD 2 (by norm_num) h2D k,
    dilation_eigenvalues X hD j] at hfirst
  let Z := CFC.sqrt W
  have hZ : Zᴴ = Z := by
    simpa only [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg W).isSelfAdjoint.star_eq
  have hZZ : Z * Zᴴ = W := by
    rw [hZ]
    exact CFC.sqrt_mul_sqrt_self W hW.nonneg
  let U : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := Z.submatrix Sum.inl id
  let V : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := Z.submatrix Sum.inr id
  have hrows : fromRows U V = Z := by ext (i | i) l <;> rfl
  have hrows' : fromCols Uᴴ Vᴴ = Zᴴ := by
    rw [← conjTranspose_fromRows_eq_fromCols_conjTranspose, hrows]
  have hblocks : fromBlocks (U * Uᴴ) (U * Vᴴ) (V * Uᴴ) (V * Vᴴ) = W := by
    rw [← fromRows_mul_fromCols, hrows, hrows', hZZ]
  have hUU : U * Uᴴ = A := by
    ext i l
    exact congrArg (fun M => M (Sum.inl i) (Sum.inl l)) hblocks
  have hVV : V * Vᴴ = B := by
    ext i l
    exact congrArg (fun M => M (Sum.inr i) (Sum.inr l)) hblocks
  have hUV : U * Vᴴ = X := by
    ext i l
    exact congrArg (fun M => M (Sum.inl i) (Sum.inr l)) hblocks
  let L := Uᴴ * U + Vᴴ * V
  have hL : L.IsHermitian := (isHermitian_conjTranspose_mul_self U).add
    (isHermitian_conjTranspose_mul_self V)
  have hLL : Zᴴ * Z = L := by
    rw [← hrows, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hWL : W.charpoly = L.charpoly := by
    rw [← hZZ, ← hLL]
    exact charpoly_mul_comm Z Zᴴ
  have hspec := eigenvalues_zero_eq_of_charpoly hW.1 hL hWL k
  let T := U + V
  let F := (((1 / 2 : ℝ) : ℂ)) • (Tᴴ * T)
  have hF : F.IsHermitian := (isHermitian_conjTranspose_mul_self T).smul (by simp [IsSelfAdjoint])
  let C := F + ((δ / 2 : ℝ) : ℂ) • 1
  have hC : C.IsHermitian := hF.add (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hE : ((δ : ℂ) • 1 - (U - V) * (U - V)ᴴ).PosSemidef := by
    convert hdisc using 1
    have hVU : V * Uᴴ = Xᴴ := by rw [← hUV, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hUU, hVV, hUV, hVU]
    abel
  have hEc := column_discrepancy (U - V) hδ hE
  have hcorr : (C - L).PosSemidef := by
    have hh := hEc.smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1/2))
    convert hh using 1
    dsimp [C, F, T, L]
    simp only [conjTranspose_add, conjTranspose_sub, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub, smul_smul]
    ext i l
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    simp only [Complex.real_smul]
    push_cast
    ring
  have hsecond := eigenvalues_zero_mono_finite hL hC hcorr k
  rw [eigenvalues_zero_add_scalar_finite F hF (δ / 2) hC k,
    eigenvalues_zero_smul_finite (Tᴴ * T) (isHermitian_conjTranspose_mul_self T)
      (1 / 2) (by norm_num) hF k,
    rectangular_gram_eigenvalues T j] at hsecond
  have hrow : (((2 : ℂ) • (A + B)) - T * Tᴴ).PosSemidef := by
    simpa only [T, hUU, hVV] using row_gram_sum_comparison U V
  have hsum := hAp.1.add hBp.1
  have htwosum : ((2 : ℂ) • (A + B)).IsHermitian := hsum.smul (by simp [IsSelfAdjoint])
  have hthird := eigenvalues_zero_mono_finite (isHermitian_mul_conjTranspose_self T)
    htwosum hrow j
  rw [eigenvalues_zero_smul_finite (A + B) hsum 2 (by norm_num) htwosum j] at hthird
  rw [hspec] at hfirst
  change 2 * singularValuesSorted X j ≤ hsum.eigenvalues₀ j + δ / 2
  linarith


end D5.S3.Quantum.Matrix.LinPsiMap

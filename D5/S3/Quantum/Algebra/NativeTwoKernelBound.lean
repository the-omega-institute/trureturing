/- GID: D5/S3/Quantum/Algebra/NativeTwoKernelBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/NativeTwoKernelBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict native width-two compression at a<b forces twice the right dimension. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
import Mathlib.Tactic

/-!
# Strict native width-two compression

The Hermitian coefficient kernel vanishes at the strict native threshold, and
the resulting residual Gram blocks force the right input dimension bound.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.Algebra.NativeTwoKernelBound

open D5.S3.Quantum.Algebra.CommonCoefficientPlane
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
open D5.S3.Quantum.TensorNetworks.BridgeGraph
open D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

open private semidefinite_coefficient_kernel from D5.S3.Quantum.Algebra.CommonCoefficientPlane

private theorem stackK_compression_smul_add_two {a b : ℕ}
    (X : Fin 2 → Matrix (Fin a) (Fin b) ℂ) (z w : ℂ)
    (T U : Matrix (Fin 2) (Fin 2) ℂ) :
    (stackK X)ᴴ * Matrix.kronecker (z • T + w • U)
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X =
      z • ((stackK X)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X) +
      w • ((stackK X)ᴴ * Matrix.kronecker U
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X) := by
  rw [stackK_compression, stackK_compression, stackK_compression]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, smul_smul,
    add_smul, smul_add]

private theorem hermitian_compression_zero {a b : ℕ} (hab : a < b)
    (X : Fin 2 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stackK X).mulVecLin)
    (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.IsHermitian)
    (hPhi : (stackK X)ᴴ * Matrix.kronecker T
      (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X = 0) : T = 0 := by
  by_contra hne
  have hsum : ∑ r, ∑ s, T r s • ((X r)ᴴ * X s) = 0 := by
    rw [← stackK_compression X T]
    exact hPhi
  have hnotP : ¬ T.PosSemidef := by
    intro h
    exact hne (semidefinite_coefficient_kernel X hX T h hsum)
  have hsumNeg : ∑ r, ∑ s, (-T) r s • ((X r)ᴴ * X s) = 0 := by
    simpa only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero] using hsum
  have hnotN : ¬ (-T).PosSemidef := by
    intro h
    have hzero := semidefinite_coefficient_kernel X hX (-T) h hsumNeg
    exact hne (neg_eq_zero.mp hzero)
  obtain ⟨j, hj⟩ : ∃ j, hT.eigenvalues j < 0 := by
    by_contra h
    apply hnotP
    apply hT.posSemidef_iff_eigenvalues_nonneg.mpr
    intro j
    exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
  obtain ⟨i, hi⟩ : ∃ i, 0 < hT.eigenvalues i := by
    by_contra h
    have hnonpos : ∀ i, hT.eigenvalues i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hd : (Matrix.diagonal (fun i => (-(hT.eigenvalues i) : ℂ))).PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast neg_nonneg.mpr (hnonpos i)
    have hp := hd.mul_mul_conjTranspose_same
      (hT.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ)
    apply hnotN
    have hs := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [hs]
    convert hp using 1
    rw [Matrix.star_eq_conjTranspose]
    simp only [Function.comp_def]
    rw [show (Matrix.diagonal fun i => -(hT.eigenvalues i : ℂ)) =
        -(Matrix.diagonal fun i => (hT.eigenvalues i : ℂ)) by
      ext r s; by_cases hrs : r = s <;> simp [hrs]]
    rw [Matrix.mul_neg, Matrix.neg_mul]
    rfl
  have hij : i ≠ j := by
    intro he
    subst j
    linarith
  have hnonzero (r : Fin 2) : hT.eigenvalues r ≠ 0 := by
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simp_all [ne_of_gt, ne_of_lt]
  have hDunit : IsUnit
      (Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues) :
        Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun r =>
      isUnit_iff_ne_zero.mpr (by simpa using hnonzero r)))
  have hU : IsUnit (hT.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) :=
    Unitary.isUnit_coe (U := hT.eigenvectorUnitary)
  have hUstar' : IsUnit (star hT.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) :=
    Unitary.isUnit_coe (U := star hT.eigenvectorUnitary)
  have hTunit : IsUnit T := by
    have hs := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [hs]
    exact (hU.mul hDunit).mul hUstar'
  have hTrank : T.rank = 2 := by
    have hr := Matrix.rank_of_isUnit T hTunit
    simpa only [Fintype.card_fin] using hr
  have hS : (stackK X).rank = b := by
    change finrank ℂ (LinearMap.range (stackK X).mulVecLin) = b
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  let Q := Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ)
  have hzero : (stackK X)ᴴ * Q * stackK X = 0 := by
    simpa only [Q] using hPhi
  have hleft := Matrix.rank_mul_ge (stackK X)ᴴ Q
  have hright := Matrix.rank_mul_ge ((stackK X)ᴴ * Q) (stackK X)
  have hz : ((stackK X)ᴴ * Q * stackK X).rank = 0 := by
    rw [hzero]
    simp
  have hQ : Q.rank = a * T.rank := by
    exact rank_kronecker_one_general T
  simp only [Matrix.rank_conjTranspose, hS, Fintype.card_prod,
    Fintype.card_fin] at hleft hright
  rw [hQ, hTrank] at hleft
  omega

private theorem complex_compression_zero {a b : ℕ} (hab : a < b)
    (X : Fin 2 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stackK X).mulVecLin)
    (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hPhi : (stackK X)ᴴ * Matrix.kronecker T
      (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X = 0) : T = 0 := by
  have hPhiStar : (stackK X)ᴴ * Matrix.kronecker Tᴴ
      (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X = 0 := by
    have h := congrArg Matrix.conjTranspose hPhi
    have hk : (Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ))ᴴ =
        Matrix.kronecker Tᴴ (1 : Matrix (Fin a) (Fin a) ℂ) := by
      simpa only [Matrix.kronecker, Matrix.conjTranspose_one] using
        Matrix.conjTranspose_kronecker T (1 : Matrix (Fin a) (Fin a) ℂ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hk] at h
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.mul_assoc] using h
  let Tr : Matrix (Fin 2) (Fin 2) ℂ := (realPart T : Matrix (Fin 2) (Fin 2) ℂ)
  let Ti : Matrix (Fin 2) (Fin 2) ℂ := (imaginaryPart T : Matrix (Fin 2) (Fin 2) ℂ)
  have hTr : Tr.IsHermitian := (realPart T).property.isHermitian
  have hTi : Ti.IsHermitian := (imaginaryPart T).property.isHermitian
  have hTr_formula : Tr = ((2 : ℝ)⁻¹ : ℂ) • (T + Tᴴ) := by
    dsimp [Tr]
    rw [realPart_apply_coe]
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul]
    ring
  let c : ℂ := -Complex.I * ((2 : ℝ)⁻¹ : ℂ)
  have hTi_formula : Ti = c • (T - Tᴴ) := by
    dsimp [Ti]
    rw [imaginaryPart_apply_coe]
    ext i j
    simp [c, Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul, smul_smul]
    ring
  have hPhiTr : (stackK X)ᴴ * Matrix.kronecker Tr
      (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X = 0 := by
    rw [hTr_formula]
    have h := stackK_compression_smul_add_two X ((2 : ℝ)⁻¹ : ℂ) ((2 : ℝ)⁻¹ : ℂ) T Tᴴ
    rw [hPhi, hPhiStar] at h
    simpa only [smul_add, smul_zero, zero_add] using h
  have hPhiTi : (stackK X)ᴴ * Matrix.kronecker Ti
      (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X = 0 := by
    rw [hTi_formula, sub_eq_add_neg, smul_add, smul_neg]
    have h := stackK_compression_smul_add_two X c (-c) T Tᴴ
    rw [hPhi, hPhiStar] at h
    simpa only [smul_sub, sub_eq_add_neg, neg_smul, smul_zero, zero_add] using h
  have hTr0 := hermitian_compression_zero hab X hX hinj Tr hTr hPhiTr
  have hTi0 := hermitian_compression_zero hab X hX hinj Ti hTi hPhiTi
  have hdecomp : Tr + Complex.I • Ti = T := by
    exact realPart_add_I_smul_imaginaryPart T
  rw [← hdecomp, hTr0, hTi0]
  simp

theorem right_dimension_bound {a b c d : ℕ} (hab : a < b)
    (M : Fin 2 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 2 → Matrix (Fin d) (Fin c) ℂ)
    (hM : LinearIndependent ℂ M)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMG : ∑ r, (M r)ᴴ * M r = 1) : 2 * c ≤ d := by
  have hSGram : (stackK M)ᴴ * stackK M = 1 := by
    rw [stackK_gram]
    exact hMG
  have hSinj : Function.Injective (stackK M).mulVecLin :=
    gram_identity_injective (stackK M) hSGram
  have hRzero (l m : Fin c) :
      (fun r s : Fin 2 => ((N r)ᴴ * N s) l m -
        (if r = s then if l = m then 1 else 0 else 0)) = 0 := by
    apply complex_compression_zero hab M hM hSinj
    rw [stackK_compression]
    exact block_kernel M N hF hMG l m
  have hNcross (r s : Fin 2) : (N r)ᴴ * N s =
      (if r = s then (1 : ℂ) else 0) • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    ext l m
    have ht := congrArg (fun X => X r s) (hRzero l m)
    have he := sub_eq_zero.mp ht
    by_cases hrs : r = s <;> by_cases hlm : l = m <;>
      simpa [hrs, hlm, Matrix.one_apply] using he
  have hconcat : (concatK N)ᴴ * concatK N = Matrix.kronecker
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin c) (Fin c) ℂ) :=
    concatK_gram N 1 hNcross
  have hI : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin c) (Fin c) ℂ) = 1 := by
    ext ⟨r, l⟩ ⟨s, m⟩
    by_cases hrs : r = s <;> by_cases hlm : l = m <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hrs, hlm]
  have hr := (Matrix.rank_mul_le_right (concatK N)ᴴ (concatK N)).trans
    (concatK N).rank_le_card_height
  rw [hconcat, hI, Matrix.rank_one] at hr
  simpa only [Fintype.card_prod, Fintype.card_fin] using hr

end D5.S3.Quantum.Algebra.NativeTwoKernelBound

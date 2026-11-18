/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A native rectangular width-three positive scalar column Gram above the three-halves threshold forces twice the opposite input dimension. -/

import D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
import D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
import D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum

/-! A native tensor-event dimension bound, including reduced widths and zero dimensions. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

private theorem weighted_gram {a b c d k : ℕ}
    (M : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin k → Matrix (Fin d) (Fin c) ℂ)
    (hc : 0 < c)
    (hF : (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = 1) :
    (∑ s, ∑ t, ((1 / (c : ℂ) : ℂ) * trace ((N s)ᴴ * N t)) • ((M s)ᴴ * M t)) = 1 := by
  classical
  let T : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ →ₗ[ℂ]
      Matrix (Fin b) (Fin b) ℂ :=
    { toFun := partialTraceRight
      map_add' := partialTraceRight_add
      map_smul' := by
        intro c A
        ext i j
        simp [partialTraceRight, Finset.mul_sum] }
  have hExp : (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) =
      ∑ s, ∑ t, kronecker ((M s)ᴴ * M t) ((N s)ᴴ * N t) := by
    simp only [Matrix.kronecker, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    exact Finset.sum_comm
  have hT := congrArg T (hExp.symm.trans hF)
  have hT1 : T 1 = (c : ℂ) • (1 : Matrix (Fin b) (Fin b) ℂ) := by
    ext i j
    simp [T, partialTraceRight, Matrix.one_apply]
  simp only [map_sum] at hT
  change (∑ s, ∑ t, partialTraceRight (kronecker ((M s)ᴴ * M t) ((N s)ᴴ * N t))) = T 1 at hT
  simp only [partialTraceRight_kronecker] at hT
  rw [hT1] at hT
  have h := congrArg (fun A => (1 / (c : ℂ) : ℂ) • A) hT
  simpa [Finset.smul_sum, smul_smul, hc.ne'] using h

private theorem mixed_energy {a b k : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
    (M : Fin k → Matrix (Fin a) (Fin b) ℂ) :
    (∑ r, (mix B M r)ᴴ * mix B M r) =
      ∑ s, ∑ t, (Bᴴ * B) s t • ((M s)ᴴ * M t) := by
  classical
  simp only [mix, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_smul]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm]

private theorem tensor_mix {a b c d k : ℕ} (B C : Matrix (Fin k) (Fin k) ℂ)
    (hBC : B.transpose * C = 1)
    (M : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin k → Matrix (Fin d) (Fin c) ℂ) :
    (∑ r, kronecker (mix B M r) (mix C N r)) = ∑ r, kronecker (M r) (N r) := by
  classical
  apply Matrix.ext
  intro p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨a, b⟩
  have hcoeff (s t : Fin k) : (∑ r, B r s * C r t) = if s = t then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hBC s) t
  have hterm (r s t : Fin k) : B r s * M s i a * (C r t * N t j b) =
      (B r s * C r t) * (M s i a * N t j b) := by ring
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, mix_apply,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext t
    rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcoeff]
  simp

theorem exact_whitening {a b c d k : ℕ}
    (M : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin k → Matrix (Fin d) (Fin c) ℂ)
    (hN : LinearIndependent ℂ N)
    (hc : 0 < c)
    (hF : (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, IsUnit B ∧
      (fun r s => (1 / (c : ℂ) : ℂ) * trace ((N r)ᴴ * N s)) = Bᴴ * B ∧
      (let C := B.transpose⁻¹
       let Mprime := mix B M
       let Nprime := mix C N
       (∑ r, kronecker (Mprime r) (Nprime r)) = (∑ r, kronecker (M r) (N r)) ∧
       (∑ r, (Mprime r)ᴴ * Mprime r) = 1 ∧
       (LinearIndependent ℂ M → LinearIndependent ℂ Mprime)) := by
  classical
  let H : Matrix (Fin k) (Fin k) ℂ :=
    fun r s => (1 / (c : ℂ) : ℂ) * trace ((N r)ᴴ * N s)
  have hH : H = (1 / (c : ℝ) : ℝ) • ((flat N)ᴴ * flat N) := by
    rw [← flat_gram]
    ext r s
    simp [H, Complex.real_smul, Matrix.smul_apply, Pi.smul_apply]
  have hpos : H.PosDef := by
    rw [hH]
    exact ((Matrix.PosDef.conjTranspose_mul_self (flat N) (flat_injective N hN)).smul
      (by positivity : (0 : ℝ) < 1 / (c : ℝ)))
  obtain ⟨B, hB, hBB⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hpos.isStrictlyPositive
  change H = Bᴴ * B at hBB
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hdetT : IsUnit B.transpose.det := by simpa using hdet
  let C := B.transpose⁻¹
  have hBC : B.transpose * C = 1 := Matrix.mul_nonsing_inv _ hdetT
  refine ⟨B, hB, hBB, tensor_mix B C hBC M N, ?_, ?_⟩
  · rw [mixed_energy, ← hBB]
    exact weighted_gram M N hc hF
  · intro hM
    exact hM.sum_smul_of_nondegenerate (Matrix.nondegenerate_of_det_ne_zero hdet.ne_zero)

def stackK {a b k : ℕ} (M : Fin k → Matrix (Fin a) (Fin b) ℂ) :
    Matrix (Fin k × Fin a) (Fin b) ℂ :=
  fun p j => M p.1 p.2 j

theorem stackK_gram {a b k : ℕ} (M : Fin k → Matrix (Fin a) (Fin b) ℂ) :
    (stackK M)ᴴ * stackK M = ∑ r, (M r)ᴴ * M r := by
  ext i j
  simp only [stackK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]

theorem block_kernel {a b c d k : ℕ}
    (M : Fin k → Matrix (Fin a) (Fin b) ℂ) (N : Fin k → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (l m : Fin c) :
    ∑ r, ∑ s, (((N r)ᴴ * N s) l m -
      (if r = s then if l = m then 1 else 0 else 0)) • ((M r)ᴴ * M s) = 0 := by
  have hExp : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) =
      ∑ r, ∑ s, Matrix.kronecker ((M r)ᴴ * M s) ((N r)ᴴ * N s) := by
    simp only [Matrix.kronecker, Matrix.conjTranspose_sum, Matrix.sum_mul,
      Matrix.mul_sum, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    exact Finset.sum_comm
  rw [hExp] at hF
  ext u v
  have h := congrArg (fun A : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ =>
    A (u, l) (v, m)) hF
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq] at h
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have h' : ∑ r, ∑ s, ((N r)ᴴ * N s) l m * ((M r)ᴴ * M s) u v =
      (if u = v ∧ l = m then 1 else 0) := by
    simpa [mul_comm] using h
  rw [h']
  have hdelta :
      ∑ r, ∑ s, (if r = s then if l = m then 1 else 0 else 0) *
          ((M r)ᴴ * M s) u v =
        (if l = m then (∑ r, (M r)ᴴ * M r) u v else 0) := by
    by_cases hlm : l = m
    · subst m
      simp [Matrix.sum_apply]
    · simp [hlm]
  rw [hdelta]
  have hMEntry (i j : Fin b) :
      (∑ r, (M r)ᴴ * M r) i j = (if i = j then 1 else 0) := by
    simpa [Matrix.one_apply] using congrArg
      (fun A : Matrix (Fin b) (Fin b) ℂ => A i j) hMGram
  by_cases huv : u = v
  · subst v
    by_cases hlm : l = m
    · rw [hMEntry]
      simp [hlm]
    · rw [hMEntry]
      simp [hlm]
  · by_cases hlm : l = m
    · rw [hMEntry]
      simp [huv, hlm]
    · simp [huv, hlm]

theorem stackK_compression_conjTranspose {a b : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ) :
    (stackK M)ᴴ * Matrix.kronecker Tᴴ (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M =
      ((stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) *
        stackK M)ᴴ := by
  have hk : (Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ))ᴴ =
      Matrix.kronecker Tᴴ (1 : Matrix (Fin a) (Fin a) ℂ) := by
    simpa only [Matrix.kronecker, Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker T (1 : Matrix (Fin a) (Fin a) ℂ)
  rw [← hk]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem block_compression {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1) (l m : Fin c) :
    let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
      ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
    (stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) *
      stackK M = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
    ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
  change (stackK M)ᴴ * Matrix.kronecker T
      (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M = 0
  change D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M T = 0
  rw [D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum]
  exact block_kernel M N hF hMGram l m

theorem stackK_compression_smul_add {a b : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (z w : ℂ) (T U : Matrix (Fin 3) (Fin 3) ℂ) :
    (stackK M)ᴴ * Matrix.kronecker (z • T + w • U)
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M =
      z • ((stackK M)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M) +
      w • ((stackK M)ᴴ * Matrix.kronecker U
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M) := by
  change D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M (z • T + w • U) =
    z • D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M T +
    w • D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M U
  rw [D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    add_smul, smul_add]

theorem complex_block_neutral {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (L : Submodule ℂ (Fin 3 → ℂ))
    (hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      (stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) *
        stackK M = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0)
    (l m : Fin c) :
    ∀ u ∈ L, ∀ v ∈ L,
      star u ⬝ᵥ ((fun r s =>
        ((N r)ᴴ * N s) l m -
          (if r = s then if l = m then 1 else 0 else 0)) *ᵥ v) = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
    ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
  let Tr : Matrix (Fin 3) (Fin 3) ℂ := (realPart T : Matrix (Fin 3) (Fin 3) ℂ)
  let Ti : Matrix (Fin 3) (Fin 3) ℂ :=
    (imaginaryPart T : Matrix (Fin 3) (Fin 3) ℂ)
  have hc : (stackK M)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M = 0 := by
    exact block_compression M N hF hMGram l m
  have hcstar : (stackK M)ᴴ * Matrix.kronecker Tᴴ
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M = 0 := by
    rw [stackK_compression_conjTranspose, hc, Matrix.conjTranspose_zero]
  have hTr : Tr.IsHermitian := by
    exact (realPart T).property.isHermitian
  have hTi : Ti.IsHermitian := by
    exact (imaginaryPart T).property.isHermitian
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
  have hcTr : (stackK M)ᴴ * Matrix.kronecker Tr
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M = 0 := by
    rw [hTr_formula]
    have h := stackK_compression_smul_add M ((2 : ℝ)⁻¹ : ℂ) ((2 : ℝ)⁻¹ : ℂ) T Tᴴ
    rw [hc, hcstar] at h
    simpa only [smul_add, smul_zero, zero_add] using h
  have hcTi : (stackK M)ᴴ * Matrix.kronecker Ti
        (1 : Matrix (Fin a) (Fin a) ℂ) * stackK M = 0 := by
    rw [hTi_formula, sub_eq_add_neg, smul_add, smul_neg]
    have h := stackK_compression_smul_add M c (-c) T Tᴴ
    rw [hc, hcstar] at h
    simpa only [smul_sub, sub_eq_add_neg, neg_smul, smul_zero, zero_add] using h
  intro u hu v hv
  have hr := hplane Tr hTr hcTr u hu v hv
  have hi := hplane Ti hTi hcTi u hu v hv
  have hdecomp : Tr + Complex.I • Ti = T := by
    exact realPart_add_I_smul_imaginaryPart T
  change star u ⬝ᵥ (T *ᵥ v) = 0
  rw [← hdecomp]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, hr, hi]
  simp

private theorem native_three_bound {a0 b0 c0 d0 : ℕ} (hab : 3 * a0 < 2 * b0)
    (M : Fin 3 → Matrix (Fin a0) (Fin b0) ℂ)
    (N : Fin 3 → Matrix (Fin d0) (Fin c0) ℂ) (hM : LinearIndependent ℂ M)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMG : ∑ r, (M r)ᴴ * M r = 1) : 2 * c0 ≤ d0 := by
  have hstackGram : (stackK M)ᴴ * stackK M = 1 := by
    rw [stackK_gram]
    exact hMG
  have hstackInj : Function.Injective (stackK M).mulVecLin :=
    gram_identity_injective (stackK M) hstackGram
  obtain ⟨L, hLdim, hL⟩ :=
    D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane.common_plane hab M hM hstackInj
  have hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      (stackK M)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a0) (Fin a0) ℂ) * stackK M = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
    intro T hT hcomp u hu v hv
    have hcomp' : (D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M)ᴴ *
        Matrix.kronecker T (1 : Matrix (Fin a0) (Fin a0) ℂ) *
          D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M = 0 := by
      have hs : D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M =
          stackK M := rfl
      rw [hs]
      exact hcomp
    exact hL T hT hcomp' u hu v hv
  have hneutral := complex_block_neutral M N hF hMG L hplane
  let e : (Fin 3 → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
    (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).symm
  let Le : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) := L.map e.toLinearMap
  have hLedim : finrank ℂ Le = 2 := by
    rw [LinearEquiv.finrank_map_eq e, hLdim]
  let b : OrthonormalBasis (Fin 2) ℂ Le := hLedim ▸ stdOrthonormalBasis ℂ Le
  let V : Matrix (Fin 3) (Fin 2) ℂ := fun i a =>
    (WithLp.ofLp ((b a : Le) : EuclideanSpace ℂ (Fin 3))) i
  have hVgram : Vᴴ * V = 1 := by
    ext a c
    have hb := (orthonormal_iff_ite.mp b.orthonormal) a c
    simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      PiLp.inner_apply, dotProduct, Matrix.one_apply, mul_comm] using hb
  have hVplane : ∀ (l m : Fin c0) (a c : Fin 2),
      ∑ r, ∑ s, star (V r a) *
        (((N r)ᴴ * N s) l m -
          (if r = s then if l = m then 1 else 0 else 0)) * V s c = 0 := by
    intro l m a c
    obtain ⟨u, hu, hueq⟩ := (b a).property
    obtain ⟨v, hv, hveq⟩ := (b c).property
    have hVa (r : Fin 3) : V r a = u r := by
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z r) hueq
      simpa [V, e] using hh.symm
    have hVc (r : Fin 3) : V r c = v r := by
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z r) hveq
      simpa [V, e] using hh.symm
    have hh := hneutral l m u hu v hv
    simpa [Matrix.mulVec, dotProduct, hVa, hVc, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hh
  let W : Matrix (Fin d0) (Fin 3 × Fin c0) ℂ := concatK N
  let P : Matrix (Fin 3 × Fin c0) (Fin 3 × Fin c0) ℂ := Wᴴ * W
  let C : Matrix (Fin 3 × Fin c0) (Fin 2 × Fin c0) ℂ :=
    Matrix.kronecker V (1 : Matrix (Fin c0) (Fin c0) ℂ)
  have hPentry (r s : Fin 3) (l m : Fin c0) : P (r, l) (s, m) =
      ((N r)ᴴ * N s) l m := by
    rfl
  have hCPC : Cᴴ * P * C = 1 := by
    have hCentry (r : Fin 3) (i : Fin c0) (a : Fin 2) (l : Fin c0) :
        C (r, i) (a, l) = if i = l then V r a else 0 := by
      by_cases h : i = l <;> simp [C, Matrix.kronecker,
        Matrix.kroneckerMap_apply, h]
    ext ⟨a, l⟩ ⟨c, m⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.conjTranspose_apply]
    simp_rw [hCentry, hPentry]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_mul, Finset.mul_sum]
    have hz := hVplane l m a c
    have hv : ∑ r, ∑ s, star (V r a) *
        ((if r = s then if l = m then 1 else 0 else 0)) * V s c =
        (if l = m then (Vᴴ * V) a c else 0) := by
      by_cases hlm : l = m
      · subst m
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
          Finset.sum_mul, Finset.mul_sum]
      · simp [hlm]
    have hsum (r s : Fin 3) :
        ∑ i : Fin c0, star (if i = l then V r a else 0) *
          ((N r)ᴴ * N s) i m * V s c =
          star (V r a) * ((N r)ᴴ * N s) l m * V s c := by
      classical
      rw [Finset.sum_eq_single l]
      · simp
      · intro b hb hbl
        simp [hbl]
      · simp
    simp_rw [hsum]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at hz
    rw [hv, hVgram] at hz
    rw [Finset.sum_comm]
    by_cases hac : a = c <;> by_cases hlm : l = m
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
  have hRank : (Cᴴ * P * C).rank ≤ d0 := by
    calc
      (Cᴴ * P * C).rank ≤ P.rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ ≤ W.rank := Matrix.rank_mul_le_right _ _
      _ ≤ d0 := by simpa using W.rank_le_card_height
  rw [hCPC, Matrix.rank_one] at hRank
  simpa only [Fintype.card_prod, Fintype.card_fin] using hRank

theorem stackK_compression {a b k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ) (T : Matrix (Fin k) (Fin k) ℂ) :
    (stackK X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X =
      ∑ r, ∑ s, T r s • ((X r)ᴴ * X s) := by
  classical
  ext j l
  simp only [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, stackK, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem two_compression_zero {a b : ℕ} (hab : 3 * a < 2 * b)
    (S : Matrix (Fin 2 × Fin a) (Fin b) ℂ)
    (hinj : Function.Injective S.mulVecLin)
    (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hT : Sᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * S = 0) : T = 0 := by
  have hS : S.rank = b := by
    change finrank ℂ (LinearMap.range S.mulVecLin) = b
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  by_contra hne
  have hTr : 0 < T.rank := by
    by_contra h
    have hmap : T.mulVecLin = 0 := by
      apply LinearMap.range_eq_bot.mp
      exact Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    exact hne (Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply', map_zero] using hmap))
  let Q := Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ)
  have hQ : Q.rank = a * T.rank := rank_kronecker_one_general T
  have hleft := Matrix.rank_mul_ge Sᴴ Q
  have hright := Matrix.rank_mul_ge (Sᴴ * Q) S
  have hz : (Sᴴ * Q * S).rank = 0 := by rw [show Sᴴ * Q * S = 0 from hT]; simp
  simp only [Matrix.rank_conjTranspose, hS, Fintype.card_prod,
    Fintype.card_fin] at hleft hright
  rw [hQ] at hleft
  have hm := Nat.mul_le_mul_left a hTr
  omega

private theorem native_two_bound {a b c d : ℕ} (hab : 3 * a < 2 * b)
    (M : Fin 2 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 2 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMG : ∑ r, (M r)ᴴ * M r = 1) : 2 * c ≤ d := by
  have hSGram : (stackK M)ᴴ * stackK M = 1 := by rw [stackK_gram]; exact hMG
  have hSinj := gram_identity_injective (stackK M) hSGram
  let T : Fin c → Fin c → Matrix (Fin 2) (Fin 2) ℂ :=
    fun l m r s => ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
  have hTzero (l m : Fin c) : T l m = 0 := by
    apply two_compression_zero hab (stackK M) hSinj (T l m)
    rw [stackK_compression]
    exact block_kernel M N hF hMG l m
  have hNcross (r s : Fin 2) : (N r)ᴴ * N s =
      (if r = s then (1 : ℂ) else 0) • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    ext l m
    have ht := congrArg (fun X => X r s) (hTzero l m)
    have ht' : ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0) = 0 := ht
    have he := sub_eq_zero.mp ht'
    by_cases hrs : r = s <;> by_cases hlm : l = m <;>
      simpa [hrs, hlm, Matrix.one_apply] using he
  have hconcat : (concatK N)ᴴ * concatK N = Matrix.kronecker
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin c) (Fin c) ℂ) := concatK_gram N 1 hNcross
  have hI : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin c) (Fin c) ℂ) = 1 := by
    ext ⟨r,l⟩ ⟨s,m⟩
    by_cases hrs : r = s <;> by_cases hlm : l = m <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hrs, hlm]
  have hr := (Matrix.rank_mul_le_right (concatK N)ᴴ (concatK N)).trans
    (concatK N).rank_le_card_height
  rw [hconcat, hI, Matrix.rank_one] at hr
  simpa only [Fintype.card_prod, Fintype.card_fin] using hr

private theorem reduce_left {a b c d n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin a) (Fin b) ℂ) (D : Fin (n + 1) → Matrix (Fin d) (Fin c) ℂ)
    (g : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (hg : g i ≠ 0) (hrel : (∑ j, g j • A j) = 0) :
    ∃ A' : Fin n → Matrix (Fin a) (Fin b) ℂ, ∃ D' : Fin n → Matrix (Fin d) (Fin c) ℂ,
      (∑ j, Matrix.kronecker (A' j) (D' j)) =
        (∑ j, Matrix.kronecker (A j) (D j)) := by
  classical
  let A' : Fin n → Matrix (Fin a) (Fin b) ℂ := fun j => A (i.succAbove j)
  let D' : Fin n → Matrix (Fin d) (Fin c) ℂ := fun j =>
    D (i.succAbove j) - (g (i.succAbove j) / g i) • D i
  have hsplit : (∑ j : Fin (n + 1), g j • A j) =
      g i • A i + ∑ j : Fin n, g (i.succAbove j) • A (i.succAbove j) := by
    rw [Fin.univ_succAbove n i]
    simp [Finset.sum_map]
  have hai : A i = ∑ j : Fin n, (-(g (i.succAbove j) / g i)) • A (i.succAbove j) := by
    have h := hsplit.symm.trans hrel
    rw [add_eq_zero_iff_eq_neg] at h
    have hi : A i = (g i)⁻¹ • (-(∑ j : Fin n, g (i.succAbove j) • A (i.succAbove j))) :=
      (eq_inv_smul_iff₀ hg).mpr h
    rw [hi, smul_neg, Finset.smul_sum]
    rw [← (Finset.univ : Finset (Fin n)).sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have hsum : (∑ j : Fin (n + 1), Matrix.kronecker (A j) (D j)) =
      Matrix.kronecker (A i) (D i) +
        ∑ j : Fin n, Matrix.kronecker (A (i.succAbove j)) (D (i.succAbove j)) := by
    rw [Fin.univ_succAbove n i]
    simpa only [Finset.sum_cons, Finset.sum_map, Fin.coe_succAboveEmb]
  refine ⟨A', D', ?_⟩
  rw [hsum, hai]
  simp only [A', D']
  change (∑ j, (Matrix.kroneckerBilinear (R := ℂ)) _ _) =
    (Matrix.kroneckerBilinear (R := ℂ)) (∑ j, _) _ + ∑ j, _
  simp only [map_sum, LinearMap.sum_apply, map_sub, map_smul, LinearMap.smul_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ext ⟨r, l⟩ ⟨m, s⟩
  simp only [sub_eq_add_neg, neg_smul, Matrix.kronecker, Matrix.kroneckerBilinear,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply]
  simp [Algebra.coe_lmul_eq_mul]
  ring

private theorem reduce_right {a b c d n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin a) (Fin b) ℂ) (D : Fin (n + 1) → Matrix (Fin d) (Fin c) ℂ)
    (g : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (hg : g i ≠ 0) (hrel : (∑ j, g j • D j) = 0) :
    ∃ A' : Fin n → Matrix (Fin a) (Fin b) ℂ, ∃ D' : Fin n → Matrix (Fin d) (Fin c) ℂ,
      (∑ j, Matrix.kronecker (A' j) (D' j)) =
        (∑ j, Matrix.kronecker (A j) (D j)) := by
  classical
  let A' : Fin n → Matrix (Fin a) (Fin b) ℂ := fun j =>
    A (i.succAbove j) - (g (i.succAbove j) / g i) • A i
  let D' : Fin n → Matrix (Fin d) (Fin c) ℂ := fun j => D (i.succAbove j)
  have hsplit : (∑ j : Fin (n + 1), g j • D j) =
      g i • D i + ∑ j : Fin n, g (i.succAbove j) • D (i.succAbove j) := by
    rw [Fin.univ_succAbove n i]
    simp [Finset.sum_map]
  have hdi : D i = ∑ j : Fin n, (-(g (i.succAbove j) / g i)) • D (i.succAbove j) := by
    have h := hsplit.symm.trans hrel
    rw [add_eq_zero_iff_eq_neg] at h
    have hi : D i = (g i)⁻¹ • (-(∑ j : Fin n, g (i.succAbove j) • D (i.succAbove j))) :=
      (eq_inv_smul_iff₀ hg).mpr h
    rw [hi, smul_neg, Finset.smul_sum]
    rw [← (Finset.univ : Finset (Fin n)).sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have hsum : (∑ j : Fin (n + 1), Matrix.kronecker (A j) (D j)) =
      Matrix.kronecker (A i) (D i) +
        ∑ j : Fin n, Matrix.kronecker (A (i.succAbove j)) (D (i.succAbove j)) := by
    rw [Fin.univ_succAbove n i]
    simpa only [Finset.sum_cons, Finset.sum_map, Fin.coe_succAboveEmb]
  refine ⟨A', D', ?_⟩
  rw [hsum, hdi]
  simp only [A', D']
  change (∑ j, (Matrix.kroneckerBilinear (R := ℂ)) _ _) =
    (Matrix.kroneckerBilinear (R := ℂ)) _ (∑ j, _) + ∑ j, _
  simp only [map_sum, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ext ⟨r, l⟩ ⟨m, s⟩
  simp only [sub_eq_add_neg, neg_smul, Matrix.kronecker, Matrix.kroneckerBilinear,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply]
  simp [Algebra.coe_lmul_eq_mul]
  ring

private theorem minimal_decomposition {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) :
    ∃ k : ℕ, k ≤ 3 ∧ ∃ A : Fin k → Matrix (Fin a) (Fin b) ℂ, ∃ D : Fin k → Matrix (Fin d) (Fin c) ℂ,
      LinearIndependent ℂ A ∧ LinearIndependent ℂ D ∧
        (∑ j, Matrix.kronecker (A j) (D j)) =
          (∑ r, Matrix.kronecker (M r) (N r)) := by
  classical
  let p : ℕ → Prop := fun k => ∃ A : Fin k → Matrix (Fin a) (Fin b) ℂ,
    ∃ D : Fin k → Matrix (Fin d) (Fin c) ℂ,
      (∑ j, Matrix.kronecker (A j) (D j)) =
        (∑ r, Matrix.kronecker (M r) (N r))
  have h3 : p 3 := ⟨M, N, rfl⟩
  have hp : ∃ k, p k := ⟨3, h3⟩
  have hmin : ∀ n < Nat.find hp, ¬p n := by
    intro n hn hpn
    have hle : Nat.find hp ≤ n := Nat.find_min' hp hpn
    omega
  have hfind_le : Nat.find hp ≤ 3 := by
    by_contra h
    have hlt3 : 3 < Nat.find hp := by omega
    exact (hmin 3 hlt3) h3
  rcases Nat.eq_zero_or_pos (Nat.find hp) with hzero | hpos
  · have hk : p 0 := by simpa [hzero] using (Nat.find_spec hp)
    obtain ⟨A, D, hsum⟩ := hk
    refine ⟨0, by omega, A, D, ?_, ?_, hsum⟩ <;> simp
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hk : p (n + 1) := by simpa [hn] using (Nat.find_spec hp)
    obtain ⟨A, D, hsum⟩ := hk
    have hA : LinearIndependent ℂ A := by
      by_contra hA
      rcases (Fintype.not_linearIndependent_iff.mp hA) with ⟨g, hg, i, hi⟩
      rcases reduce_left A D g i hi hg with ⟨A', D', hred⟩
      exact (hmin n (by omega)) ⟨A', D', hred.trans hsum⟩
    have hD : LinearIndependent ℂ D := by
      by_contra hD
      rcases (Fintype.not_linearIndependent_iff.mp hD) with ⟨g, hg, i, hi⟩
      rcases reduce_right A D g i hi hg with ⟨A', D', hred⟩
      exact (hmin n (by omega)) ⟨A', D', hred.trans hsum⟩
    refine ⟨n + 1, by omega, A, D, hA, hD, hsum⟩

theorem normalized_minimal_decomposition {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
        (∑ r, Matrix.kronecker (M r) (N r)) =
      (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) :
    ∃ k : ℕ, k ≤ 3 ∧ ∃ A : Fin k → Matrix (Fin a) (Fin b) ℂ, ∃ D : Fin k → Matrix (Fin d) (Fin c) ℂ,
      LinearIndependent ℂ A ∧ LinearIndependent ℂ D ∧
        (∑ j, Matrix.kronecker (A j) (D j)) =
          (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
            (∑ r, Matrix.kronecker (M r) (N r)) ∧
        (∑ j, Matrix.kronecker (A j) (D j))ᴴ *
            (∑ j, Matrix.kronecker (A j) (D j)) =
          (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ) := by
  classical
  obtain ⟨k, hk, A, D, hA, hD, hsum⟩ := minimal_decomposition M N
  let ζ : ℂ := (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)
  have hsqrt : (Real.sqrt lambda) ^ 2 = lambda := by
    simpa [pow_two] using (Real.sq_sqrt (le_of_lt hlambda))
  have hsqrt_ne : Real.sqrt lambda ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlambda)
  have hc : ζ ≠ 0 := by
    dsimp [ζ]
    exact_mod_cast (inv_ne_zero hsqrt_ne)
  let A' : Fin k → Matrix (Fin a) (Fin b) ℂ := fun j => ζ • A j
  have hA' : LinearIndependent ℂ A' := by
    exact hA.units_smul (fun _ => Units.mk0 ζ hc)
  have hsum' : (∑ j, Matrix.kronecker (A' j) (D j)) = ζ •
      (∑ r, Matrix.kronecker (M r) (N r)) := by
    change (∑ j, (Matrix.kroneckerBilinear (R := ℂ)) (ζ • A j) (D j)) = _
    simp only [map_smul, LinearMap.smul_apply, ← Finset.smul_sum]
    exact congrArg (fun X : Matrix (Fin a × Fin d) (Fin b × Fin c) ℂ => ζ • X) hsum
  have hcc : (star ζ) * ζ * (lambda : ℂ) = 1 := by
    have hreal : (Real.sqrt lambda)⁻¹ * (Real.sqrt lambda)⁻¹ * lambda = 1 := by
      field_simp [hsqrt_ne]
      nlinarith [hsqrt]
    dsimp [ζ]
    simpa [Complex.star_def] using congrArg (fun x : ℝ => (x : ℂ)) hreal
  have hgram : (∑ j, Matrix.kronecker (A' j) (D j))ᴴ *
      (∑ j, Matrix.kronecker (A' j) (D j)) =
      (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ) := by
    rw [hsum']
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hF]
    have hscalar : ζ * (star ζ * (lambda : ℂ)) = 1 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcc
    rw [hscalar]
    simp
  exact ⟨k, hk, A', D, hA', hD, hsum', hgram⟩

/-- The native tensor event, with arbitrary factors and all natural dimensions. -/
theorem bound {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hab : 3 * a < 2 * b)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) =
        (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) : 2 * c ≤ d := by
  classical
  by_cases hcz : c = 0
  · simp [hcz]
  have hc : 0 < c := Nat.pos_of_ne_zero hcz
  by_cases hstrong : 2 * a < b
  · have hthree := RestrictedFlatSpectrum.obstruction M N hc hstrong lambda hlambda hF
    omega
  obtain ⟨k, hk, A, D, hA, hD, hsum, hgram⟩ :=
    normalized_minimal_decomposition M N lambda hlambda hF
  obtain ⟨B, hB, hBB, hPres, hMGram, hMLI⟩ := exact_whitening A D hD hc hgram
  let M' := mix B A
  let N' := mix B.transpose⁻¹ D
  have hM' : LinearIndependent ℂ M' := hMLI hA
  have hMG : ∑ r, (M' r)ᴴ * M' r = 1 := hMGram
  have hFG : (∑ r, Matrix.kronecker (M' r) (N' r))ᴴ *
      (∑ r, Matrix.kronecker (M' r) (N' r)) = 1 := by
    simpa only [M', N', hPres] using hgram
  have hSG : (stackK M')ᴴ * stackK M' = 1 := by rw [stackK_gram]; exact hMG
  have hSI := gram_identity_injective (stackK M') hSG
  have hdim := LinearMap.finrank_le_finrank_of_injective hSI
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at hdim
  interval_cases k
  · omega
  · omega
  · exact native_two_bound hab M' N' hFG hMG
  · exact native_three_bound hab M' N' hM' hFG hMG

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

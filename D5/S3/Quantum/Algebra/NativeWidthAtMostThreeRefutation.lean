/- GID: D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation
   generality: E
   mirror-B: D5/B/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.claim; result=D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.result; claim=D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.claim
   digest: The original universal positive-scalar inner-cone event is false on native width three. -/

import D5.S3.Quantum.Algebra.CommonCoefficientPlane
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.Algebra.NativeCoefficientWhitening

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable def mix {k m n : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
    (X : Fin k → Matrix (Fin m) (Fin n) ℂ) (r : Fin k) : Matrix (Fin m) (Fin n) ℂ :=
  ∑ s, B r s • X s

theorem mix_apply {k m n : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
    (X : Fin k → Matrix (Fin m) (Fin n) ℂ) (r : Fin k) (i : Fin m) (j : Fin n) :
    mix B X r i j = ∑ s, B r s * X s i j := by
  simp [mix, Matrix.sum_apply]

def flat {k m n : ℕ} (X : Fin k → Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin k) ℂ := fun p r => X r p.1 p.2

private theorem flat_mix {k m n : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
    (X : Fin k → Matrix (Fin m) (Fin n) ℂ) :
    flat (mix B X) = flat X * B.transpose := by
  ext p r
  simp [flat, mix, Matrix.mul_apply, Matrix.sum_apply, mul_comm]

theorem flat_gram {k m n : ℕ} (X : Fin k → Matrix (Fin m) (Fin n) ℂ) :
    (fun r s => trace ((X r)ᴴ * X s)) = (flat X)ᴴ * flat X := by
  ext r s
  simp only [trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, flat,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem flat_injective {k m n : ℕ} (X : Fin k → Matrix (Fin m) (Fin n) ℂ)
    (hX : LinearIndependent ℂ X) : Function.Injective (flat X).mulVec := by
  intro x y hxy
  apply hX.fintypeLinearCombination_injective
  ext i j
  have h := congrFun hxy (i, j)
  simpa [Fintype.linearCombination_apply, flat, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, mul_comm] using h

private theorem weighted_gram {k : ℕ}
    (M : Fin k → Matrix (Fin 3) (Fin 5) ℂ)
    (N : Fin k → Matrix (Fin 5) (Fin 3) ℂ)
    (hF : (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = 1) :
    (∑ s, ∑ t, ((1 / 3 : ℂ) * trace ((N s)ᴴ * N t)) • ((M s)ᴴ * M t)) = 1 := by
  classical
  let T : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ →ₗ[ℂ]
      Matrix (Fin 5) (Fin 5) ℂ :=
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
  have hT1 : T 1 = (3 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext i j
    simp [T, partialTraceRight, Matrix.one_apply]
  simp only [map_sum] at hT
  change (∑ s, ∑ t, partialTraceRight (kronecker ((M s)ᴴ * M t) ((N s)ᴴ * N t))) = T 1 at hT
  simp only [partialTraceRight_kronecker] at hT
  rw [hT1] at hT
  have h := congrArg (fun A => (1 / 3 : ℂ) • A) hT
  simpa [Finset.smul_sum, smul_smul] using h

private theorem mixed_energy {k : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
    (M : Fin k → Matrix (Fin 3) (Fin 5) ℂ) :
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

private theorem tensor_mix {k : ℕ} (B C : Matrix (Fin k) (Fin k) ℂ)
    (hBC : B.transpose * C = 1)
    (M : Fin k → Matrix (Fin 3) (Fin 5) ℂ)
    (N : Fin k → Matrix (Fin 5) (Fin 3) ℂ) :
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

private theorem exact_whitening {k : ℕ}
    (M : Fin k → Matrix (Fin 3) (Fin 5) ℂ)
    (N : Fin k → Matrix (Fin 5) (Fin 3) ℂ)
    (hN : LinearIndependent ℂ N)
    (hF : (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, IsUnit B ∧
      (fun r s => (1 / 3 : ℂ) * trace ((N r)ᴴ * N s)) = Bᴴ * B ∧
      (let C := B.transpose⁻¹
       let Mprime := mix B M
       let Nprime := mix C N
       (∑ r, kronecker (Mprime r) (Nprime r)) = (∑ r, kronecker (M r) (N r)) ∧
       (∑ r, (Mprime r)ᴴ * Mprime r) = 1 ∧
       (fun r s => (1 / 3 : ℂ) * trace ((Nprime r)ᴴ * Nprime s)) =
         (1 : Matrix (Fin k) (Fin k) ℂ) ∧
       (LinearIndependent ℂ M → LinearIndependent ℂ Mprime)) := by
  classical
  let H : Matrix (Fin k) (Fin k) ℂ :=
    fun r s => (1 / 3 : ℂ) * trace ((N r)ᴴ * N s)
  have hH : H = (1 / 3 : ℝ) • ((flat N)ᴴ * flat N) := by
    rw [← flat_gram]
    ext r s
    simp [H, Complex.real_smul, Matrix.smul_apply, Pi.smul_apply]
  have hpos : H.PosDef := by
    rw [hH]
    exact ((Matrix.PosDef.conjTranspose_mul_self (flat N) (flat_injective N hN)).smul
      (by norm_num : (0 : ℝ) < 1 / 3))
  obtain ⟨B, hB, hBB⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hpos.isStrictlyPositive
  change H = Bᴴ * B at hBB
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hdetT : IsUnit B.transpose.det := by simpa using hdet
  let C := B.transpose⁻¹
  have hBC : B.transpose * C = 1 := Matrix.mul_nonsing_inv _ hdetT
  have hCT : C.transpose = B⁻¹ := by simp [C, ← Matrix.transpose_nonsing_inv]
  refine ⟨B, hB, hBB, tensor_mix B C hBC M N, ?_, ?_, ?_⟩
  · rw [mixed_energy, ← hBB]
    exact weighted_gram M N hF
  · change (fun r s => (1 / 3 : ℂ) * trace ((mix C N r)ᴴ * mix C N s)) =
      (1 : Matrix (Fin k) (Fin k) ℂ)
    have hscale (X : Fin k → Matrix (Fin 5) (Fin 3) ℂ) :
        (fun r s => (1 / 3 : ℂ) * trace ((X r)ᴴ * X s)) =
          (1 / 3 : ℂ) • ((flat X)ᴴ * flat X) := by
      rw [← flat_gram]
      rfl
    rw [hscale, flat_mix, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (flat N)ᴴ, ← Matrix.mul_smul,
      ← Matrix.smul_mul]
    have hH' : (1 / 3 : ℂ) • ((flat N)ᴴ * flat N) = H := by
      rw [← hscale]
    rw [hH', hBB, hCT]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    rw [← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
  · intro hM
    exact hM.sum_smul_of_nondegenerate (Matrix.nondegenerate_of_det_ne_zero hdet.ne_zero)

end D5.S3.Quantum.Algebra.NativeCoefficientWhitening

namespace D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

abbrev MatM (k : ℕ) := Fin k → Matrix (Fin 3) (Fin 5) ℂ
abbrev MatN (k : ℕ) := Fin k → Matrix (Fin 5) (Fin 3) ℂ

/-- The original universal inner-cone flat-spectrum event. -/
def claim : Prop :=
  ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
    b ≤ 2 * a → d ≤ 2 * c →
    ∃ M : Fin 3 → Matrix (Fin a) (Fin b) ℂ,
    ∃ N : Fin 3 → Matrix (Fin d) (Fin c) ℂ,
    ∃ lambda : ℝ, 0 < lambda ∧
      (b * c ≤ a * d →
        (D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.flow M N)ᴴ *
          D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.flow M N =
            (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) ∧
      (a * d ≤ b * c →
        D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.flow M N *
          (D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.flow M N)ᴴ =
            (lambda : ℂ) • (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ))

private theorem matrix_not_injective_of_dimensions
    {m n : ℕ} (h : n < m) (A : Matrix (Fin n) (Fin m) ℂ) :
    ¬ Function.Injective A.mulVecLin := by
  intro hA
  have hd := LinearMap.finrank_le_finrank_of_injective hA
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  omega

private theorem tensor_kernel_vector
    (M : Matrix (Fin 3) (Fin 5) ℂ) (N : Matrix (Fin 5) (Fin 3) ℂ) :
    ∃ z : Fin 5 → ℂ, z ≠ 0 ∧ M *ᵥ z = 0 ∧
      (Matrix.kronecker M N).mulVec
        (Matrix.vec (Matrix.vecMulVec (fun _ : Fin 3 => 1) z)) = 0 := by
  have hnot : ¬ Function.Injective M.mulVecLin :=
    matrix_not_injective_of_dimensions (m := 5) (n := 3) (by omega) M
  obtain ⟨x, y, hxyM, hxy⟩ := Function.not_injective_iff.mp hnot
  let z := x - y
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  have hMz : M *ᵥ z = 0 := by
    dsimp [z]
    change M.mulVecLin (x - y) = 0
    rw [map_sub, hxyM, sub_self]
  refine ⟨z, hz, hMz, ?_⟩
  have hvec := Matrix.kronecker_mulVec_vec N
    (Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ)) z) M
  have hright : Matrix.vecMulVec (fun _ : Fin 3 => 1) z * Mᵀ = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply,
      one_mul]
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hMz j
  have hv0 : Matrix.vec (N * Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ)) z * Mᵀ) = 0 := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_zero]
    simp
  simpa [Matrix.kronecker] using hvec.trans hv0

theorem gram_identity_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : Matrix m n ℂ) (hF : Fᴴ * F = 1) : Function.Injective F.mulVecLin := by
  intro u v huv
  have hzero : F *ᵥ (u - v) = 0 := by
    change F.mulVecLin (u - v) = 0
    rw [map_sub, huv, sub_self]
  have hleft : (Fᴴ * F) *ᵥ (u - v) = 0 := by
    rw [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero]
  rw [hF, Matrix.one_mulVec] at hleft
  exact sub_eq_zero.mp hleft

private theorem k_zero_false
    (M : MatM 0) (N : MatN 0)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1) : False := by
  have h := congrArg (fun A : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ =>
    A (0, 0) (0, 0)) hF
  simpa [Matrix.one_apply] using h

private theorem k_one_false
    (M : MatM 1) (N : MatN 1)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1) : False := by
  let F := Matrix.kronecker (M 0) (N 0)
  have hsum : (∑ r, Matrix.kronecker (M r) (N r)) = F := by
    simp [F]
  have hFinj : Function.Injective F.mulVecLin := by
    apply gram_identity_injective F
    simpa [F, hsum] using hF
  obtain ⟨z, hz, hMz, hker⟩ := tensor_kernel_vector (M 0) (N 0)
  have hvzero : Matrix.vec (Matrix.vecMulVec (fun _ : Fin 3 => 1) z) = 0 := by
    apply hFinj
    simpa [F] using hker
  have hmatzero : Matrix.vecMulVec (fun _ : Fin 3 => 1) z = 0 := by
    exact Matrix.vec_eq_zero_iff.mp hvzero
  have hone : (fun _ : Fin 3 => (1 : ℂ)) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  apply hz
  funext j
  have hj := congrArg (fun A => A 0 j) hmatzero
  simpa [Matrix.vecMulVec_apply] using hj

theorem rank_kronecker_one_general
    {m n : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ)).rank = n * H.rank := by
  classical
  let e : (Fin m × Fin n) ≃ (Σ _ : Fin n, Fin m) :=
    (Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm
  have he : (Matrix.blockDiagonal' (fun _ : Fin n => H)).submatrix e e =
      Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext ⟨r, i⟩ ⟨s, j⟩
    by_cases hij : i = j
    · subst j
      simp [e, Matrix.kronecker, Matrix.kroneckerMap_apply]
    · simp [e, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.blockDiagonal'_apply_ne, hij]
  rw [← he, Matrix.rank_submatrix,
    D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Blocks.rank_block]
  simp

private theorem two_compression_zero
    (S : Matrix (Fin 2 × Fin 3) (Fin 5) ℂ)
    (hinj : Function.Injective S.mulVecLin)
    (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hT : Sᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) * S = 0) :
    T = 0 := by
  have hS : S.rank = 5 := by
    change finrank ℂ (LinearMap.range S.mulVecLin) = 5
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  by_contra hne
  have hTr : 0 < T.rank := by
    rw [Matrix.rank]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    have hentry : ∃ i j, T i j ≠ 0 := by
      by_contra h'
      push_neg at h'
      apply hne
      ext i j
      exact h' i j
    obtain ⟨i, j, hij⟩ := hentry
    refine ⟨⟨T *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩, ?_⟩
    intro hv
    have hv' := congrArg Subtype.val hv
    have hvi := congrFun hv' i
    fin_cases j
    · simp [Matrix.mulVec, dotProduct] at hvi
      apply hij
      change T i 0 = 0
      exact hvi
    · simp [Matrix.mulVec, dotProduct] at hvi
      apply hij
      change T i 1 = 0
      exact hvi
  let Q := Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hQ : Q.rank = 3 * T.rank := rank_kronecker_one_general T
  have hleft := Matrix.rank_mul_ge Sᴴ Q
  have hright := Matrix.rank_mul_ge (Sᴴ * Q) S
  have hz : (Sᴴ * Q * S).rank = 0 := by rw [show Sᴴ * Q * S = 0 from hT]; simp
  simp only [Matrix.rank_conjTranspose, hS, Fintype.card_prod,
    Fintype.card_fin] at hleft hright
  rw [hQ] at hleft
  omega

private def stackK {k : ℕ} (M : MatM k) : Matrix (Fin k × Fin 3) (Fin 5) ℂ :=
  fun p j => M p.1 p.2 j

private theorem stackK_gram {k : ℕ} (M : MatM k) :
    (stackK M)ᴴ * stackK M = ∑ r, (M r)ᴴ * M r := by
  ext i j
  simp only [stackK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]

private theorem block_kernel {k : ℕ}
    (M : MatM k) (N : MatN k)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (l m : Fin 3) :
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
  have h := congrArg (fun A : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ =>
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
  have hMEntry (a b : Fin 5) :
      (∑ r, (M r)ᴴ * M r) a b = (if a = b then 1 else 0) := by
    simpa [Matrix.one_apply] using congrArg
      (fun A : Matrix (Fin 5) (Fin 5) ℂ => A a b) hMGram
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

private theorem stackK_compression_conjTranspose
    (M : MatM 3) (T : Matrix (Fin 3) (Fin 3) ℂ) :
    (stackK M)ᴴ * Matrix.kronecker Tᴴ (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M =
      ((stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
        stackK M)ᴴ := by
  have hk : (Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ =
      Matrix.kronecker Tᴴ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    simpa only [Matrix.kronecker, Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ)
  rw [← hk]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem block_compression
    (M : MatM 3) (N : MatN 3)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1) (l m : Fin 3) :
    let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
      ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
    (stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
      stackK M = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
    ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
  change (stackK M)ᴴ * Matrix.kronecker T
      (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0
  change D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M T = 0
  rw [D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum]
  exact block_kernel M N hF hMGram l m

private theorem stackK_compression_smul_add
    (M : MatM 3) (a b : ℂ) (T U : Matrix (Fin 3) (Fin 3) ℂ) :
    (stackK M)ᴴ * Matrix.kronecker (a • T + b • U)
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M =
      a • ((stackK M)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) +
      b • ((stackK M)ᴴ * Matrix.kronecker U
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) := by
  change D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M (a • T + b • U) =
    a • D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M T +
    b • D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M U
  rw [D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    add_smul, smul_add]

private theorem complex_block_neutral
    (M : MatM 3) (N : MatN 3)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (L : Submodule ℂ (Fin 3 → ℂ))
    (hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      (stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
        stackK M = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0)
    (l m : Fin 3) :
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
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    exact block_compression M N hF hMGram l m
  have hcstar : (stackK M)ᴴ * Matrix.kronecker Tᴴ
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
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
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    rw [hTr_formula]
    have h := stackK_compression_smul_add M ((2 : ℝ)⁻¹ : ℂ) ((2 : ℝ)⁻¹ : ℂ) T Tᴴ
    rw [hc, hcstar] at h
    simpa only [smul_add, smul_zero, zero_add] using h
  have hcTi : (stackK M)ᴴ * Matrix.kronecker Ti
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
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

private def coefficientColumns (N : MatN 3) :
    Matrix (Fin 5) (Fin 3 × Fin 3) ℂ := fun j p => N p.1 j p.2

private theorem coefficient_columns_gram (N : MatN 3) (r s l m : Fin 3) :
    ((coefficientColumns N)ᴴ * coefficientColumns N) (r, l) (s, m) =
      ((N r)ᴴ * N s) l m := by
  simp [coefficientColumns, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem native_three_refutation
    (M : MatM 3) (N : MatN 3) (hM : LinearIndependent ℂ M)
    (hN : LinearIndependent ℂ N) :
    ¬ ((∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1) := by
  intro hF
  obtain ⟨B, hB, hBB, hPres, hMGram, _hNGram, hMprimeLI⟩ :=
    D5.S3.Quantum.Algebra.NativeCoefficientWhitening.exact_whitening M N hN hF
  let M' : MatM 3 := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix B M
  let Ccoeff : Matrix (Fin 3) (Fin 3) ℂ := B.transpose⁻¹
  let N' : MatN 3 := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix Ccoeff N
  have hM'LI : LinearIndependent ℂ M' := by
    simpa [M'] using hMprimeLI hM
  have hM'Gram : ∑ r, (M' r)ᴴ * M' r = 1 := by
    simpa [M'] using hMGram
  have hF' : (∑ r, Matrix.kronecker (M' r) (N' r))ᴴ *
      (∑ r, Matrix.kronecker (M' r) (N' r)) = 1 := by
    simpa only [M', N', Ccoeff, hPres] using hF
  have hstackGram : (stackK M')ᴴ * stackK M' = 1 := by
    rw [stackK_gram]
    exact hM'Gram
  have hstackInj : Function.Injective (stackK M').mulVecLin :=
    gram_identity_injective (stackK M') hstackGram
  obtain ⟨L, hLdim, hL⟩ :=
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.common_plane M' hM'LI hstackInj
  have hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      (stackK M')ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M' = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
    intro T hT hcomp u hu v hv
    have hcomp' : (D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M')ᴴ *
        Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
          D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M' = 0 := by
      have hs : D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M' =
          stackK M' := rfl
      rw [hs]
      exact hcomp
    exact hL T hT hcomp' u hu v hv
  have hneutral := complex_block_neutral M' N' hF' hM'Gram L hplane
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
  have hVplane : ∀ (l m : Fin 3) (a c : Fin 2),
      ∑ r, ∑ s, star (V r a) *
        (((N' r)ᴴ * N' s) l m -
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
  let W : Matrix (Fin 5) (Fin 3 × Fin 3) ℂ := coefficientColumns N'
  let P : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Wᴴ * W
  let C : Matrix (Fin 3 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    Matrix.kronecker V (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hPentry (r s l m : Fin 3) : P (r, l) (s, m) =
      ((N' r)ᴴ * N' s) l m := by
    simpa [P, W] using coefficient_columns_gram N' r s l m
  have hCPC : Cᴴ * P * C = 1 := by
    have hCentry (r i : Fin 3) (a : Fin 2) (l : Fin 3) :
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
        ∑ i : Fin 3, star (if i = l then V r a else 0) *
          ((N' r)ᴴ * N' s) i m * V s c =
          star (V r a) * ((N' r)ᴴ * N' s) l m * V s c := by
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
  have hRank : (Cᴴ * P * C).rank ≤ 5 := by
    calc
      (Cᴴ * P * C).rank ≤ P.rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ ≤ W.rank := Matrix.rank_mul_le_right _ _
      _ ≤ 5 := by simpa using W.rank_le_card_height
  rw [hCPC, Matrix.rank_one] at hRank
  norm_num at hRank

def concatK {k d c : ℕ} (N : Fin k → Matrix (Fin d) (Fin c) ℂ) :
    Matrix (Fin d) (Fin k × Fin c) ℂ := fun i p => N p.1 i p.2

theorem concatK_gram {k d c : ℕ}
    (N : Fin k → Matrix (Fin d) (Fin c) ℂ)
    (H : Matrix (Fin k) (Fin k) ℂ)
    (hN : ∀ r s, (N r)ᴴ * N s = H r s • 1) :
    (concatK N)ᴴ * concatK N = Matrix.kronecker H (1 : Matrix (Fin c) (Fin c) ℂ) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  have h := congrArg (fun A : Matrix (Fin c) (Fin c) ℂ => A i j) (hN r s)
  simpa [concatK, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul] using h

private theorem exact_k2_native_refutation
    (M : Fin 2 → Matrix (Fin 3) (Fin 5) ℂ)
    (N : Fin 2 → Matrix (Fin 5) (Fin 3) ℂ)
    (hM : LinearIndependent ℂ M)
    (hN : LinearIndependent ℂ N) :
    (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
        (∑ r, Matrix.kronecker (M r) (N r)) ≠
      (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ) := by
  intro hF
  obtain ⟨B, hB, hBB, hPres, hMGram, _hNGram, _hMprimeLI⟩ :=
    D5.S3.Quantum.Algebra.NativeCoefficientWhitening.exact_whitening M N hN hF
  let M' : Fin 2 → Matrix (Fin 3) (Fin 5) ℂ :=
    D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix B M
  let C : Matrix (Fin 2) (Fin 2) ℂ := B.transpose⁻¹
  let N' : Fin 2 → Matrix (Fin 5) (Fin 3) ℂ :=
    D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix C N
  have hF' :
      (∑ r, Matrix.kronecker (M' r) (N' r))ᴴ *
          (∑ r, Matrix.kronecker (M' r) (N' r)) =
        (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ) := by
    have hF0 := hF
    rw [← hPres] at hF0
    simpa [M', C, N'] using hF0
  have hMGram' : ∑ r, (M' r)ᴴ * M' r = 1 := by
    simpa [M'] using hMGram
  let S : Matrix (Fin 2 × Fin 3) (Fin 5) ℂ := stackK M'
  have hSGram : Sᴴ * S = (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
    rw [show Sᴴ * S = ∑ r, (M' r)ᴴ * M' r by
      simpa [S] using stackK_gram M']
    exact hMGram'
  have hSinj : Function.Injective S.mulVecLin :=
    gram_identity_injective S hSGram
  let T : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
    fun l m r s =>
      ((N' r)ᴴ * N' s) l m -
        (if r = s then if l = m then 1 else 0 else 0)
  have hTzero (l m : Fin 3) : T l m = 0 := by
    apply two_compression_zero S hSinj (T l m)
    have hbk := block_kernel M' N' hF' hMGram' l m
    have hcomp :
        Sᴴ * Matrix.kronecker (T l m)
            (1 : Matrix (Fin 3) (Fin 3) ℂ) * S =
          ∑ r, ∑ s, (T l m r s) • ((M' r)ᴴ * M' s) := by
      ext u v
      simp only [S, stackK, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        Fintype.sum_prod_type]
      simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_lhs =>
        arg 2
        ext s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hcomp]
    exact hbk
  have hNcross (r s : Fin 2) :
      (N' r)ᴴ * N' s =
        (if r = s then (1 : ℂ) else 0) •
          (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext l m
    have ht := congrArg (fun X => X r s) (hTzero l m)
    have ht' :
        ((N' r)ᴴ * N' s) l m -
            (if r = s then if l = m then 1 else 0 else 0) = 0 := by
      simpa [T] using ht
    have he := sub_eq_zero.mp ht'
    by_cases hrs : r = s <;> by_cases hlm : l = m <;>
      simpa [hrs, hlm, Matrix.one_apply] using he
  have hconcat :
      (concatK N')ᴴ * concatK N' =
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
          (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
    concatK_gram N' 1 hNcross
  have hkronecker :
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
          (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) := by
    ext ⟨r, l⟩ ⟨s, m⟩
    by_cases hrs : r = s <;> by_cases hlm : l = m <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hrs, hlm]
  have hrank6 : 6 ≤ (concatK N').rank := by
    have hEq :
        ((concatK N')ᴴ * concatK N').rank = 6 := by
      rw [hconcat, hkronecker, Matrix.rank_one]
      simp
    calc
      6 = ((concatK N')ᴴ * concatK N').rank := hEq.symm
      _ ≤ (concatK N').rank := Matrix.rank_mul_le_right _ _
  have hrank5 : (concatK N').rank ≤ 5 := by
    simpa using (concatK N').rank_le_card_height
  omega

private abbrev Left := Matrix (Fin 3) (Fin 5) ℂ
private abbrev Right := Matrix (Fin 5) (Fin 3) ℂ
private abbrev Native := Matrix (Fin 3 × Fin 5) (Fin 5 × Fin 3) ℂ

private theorem reduce_left {n : ℕ}
    (A : Fin (n + 1) → Left) (D : Fin (n + 1) → Right)
    (g : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (hg : g i ≠ 0) (hrel : (∑ j, g j • A j) = 0) :
    ∃ A' : Fin n → Left, ∃ D' : Fin n → Right,
      (∑ j, Matrix.kronecker (A' j) (D' j)) =
        (∑ j, Matrix.kronecker (A j) (D j)) := by
  classical
  let A' : Fin n → Left := fun j => A (i.succAbove j)
  let D' : Fin n → Right := fun j =>
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

private theorem reduce_right {n : ℕ}
    (A : Fin (n + 1) → Left) (D : Fin (n + 1) → Right)
    (g : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (hg : g i ≠ 0) (hrel : (∑ j, g j • D j) = 0) :
    ∃ A' : Fin n → Left, ∃ D' : Fin n → Right,
      (∑ j, Matrix.kronecker (A' j) (D' j)) =
        (∑ j, Matrix.kronecker (A j) (D j)) := by
  classical
  let A' : Fin n → Left := fun j =>
    A (i.succAbove j) - (g (i.succAbove j) / g i) • A i
  let D' : Fin n → Right := fun j => D (i.succAbove j)
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

private theorem minimal_decomposition (M : Fin 3 → Left) (N : Fin 3 → Right) :
    ∃ k : ℕ, k ≤ 3 ∧ ∃ A : Fin k → Left, ∃ D : Fin k → Right,
      LinearIndependent ℂ A ∧ LinearIndependent ℂ D ∧
        (∑ j, Matrix.kronecker (A j) (D j)) =
          (∑ r, Matrix.kronecker (M r) (N r)) := by
  classical
  let p : ℕ → Prop := fun k => ∃ A : Fin k → Left, ∃ D : Fin k → Right,
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

private theorem normalized_minimal_decomposition
    (M : Fin 3 → Left) (N : Fin 3 → Right) (lambda : ℝ) (hlambda : 0 < lambda)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
        (∑ r, Matrix.kronecker (M r) (N r)) =
      (lambda : ℂ) • (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ)) :
    ∃ k : ℕ, k ≤ 3 ∧ ∃ A : Fin k → Left, ∃ D : Fin k → Right,
      LinearIndependent ℂ A ∧ LinearIndependent ℂ D ∧
        (∑ j, Matrix.kronecker (A j) (D j)) =
          (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) •
            (∑ r, Matrix.kronecker (M r) (N r)) ∧
        (∑ j, Matrix.kronecker (A j) (D j))ᴴ *
            (∑ j, Matrix.kronecker (A j) (D j)) =
          (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ) := by
  classical
  obtain ⟨k, hk, A, D, hA, hD, hsum⟩ := minimal_decomposition M N
  let c : ℂ := (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ)
  have hsqrt : (Real.sqrt lambda) ^ 2 = lambda := by
    simpa [pow_two] using (Real.sq_sqrt (le_of_lt hlambda))
  have hsqrt_ne : Real.sqrt lambda ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlambda)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (inv_ne_zero hsqrt_ne)
  let A' : Fin k → Left := fun j => c • A j
  have hA' : LinearIndependent ℂ A' := by
    exact hA.units_smul (fun _ => Units.mk0 c hc)
  have hsum' : (∑ j, Matrix.kronecker (A' j) (D j)) = c •
      (∑ r, Matrix.kronecker (M r) (N r)) := by
    change (∑ j, (Matrix.kroneckerBilinear (R := ℂ)) (c • A j) (D j)) = _
    simp only [map_smul, LinearMap.smul_apply, ← Finset.smul_sum]
    exact congrArg (fun X : Native => c • X) hsum
  have hcc : (star c) * c * (lambda : ℂ) = 1 := by
    have hreal : (Real.sqrt lambda)⁻¹ * (Real.sqrt lambda)⁻¹ * lambda = 1 := by
      field_simp [hsqrt_ne]
      nlinarith [hsqrt]
    dsimp [c]
    simpa [Complex.star_def] using congrArg (fun x : ℝ => (x : ℂ)) hreal
  have hgram : (∑ j, Matrix.kronecker (A' j) (D j))ᴴ *
      (∑ j, Matrix.kronecker (A' j) (D j)) =
      (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ) := by
    rw [hsum']
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hF]
    have hscalar : c * (star c * (lambda : ℂ)) = 1 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcc
    rw [hscalar]
    simp
  exact ⟨k, hk, A', D, hA', hD, hsum', hgram⟩

/-- Arbitrary native triples cannot have any positive scalar column Gram. -/
theorem positive_scalar_obstruction (M : MatM 3) (N : MatN 3)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ ((∑ r, Matrix.kronecker (M r) (N r))ᴴ *
        (∑ r, Matrix.kronecker (M r) (N r)) =
      (lambda : ℂ) • (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ)) := by
  intro hF
  obtain ⟨k, hk, A, D, hA, hD, _hsum, hgram⟩ :=
    normalized_minimal_decomposition M N lambda hlambda hF
  interval_cases k
  · exact k_zero_false A D hgram
  · exact k_one_false A D hgram
  · exact exact_k2_native_refutation A D hA hD hgram
  · exact native_three_refutation A D hA hD hgram

/-- Literal negation of the complete original universal event. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨M, N, lambda, hlambda, hcol, _hrow⟩ :=
    h 3 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply positive_scalar_obstruction M N lambda hlambda
  exact hcol (by norm_num)

end D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

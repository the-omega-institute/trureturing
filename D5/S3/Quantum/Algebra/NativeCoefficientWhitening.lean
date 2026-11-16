/- GID: D5/S3/Quantum/Algebra/NativeCoefficientWhitening
   generality: G
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: Exact finite coefficient whitening application. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

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

theorem flat_mix {k m n : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
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

theorem weighted_gram {k : ℕ}
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

theorem mixed_energy {k : ℕ} (B : Matrix (Fin k) (Fin k) ℂ)
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

theorem tensor_mix {k : ℕ} (B C : Matrix (Fin k) (Fin k) ℂ)
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

theorem exact_whitening {k : ℕ}
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

example (M : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (N : Fin 3 → Matrix (Fin 5) (Fin 3) ℂ) :
    (∑ r, kronecker (M r) (N r)) =
      D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.flow M N := rfl

end D5.S3.Quantum.Algebra.NativeCoefficientWhitening

/- GID: D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GHZMeasureBiseparableBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The GHZ measure has sharp bound one half on arbitrary A|BC product density states. -/

/-
proof_shape: result: bind-only
escape_witness: none
The local auxiliary facts instantiate frozen variance and Mathlib tensor laws,
  unfold the displayed definitions and normalize; no helper theorem is retained.
admission_basis: open-problem-resolution (#12719; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Information/ActualPureQubitGeometry; module statement_id sha256:ee8e9959e66d6cb0b6f5314fffb04cb8a702ffba160bdac63f03a705e0523b83
    D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix: sha256:ee496966fe099c646fb0f51761f3b1e446ac73f2e7b579da5586731706e8c52d
  D5/S3/Quantum/FiniteDimensional; module statement_id sha256:8448b6959a48d5c232600cbaa512d3eae6aadd57de71f1e30aad67fde1d1b63d
    D5/S3/Quantum/FiniteDimensional.qubitX: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
    D5/S3/Quantum/FiniteDimensional.qubitZ: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
    D5/S3/Quantum/FiniteDimensional.QubitMatrix: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
  D5/S3/Quantum/Information/CovarianceSumBound; module statement_id sha256:764b4acecf70a4ec02895cc386fdc0627662f58d9db718aef3dff79b99818f44
    D5/S3/Quantum/Information/CovarianceSumBound.variance_nonneg: sha256:b87817c872ae9a6650f2ca6fa6033b3ede876d399b80637cbf18d745a7abf2b3
    D5/S3/Quantum/Information/CovarianceSumBound.variance: sha256:cbfb32d0ddbfaade47e6a8c978fffc35324a71894dafc5a1b79510d6efcfd37c
  D5/S3/Observer/StateNotPath; module statement_id sha256:f740976b95674a875586cc6265d74412c9e48c1341daacb056bb3eacc9ea6389
    D5/S3/Observer/StateNotPath.basisZeroDensity: sha256:e18c38524fd57930c36be354fe1b20cec6d9caa33855120180ba03f61c045513
  D5/S3/QuantumBounds/CHSHWitness; module statement_id sha256:0b256a55db0859d4a6703ba970f7ff6eefd46196b707e4e28e0bdf62e7529e5f
    D5/S3/QuantumBounds/CHSHWitness.bellDensity: sha256:e912835dc9088a23076f5ad7c742dd494605dd2e25b7beb587d4750a4f1efa84
    D5/S3/QuantumBounds/CHSHWitness.bellVector: sha256:ef8ab2c76767d0b6e0ead3d2869923996cafda705f450300e01195f336eadb8f
    D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state: sha256:f25b7239e34182d1cdaff8dfc1f1b67e43f85b40bdfbe3e850173bf7593427d5
    D5/S3/QuantumBounds/CHSHWitness.TwoQubitMatrix: sha256:2a939b5c081cb7f5071bf116c5a5967adc0c05361ef9b701465cb9cb84dc1c22
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition; module statement_id sha256:445d28204f4c839e9d5711f568c7f8a3259e36bcff54986168a827333cbdbb5d
    D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  D5/S3/Quantum/QubitWitnesses; module statement_id sha256:6ffbe3f05bf1773318869947f3016fda7edbe5a99e6b91bfd6f9236efa6db474
    D5/S3/Quantum/QubitWitnesses.bellCoefficients: sha256:e2b60dfaa8cf4c9859738273f0e38c061b7898ed8aba82a4f813fd80d5eb5fe8
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Information.CovarianceSumBound
import D5.S3.Observer.StateNotPath
import D5.S3.QuantumBounds.CHSHWitness


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Matrix
open scoped Kronecker ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
open D5.S3.Quantum.FiniteDimensional
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.Observer.StateNotPath
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)

def IsDensity {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ trace ρ = 1

def expect {n : Type*} [Fintype n] [DecidableEq n] (ρ A : Matrix n n ℂ) : ℝ :=
  (trace (A * ρ)).re

def observable (a b c : (Fin 3 → ℝ)) : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ := (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) ⊗ₖ ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c i))))
def E (ρ : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) (a b c : (Fin 3 → ℝ)) : ℝ := expect ρ (observable a b c)
def Istar (ρ : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) (a₁ a₂ b₁ b₂ c₁ c₂ : (Fin 3 → ℝ)) : ℝ :=
  E ρ a₁ b₁ c₁ - E ρ a₁ b₂ c₂ * E ρ a₂ b₁ c₂ * E ρ a₂ b₂ c₁

def values (ρ : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) : Set ℝ :=
  {v | ∃ a₁ a₂ b₁ b₂ c₁ c₂, Orthonormal ℝ (![WithLp.toLp 2 a₁, WithLp.toLp 2 a₂] : Fin 2 → EuclideanSpace ℝ (Fin 3)) ∧ Orthonormal ℝ (![WithLp.toLp 2 b₁, WithLp.toLp 2 b₂] : Fin 2 → EuclideanSpace ℝ (Fin 3)) ∧ Orthonormal ℝ (![WithLp.toLp 2 c₁, WithLp.toLp 2 c₂] : Fin 2 → EuclideanSpace ℝ (Fin 3)) ∧
    v = |Istar ρ a₁ a₂ b₁ b₂ c₁ c₂|}
def EGHZ (ρ : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) : ℝ := (1 / 2) * sSup (values ρ)

def claim : Prop :=
  (∀ (ρA : QubitMatrix) (ρBC : TwoQubitMatrix), IsDensity ρA → IsDensity ρBC →
    EGHZ (ρA ⊗ₖ ρBC) ≤ 1 / 2) ∧
  (∃ (ρA : QubitMatrix) (ρBC : TwoQubitMatrix), IsDensity ρA ∧ IsDensity ρBC ∧
    EGHZ (ρA ⊗ₖ ρBC) = 1 / 2)


/-- The exact A|BC constant in Wu–Zhong–Wu, Eq. (37). -/
theorem result : claim := by
  have spin_hermitian (a : (Fin 3 → ℝ)) : ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i)))).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochMatrix] <;> ring

  have spin_anticommutator (a b : (Fin 3 → ℝ)) :
      (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) * (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b i))) + (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b i))) * (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) = (2 * dotProduct a b : ℂ) • (1 : QubitMatrix) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [blochMatrix, dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring

  have spin_square (a : (Fin 3 → ℝ)) (ha : dotProduct a a = 1) :
      (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) * (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) = 1 := by
    have h := spin_anticommutator a a
    rw [ha] at h
    ext i j
    have hi := congrArg (fun M : QubitMatrix => M i j) h
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hi
    norm_num at hi
    linear_combination (1 / 2 : ℂ) * hi

  have exp_add {n : Type} [Fintype n] [DecidableEq n] (ρ A B : Matrix n n ℂ) :
      expect ρ (A + B) = expect ρ A + expect ρ B := by simp [expect, add_mul]
  have exp_smul {n : Type} [Fintype n] [DecidableEq n]
      (ρ A : Matrix n n ℂ) (t : ℝ) : expect ρ (t • A) = t * expect ρ A := by
    simp [expect, Complex.real_smul, Complex.mul_re]
  have exp_one {n : Type} [Fintype n] [DecidableEq n]
      (ρ : Matrix n n ℂ) (hρ : IsDensity ρ) : expect ρ 1 = 1 := by simp [expect, hρ.2]

  have variance_nonneg {n : Type} [Fintype n] [DecidableEq n]
      (ρ A : Matrix n n ℂ) (hρ : IsDensity ρ) (hA : A.IsHermitian) :
      (expect ρ A)^2 ≤ expect ρ (A * A) := by
    let state : D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState n :=
      ⟨CStarMatrix.ofMatrix ρ, ⟨map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hρ.1.nonneg, hρ.2⟩⟩
    have h := D5.S3.Quantum.Information.CovarianceSumBound.variance_nonneg state hA
    change 0 ≤ (trace (ρ * (A*A))).re - (trace (ρ*A)).re^2 at h
    rw [trace_mul_comm ρ (A*A), trace_mul_comm ρ A] at h
    exact sub_nonneg.mp h

  have anticomm_bound {n : Type} [Fintype n] [DecidableEq n]
      (ρ A B : Matrix n n ℂ) (hρ : IsDensity ρ) (hA : A.IsHermitian) (hB : B.IsHermitian)
      (hAA : A * A = 1) (hBB : B * B = 1) (hAB : A * B + B * A = 0) :
      (expect ρ A)^2 + (expect ρ B)^2 ≤ 1 := by
    let u := expect ρ A
    let v := expect ρ B
    let H := u • A + v • B
    have hH : H.IsHermitian :=
      (hA.smul (by simp [IsSelfAdjoint])).add (hB.smul (by simp [IsSelfAdjoint]))
    have hsq : H * H = (u^2 + v^2) • (1 : Matrix n n ℂ) := by
      calc
        H * H = (u*u) • (A*A) + (u*v) • (A*B+B*A) + (v*v) • (B*B) := by
          dsimp [H]
          simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
          module
        _ = (u^2 + v^2) • (1 : Matrix n n ℂ) := by
          rw [hAA, hBB, hAB, smul_zero, add_zero, ← add_smul]
          congr 1
          ring
    have ht := variance_nonneg ρ H hρ hH
    rw [hsq, exp_smul, exp_one ρ hρ] at ht
    have he : expect ρ H = u^2 + v^2 := by simp [H, exp_add, exp_smul, u, v, pow_two]
    rw [he] at ht
    dsimp [u, v] at ht
    nlinarith [sq_nonneg (expect ρ A), sq_nonneg (expect ρ B)]

  have exp_abs_le_one {n : Type} [Fintype n] [DecidableEq n]
      (ρ A : Matrix n n ℂ) (hρ : IsDensity ρ) (hA : A.IsHermitian) (hAA : A*A=1) :
      |expect ρ A| ≤ 1 := by
    have h := variance_nonneg ρ A hρ hA
    rw [hAA, exp_one ρ hρ] at h
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

  have tensor_hermitian {m n : Type} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
      (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
    change (A ⊗ₖ B)ᴴ = A ⊗ₖ B
    rw [conjTranspose_kronecker, hA, hB]

  have tensor_square {m n : Type} [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
      (hA : A*A=1) (hB : B*B=1) : (A ⊗ₖ B)*(A ⊗ₖ B)=1 := by
    rw [← mul_kronecker_mul, hA, hB, one_kronecker_one]

  have E_factor (ρA : QubitMatrix) (ρBC : TwoQubitMatrix) (hρA : IsDensity ρA)
      (a b c : (Fin 3 → ℝ)) :
      E (ρA ⊗ₖ ρBC) a b c = expect ρA ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i)))) * expect ρBC ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c i)))) := by
    have him : (trace ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) * ρA)).im = 0 := by
      have h := trace_conjTranspose ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) * ρA)
      rw [conjTranspose_mul, hρA.1.1.eq, (spin_hermitian a).eq, trace_mul_comm] at h
      have hi := congrArg Complex.im h
      simp only [Complex.star_def, Complex.conj_im] at hi
      linarith
    simp only [E, observable, expect, ← mul_kronecker_mul, trace_kronecker,
      Complex.mul_re, him, zero_mul, sub_zero]

  have product_correlations (ρA : QubitMatrix) (ρBC : TwoQubitMatrix)
      (hρA : IsDensity ρA) (hρBC : IsDensity ρBC)
      (a₁ a₂ b₁ b₂ c₁ c₂ : (Fin 3 → ℝ))
      (ha : Orthonormal ℝ (![WithLp.toLp 2 a₁, WithLp.toLp 2 a₂] : Fin 2 → EuclideanSpace ℝ (Fin 3))) (hb : Orthonormal ℝ (![WithLp.toLp 2 b₁, WithLp.toLp 2 b₂] : Fin 2 → EuclideanSpace ℝ (Fin 3))) (hc : Orthonormal ℝ (![WithLp.toLp 2 c₁, WithLp.toLp 2 c₂] : Fin 2 → EuclideanSpace ℝ (Fin 3))) :
      (expect ρA ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a₁ i)))))^2 + (expect ρA ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a₂ i)))))^2 ≤ 1 ∧
      (expect ρBC ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i)))))^2 + (expect ρBC ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₂ i)))))^2 ≤ 1 ∧
      (expect ρBC ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i)))))^2 + (expect ρBC ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₂ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i)))))^2 ≤ 1 ∧
      |expect ρBC ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₂ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₂ i))))| ≤ 1 := by
    have ha : dotProduct a₁ a₁ = 1 ∧ dotProduct a₂ a₂ = 1 ∧ dotProduct a₁ a₂ = 0 := by
      have h00 := orthonormal_iff_ite.mp ha 0 0
      have h11 := orthonormal_iff_ite.mp ha 1 1
      have h10 := orthonormal_iff_ite.mp ha 1 0
      change dotProduct a₁ a₁ = (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) at h00
      change dotProduct a₂ a₂ = (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) at h11
      change dotProduct a₁ a₂ = (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) at h10
      exact ⟨by simpa only [if_pos rfl, if_true] using h00,
        by simpa only [if_pos rfl, if_true] using h11, by simpa using h10⟩
    have hb : dotProduct b₁ b₁ = 1 ∧ dotProduct b₂ b₂ = 1 ∧ dotProduct b₁ b₂ = 0 := by
      have h00 := orthonormal_iff_ite.mp hb 0 0
      have h11 := orthonormal_iff_ite.mp hb 1 1
      have h10 := orthonormal_iff_ite.mp hb 1 0
      change dotProduct b₁ b₁ = (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) at h00
      change dotProduct b₂ b₂ = (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) at h11
      change dotProduct b₁ b₂ = (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) at h10
      exact ⟨by simpa only [if_pos rfl, if_true] using h00,
        by simpa only [if_pos rfl, if_true] using h11, by simpa using h10⟩
    have hc : dotProduct c₁ c₁ = 1 ∧ dotProduct c₂ c₂ = 1 ∧ dotProduct c₁ c₂ = 0 := by
      have h00 := orthonormal_iff_ite.mp hc 0 0
      have h11 := orthonormal_iff_ite.mp hc 1 1
      have h10 := orthonormal_iff_ite.mp hc 1 0
      change dotProduct c₁ c₁ = (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) at h00
      change dotProduct c₂ c₂ = (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) at h11
      change dotProduct c₁ c₂ = (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) at h10
      exact ⟨by simpa only [if_pos rfl, if_true] using h00,
        by simpa only [if_pos rfl, if_true] using h11, by simpa using h10⟩
    have hanti {a b : (Fin 3 → ℝ)} (h : dotProduct a b = 0) : (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) * (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b i))) + (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b i))) * (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * a i))) = 0 := by
      rw [spin_anticommutator, h]
      simp
    have hrow : ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i))))*((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₂ i)))) +
        ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₂ i))))*((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i)))) = 0 := by
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, spin_square b₁ hb.1,
        ← kronecker_add, hanti hc.2.2, kronecker_zero]
    have hcol : ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i))))*((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₂ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i)))) +
        ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₂ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i))))*((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * b₁ i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * c₁ i)))) = 0 := by
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, spin_square c₁ hc.1,
        ← add_kronecker, hanti hb.2.2, zero_kronecker]
    refine ⟨anticomm_bound ρA _ _ hρA (spin_hermitian _) (spin_hermitian _)
      (spin_square _ ha.1) (spin_square _ ha.2.1) (hanti ha.2.2), ?_, ?_, ?_⟩
    · exact anticomm_bound ρBC _ _ hρBC
        (tensor_hermitian (spin_hermitian _) (spin_hermitian _))
        (tensor_hermitian (spin_hermitian _) (spin_hermitian _))
        (tensor_square (spin_square _ hb.1) (spin_square _ hc.1))
        (tensor_square (spin_square _ hb.1) (spin_square _ hc.2.1)) hrow
    · exact anticomm_bound ρBC _ _ hρBC
        (tensor_hermitian (spin_hermitian _) (spin_hermitian _))
        (tensor_hermitian (spin_hermitian _) (spin_hermitian _))
        (tensor_square (spin_square _ hb.1) (spin_square _ hc.1))
        (tensor_square (spin_square _ hb.2.1) (spin_square _ hc.1)) hcol
    · exact exp_abs_le_one ρBC _ hρBC
        (tensor_hermitian (spin_hermitian _) (spin_hermitian _))
        (tensor_square (spin_square _ hb.2.1) (spin_square _ hc.2.1))

  have scalar_bound (u v x y z w : ℝ)
      (hu : u^2+v^2≤1) (hy : x^2+y^2≤1) (hz : x^2+z^2≤1) (hw : |w| ≤1) :
      |u*x-u*v^2*w*y*z| ≤1 := by
    let q := |u|
    let X := |x|
    let c := 1-q^2
    have hq0 : 0≤q := abs_nonneg _
    have hX0 : 0≤X := abs_nonneg _
    have hq2 : q^2+v^2≤1 := by simpa [q] using hu
    have hX2 : X^2≤1 := by dsimp [X]; rw [sq_abs]; nlinarith [sq_nonneg y]
    have hq1 : q≤1 := by nlinarith [sq_nonneg v]
    have hX1 : X≤1 := by nlinarith
    have hc0 : 0≤c := by dsimp [c]; nlinarith [sq_nonneg v]
    have hc1 : c≤1 := by dsimp [c]; nlinarith [sq_nonneg q]
    have hv : v^2≤c := by dsimp [c]; linarith
    have hYZ : |y| *|z| ≤1-X^2 := by
      have hys : |y| ^2=y^2 := sq_abs _
      have hzs : |z| ^2=z^2 := sq_abs _
      have hxs : X^2=x^2 := sq_abs _
      nlinarith [sq_nonneg (|y| -|z|)]
    have hrest : |w| *(|y| *|z|)≤1-X^2 :=
      (mul_le_mul_of_nonneg_right hw (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using hYZ)
    have hbound : |u*x-u*v^2*w*y*z| ≤q*(X+c*(1-X^2)) := by
      calc
        _ ≤ q*X+q*v^2*|w| *|y| *|z| := by
          have h := abs_sub (u*x) (u*v^2*w*y*z)
          have he : |u*v^2*w*y*z| = |u| *v^2*|w| *|y| *|z| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg v)]
          rw [he, abs_mul] at h
          exact h
        _ = q*X+(q*v^2)*(|w| *(|y| *|z|)) := by ring
        _ ≤ q*X+(q*v^2)*(1-X^2) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrest (mul_nonneg hq0 (sq_nonneg v)))
        _ ≤ q*X+(q*c)*(1-X^2) := by
          apply add_le_add (le_refl _)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hq0) (by linarith)
        _ = q*(X+c*(1-X^2)) := by ring
    apply hbound.trans
    by_cases hcase : c≤1/2
    · have hterm := mul_le_mul_of_nonneg_right hcase (show 0≤1-X^2 by linarith)
      have hbracket : X+c*(1-X^2)≤1 := by nlinarith [sq_nonneg (X-1)]
      exact (mul_le_mul_of_nonneg_left hbracket hq0).trans (by simpa using hq1)
    · have hq : q≤3/4 := by dsimp [c] at hcase; nlinarith
      have hterm := mul_le_mul_of_nonneg_right hc1 (show 0≤1-X^2 by linarith)
      have hbracket : X+c*(1-X^2)≤5/4 := by nlinarith [sq_nonneg (X-1/2)]
      have h := mul_le_mul_of_nonneg_left hbracket hq0
      nlinarith

  have product_Istar_bound (ρA : QubitMatrix) (ρBC : TwoQubitMatrix)
      (hρA : IsDensity ρA) (hρBC : IsDensity ρBC)
      (a₁ a₂ b₁ b₂ c₁ c₂ : (Fin 3 → ℝ))
      (ha : Orthonormal ℝ (![WithLp.toLp 2 a₁, WithLp.toLp 2 a₂] : Fin 2 → EuclideanSpace ℝ (Fin 3))) (hb : Orthonormal ℝ (![WithLp.toLp 2 b₁, WithLp.toLp 2 b₂] : Fin 2 → EuclideanSpace ℝ (Fin 3))) (hc : Orthonormal ℝ (![WithLp.toLp 2 c₁, WithLp.toLp 2 c₂] : Fin 2 → EuclideanSpace ℝ (Fin 3))) :
      |Istar (ρA ⊗ₖ ρBC) a₁ a₂ b₁ b₂ c₁ c₂| ≤ 1 := by
    obtain ⟨hu,hy,hz,hw⟩ := product_correlations ρA ρBC hρA hρBC a₁ a₂ b₁ b₂ c₁ c₂ ha hb hc
    simp only [Istar, E_factor _ _ hρA]
    convert scalar_bound _ _ _ _ _ _ hu hy hz hw using 1
    congr 1
    ring

  let xAxis : (Fin 3 → ℝ) := fun i => if i.val=0 then 1 else 0
  let zAxis : (Fin 3 → ℝ) := fun i => if i.val=2 then 1 else 0

  have axis_spin : (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * xAxis i))) = qubitX ∧ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * zAxis i))) = qubitZ := by
    have hx0 : xAxis 0 = 1 := rfl
    have hx1 : xAxis 1 = 0 := rfl
    have hx2 : xAxis 2 = 0 := rfl
    have hz0 : zAxis 0 = 0 := rfl
    have hz1 : zAxis 1 = 0 := rfl
    have hz2 : zAxis 2 = 1 := rfl
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [blochMatrix, hx0, hx1, hx2, hz0, hz1, hz2, qubitX, qubitZ]

  have axes_ortho : Orthonormal ℝ (![WithLp.toLp 2 xAxis, WithLp.toLp 2 zAxis] : Fin 2 → EuclideanSpace ℝ (Fin 3)) ∧ Orthonormal ℝ (![WithLp.toLp 2 zAxis, WithLp.toLp 2 xAxis] : Fin 2 → EuclideanSpace ℝ (Fin 3)) := by
    have hxx : dotProduct xAxis xAxis = 1 := by
      unfold dotProduct
      rw [Fin.sum_univ_three]
      change (1*1+0*0+0*0 : ℝ) = 1
      norm_num
    have hzz : dotProduct zAxis zAxis = 1 := by
      unfold dotProduct
      rw [Fin.sum_univ_three]
      change (0*0+0*0+1*1 : ℝ) = 1
      norm_num
    have hxz : dotProduct xAxis zAxis = 0 := by
      unfold dotProduct
      rw [Fin.sum_univ_three]
      change (1*0+0*0+0*1 : ℝ) = 0
      norm_num
    have hzx : dotProduct zAxis xAxis = 0 := by
      unfold dotProduct
      rw [Fin.sum_univ_three]
      change (0*1+0*0+1*0 : ℝ) = 0
      norm_num
    constructor
    · apply orthonormal_iff_ite.mpr
      intro i j
      fin_cases i <;> fin_cases j
      · change dotProduct xAxis xAxis = 1
        exact hxx
      · change dotProduct zAxis xAxis = 0
        exact hzx
      · change dotProduct xAxis zAxis = 0
        exact hxz
      · change dotProduct zAxis zAxis = 1
        exact hzz
    · apply orthonormal_iff_ite.mpr
      intro i j
      fin_cases i <;> fin_cases j
      · change dotProduct zAxis zAxis = 1
        exact hzz
      · change dotProduct xAxis zAxis = 0
        exact hxz
      · change dotProduct zAxis xAxis = 0
        exact hzx
      · change dotProduct xAxis xAxis = 1
        exact hxx

  have values_nonempty (ρ : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) : (values ρ).Nonempty := by
    refine ⟨|Istar ρ zAxis xAxis xAxis zAxis xAxis zAxis|, ?_⟩
    exact ⟨zAxis, xAxis, xAxis, zAxis, xAxis, zAxis,
      axes_ortho.2, axes_ortho.1, axes_ortho.1, rfl⟩

  have product_values_bounded (ρA : QubitMatrix) (ρBC : TwoQubitMatrix)
      (hρA : IsDensity ρA) (hρBC : IsDensity ρBC) : BddAbove (values (ρA ⊗ₖ ρBC)) := by
    refine ⟨1, ?_⟩
    rintro v ⟨a₁,a₂,b₁,b₂,c₁,c₂,ha,hb,hc,rfl⟩
    exact product_Istar_bound ρA ρBC hρA hρBC _ _ _ _ _ _ ha hb hc

  have product_upper_bound (ρA : QubitMatrix) (ρBC : TwoQubitMatrix)
      (hρA : IsDensity ρA) (hρBC : IsDensity ρBC) : EGHZ (ρA ⊗ₖ ρBC)≤1/2 := by
    have hs : sSup (values (ρA ⊗ₖ ρBC))≤1 := by
      apply csSup_le (values_nonempty _)
      rintro v ⟨a₁,a₂,b₁,b₂,c₁,c₂,ha,hb,hc,rfl⟩
      exact product_Istar_bound ρA ρBC hρA hρBC _ _ _ _ _ _ ha hb hc
    dsimp [EGHZ]
    linarith


  let rhoZero : QubitMatrix := basisZeroDensity
  let rhoBell : TwoQubitMatrix := bellDensity

  have rhoZero_density : IsDensity rhoZero := by
    constructor
    · have he : rhoZero = diagonal (![1,0] : Fin 2 → ℂ) := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      rw [he]
      rw [posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> norm_num
    · change trace basisZeroDensity = 1
      rw [trace, Fin.sum_univ_two]
      change (1 + 0 : ℂ) = 1
      exact add_zero 1

  have rhoBell_density : IsDensity rhoBell := bell_density_is_state

  have rhoZero_values : expect rhoZero ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * zAxis i))))=1 ∧ expect rhoZero ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * xAxis i))))=0 := by
    rw [axis_spin.1, axis_spin.2]
    constructor <;> norm_num [expect, rhoZero, basisZeroDensity,
      qubitX, qubitZ, trace, Matrix.mul_apply, Fin.sum_univ_two]

  have rhoBell_xx : expect rhoBell ((blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * xAxis i))) ⊗ₖ (blochMatrix 0 (WithLp.toLp 2 (fun i => 2 * xAxis i))))=1 := by
    have hsqrt : (Real.sqrt 2 : ℂ)^2=2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; norm_num
    have hinv : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹=(2:ℂ)⁻¹ := by
      rw [← mul_inv, ← pow_two, hsqrt]
    rw [axis_spin.1]
    norm_num [expect, rhoBell, bellDensity, bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients, qubitX, trace, Matrix.mul_apply, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply, Pi.star_apply, hinv]

  have bell_attainment : EGHZ (rhoZero ⊗ₖ rhoBell)=1/2 := by
    have hval : |Istar (rhoZero ⊗ₖ rhoBell) zAxis xAxis xAxis zAxis xAxis zAxis| =1 := by
      simp only [Istar, E_factor _ _ rhoZero_density, rhoZero_values.1, rhoZero_values.2,
        rhoBell_xx, one_mul, zero_mul, mul_zero, sub_zero, abs_one]
    have hm : (1:ℝ) ∈ values (rhoZero ⊗ₖ rhoBell) :=
      ⟨zAxis,xAxis,xAxis,zAxis,xAxis,zAxis,axes_ortho.2,axes_ortho.1,axes_ortho.1,hval.symm⟩
    have hs := le_csSup (product_values_bounded _ _ rhoZero_density rhoBell_density) hm
    apply le_antisymm (product_upper_bound _ _ rhoZero_density rhoBell_density)
    dsimp [EGHZ]
    linarith

  exact ⟨product_upper_bound, rhoZero, rhoBell, rhoZero_density, rhoBell_density, bell_attainment⟩

end D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound

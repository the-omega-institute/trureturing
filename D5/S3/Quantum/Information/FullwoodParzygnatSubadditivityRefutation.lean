/- GID: D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.claim; result=D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result; claim=D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.claim
   digest: The Werner–Holevo channel on the maximally mixed five-level state violates PDM subadditivity. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap

noncomputable section
namespace D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation

/-- Input-first Jamiołkowski matrix, with reversed matrix units in the channel argument. -/
def jamio {n m : ℕ}
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ i, ∑ j, single i j 1 ⊗ₖ E (single j i 1)

/-- The two-time pseudo-density matrix is half the indicated anticommutator. -/
def pdm {n m : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  (1 / 2 : ℝ) • ((ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * jamio E +
    jamio E * (ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)))

/-- Signed spectral entropy, defined by real functional calculus without a proof argument.
For Hermitian X this is the sum of -λ log |λ|, including the value zero at λ = 0. -/
def S {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) : ℝ :=
  (trace (cfc (fun x : ℝ => -x * Real.log |x|) X)).re

/-- Subadditivity for every finite-dimensional density and complete finite Kraus family. -/
def claim : Prop :=
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (ρ : Matrix (Fin n) (Fin n) ℂ), ρ.PosSemidef → trace ρ = 1 →
  ∀ (ι : Type) [Fintype ι] (K : ι → Matrix (Fin m) (Fin n) ℂ),
    (∑ k, (K k)ᴴ * K k) = 1 →
    S (pdm ρ (of_kraus K K)) ≤ S ρ + S ((of_kraus K K) ρ)

private def pairs : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

private def K (k : Fin 10) : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 2 : ℂ) • (single (pairs k).1 (pairs k).2 1 - single (pairs k).2 (pairs k).1 1)

private def ρ : Matrix (Fin 5) (Fin 5) ℂ := (1 / 5 : ℝ) • 1

private def Ω (p : Fin 5 × Fin 5) : ℂ := if p.1 = p.2 then 1 else 0

private def P : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ :=
  (1 / 5 : ℝ) • vecMulVec Ω (star Ω)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem action (X : Matrix (Fin 5) (Fin 5) ℂ) :
    (of_kraus K K) X = (1 / 4 : ℂ) • (trace X • 1 - Xᵀ) := by
  change (∑ k, K k * X * (K k)ᴴ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, pairs, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.single, Matrix.trace] <;> ring

private theorem complete : (∑ k, (K k)ᴴ * K k) = 1 := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  have htp : trace ((of_kraus K K) X) = trace X := by
    rw [action, trace_smul, trace_sub, trace_smul, trace_one, trace_transpose]
    simp only [smul_eq_mul, Fintype.card_fin, Nat.cast_ofNat]
    ring
  change trace (∑ k, K k * X * (K k)ᴴ) = trace X at htp
  rw [trace_sum] at htp
  have ht (k : Fin 10) : trace (K k * X * (K k)ᴴ) = trace (X * ((K k)ᴴ * K k)) := by
    rw [trace_mul_cycle, trace_mul_cycle, Matrix.mul_assoc]
  simp_rw [ht] at htp
  simpa only [Matrix.mul_sum, trace_sum, mul_one] using htp

private theorem jamio_apply {n m : ℕ}
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (a c : Fin n) (b d : Fin m) :
    jamio E (a,b) (c,d) = E (single c a 1) b d := by
  simp [jamio, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single, ite_and]


private theorem P_hermitian : P.IsHermitian := by
  exact (Matrix.posSemidef_vecMulVec_self_star Ω).isHermitian.smul
    (isSelfAdjoint_iff.mpr (by simp) : IsSelfAdjoint (1 / 5 : ℝ))

private theorem P_idempotent : P * P = P := by
  have hdot : star Ω ⬝ᵥ Ω = (5 : ℂ) := by
    simp [dotProduct, Fintype.sum_prod_type, Ω]
  unfold P
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdot]
  ext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    RCLike.real_smul_eq_coe_mul]
  norm_num
  ring

private theorem P_trace : trace P = 1 := by
  simp [P, Matrix.trace, Matrix.vecMulVec_apply, Ω, Fintype.sum_prod_type]

set_option maxRecDepth 100000 in
private theorem jamio_eq : jamio (of_kraus K K) =
    (1 / 4 : ℝ) • (1 - (5 : ℝ) • P) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  rw [jamio_apply, action]
  have ht : trace (single c a (1 : ℂ)) = if c = a then 1 else 0 := by
    by_cases h : c = a
    · subst c; simp
    · simp [trace_single_eq_of_ne c a (1 : ℂ) h, h]
  rw [ht]
  clear ht
  simp [P, Ω, Matrix.single, Matrix.one_apply, Matrix.vecMulVec_apply, Prod.ext_iff]
  split_ifs <;> simp_all only [Matrix.one_apply, and_self, and_true, true_and,
    not_true_eq_false, false_and, and_false, not_false_eq_true] <;> norm_num <;>
    simp_all only [Matrix.one_apply, and_self, and_true, true_and,
      not_true_eq_false, false_and, and_false, not_false_eq_true] <;> norm_num <;> ring

private theorem pdm_eq : pdm ρ (of_kraus K K) =
    (1 / 20 : ℝ) • (1 : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ) +
      (-1 / 4 : ℝ) • P := by
  have hkron : ρ ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) =
      (1 / 5 : ℝ) • (1 : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ) := by
    simp [ρ, Matrix.smul_kronecker]
  unfold pdm
  rw [hkron, jamio_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  module

private theorem stationary : (of_kraus K K) ρ = ρ := by
  rw [action]
  ext i j
  simp [ρ, Matrix.trace, Matrix.one_apply, eq_comm]
  split_ifs <;> norm_num

private theorem density : ρ.PosSemidef ∧ trace ρ = 1 := by
  constructor
  · exact Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 5)
  · norm_num [ρ, Matrix.trace, Fin.sum_univ_succ]

private theorem projection_cfc {n : Type} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (f : ℝ → ℝ) (a b : ℝ) :
    cfc f (a • (1 : Matrix n n ℂ) + b • Q) =
      f a • (1 : Matrix n n ℂ) + (f (a+b) - f a) • Q := by
  have hsa : IsSelfAdjoint Q := hQ
  have haff : cfc (fun x : ℝ => a + b*x) Q = a • (1 : Matrix n n ℂ) + b • Q := by
    rw [cfc_const_add a (fun x : ℝ => b*x) Q (by fun_prop) hsa,
      cfc_const_mul_id b Q hsa, Algebra.algebraMap_eq_smul_one]
  rw [← haff, ← cfc_comp f (fun x : ℝ => a+b*x) Q hsa
    ((Q.finite_real_spectrum.image _).continuousOn _) (by fun_prop)]
  calc
    cfc (fun x : ℝ => f (a+b*x)) Q =
        cfc (fun x : ℝ => f a + (f (a+b) - f a)*x) Q := by
      apply cfc_congr
      intro x hx
      have hspec := (show IsIdempotentElem Q from hQQ).spectrum_subset ℝ hx
      rcases Set.mem_insert_iff.mp hspec with rfl | hx
      · simp
      · have hx : x = 1 := Set.mem_singleton_iff.mp hx
        subst x
        simp
    _ = _ := by
      rw [cfc_const_add _ (fun x : ℝ => (f (a+b) - f a)*x) Q (by fun_prop) hsa,
        cfc_const_mul_id _ Q hsa, Algebra.algebraMap_eq_smul_one]


private theorem entropy_rho : S ρ = Real.log 5 := by
  unfold S ρ
  rw [← Algebra.algebraMap_eq_smul_one, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, trace_smul, trace_one]
  simp only [Complex.smul_re, smul_eq_mul, Complex.natCast_re]
  norm_num [Real.log_div]
  ring

private theorem entropy_pdm : S (pdm ρ (of_kraus K K)) =
    Real.log 5 + (6 / 5 : ℝ) * Real.log 4 := by
  unfold S
  rw [pdm_eq, projection_cfc P P_hermitian P_idempotent,
    trace_add, trace_smul, trace_smul, trace_one, P_trace]
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.natCast_re,
    Complex.one_re]
  norm_num [Real.log_div]
  rw [show (20 : ℝ) = 4 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- The finite Kraus Werner–Holevo process in dimension five violates subadditivity. -/
theorem result : ¬ claim := by
  intro hclaim
  have hbound := hclaim 5 5 (by norm_num) (by norm_num) ρ density.1 density.2
    (Fin 10) K complete
  obtain ⟨channel, hchannel⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K complete
  have hchannelAction : CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix ρ)) = (of_kraus K K) ρ := by
    exact hchannel ρ
  have hfixed : CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix ρ)) = ρ :=
    hchannelAction.trans stationary
  rw [← hchannelAction, hfixed, entropy_rho, entropy_pdm] at hbound
  have hgap : 0 < (1 / 5 : ℝ) * Real.log (4096 / 3125) := by
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hlogs : Real.log (4096 / 3125 : ℝ) = 6 * Real.log 4 - 5 * Real.log 5 := by
    rw [show (4096 / 3125 : ℝ) = 4^6 / 5^5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [hlogs] at hgap
  linarith

#print axioms result

end D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation

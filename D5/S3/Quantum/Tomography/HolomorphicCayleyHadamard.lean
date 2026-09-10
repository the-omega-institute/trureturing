/- GID: D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/HolomorphicCayleyHadamard
   mirror-E: none(waiver:analytic-continuation-bridge)
   anchors: []
   digest: The actual real Cayley residual admits a paired holomorphic extension with an explicit complex Frechet Jacobian and exact complex residual conservation. -/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/- Reuse: Matrix.mulVec, dotProduct_mulVec, mulVec_mulVec, complex star,
   ContinuousLinearMap.proj/pi and Mathlib's actual derivative rules.
   CayleyHadamardDifferential owns the real path derivative. Its private
   coordinate formula is the real restriction of this complex chart.
   The conjugate coefficient is fixed. No conjugation of a complex variable
   occurs in the extension; normSq is used only in the real-slice theorem.
   H is fixed. Holomorphically varying H requires a separate coefficient
   companion, not pointwise conjugation of a holomorphic H-parameter.
-/

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.HolomorphicCayleyHadamard

open Matrix

/-- The complex Cayley phase. For a unit coefficient s, its reciprocal
companion is `cayleyPhase (star s) (-z)`, away from the two poles. -/
def cayleyPhase (s z : ℂ) : ℂ := s * (1 + Complex.I * z) / (1 - Complex.I * z)

private abbrev plusAmplitude {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (s z : Fin d → ℂ) (a : Fin d) : ℂ :=
  ∑ i, star (H i a) * cayleyPhase (s i) (z i)

private abbrev minusAmplitude {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (s z : Fin d → ℂ) (a : Fin d) : ℂ :=
  ∑ i, H i a * cayleyPhase (star (s i)) (-z i)

/-- Holomorphic complexification of the squared-modulus residual, using
paired rational factors. On real coordinates it equals the real residual. -/
def pairedCayleyResidual {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (s z : Fin d → ℂ) : Fin d → ℂ := fun a ↦
  plusAmplitude H s z a * minusAmplitude H s z a - (d : ℂ)

/-- Actual complex Jacobian. The negative sign in the second summand is
essential: the reciprocal companion has derivative -2 i conjugate(s)/(1+i z)^2. -/
def pairedCayleyJacobian {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (s z : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ := fun a k ↦
  (star (H k a) * (2 * Complex.I * s k / (1 - Complex.I * z k) ^ 2)) *
      minusAmplitude H s z a +
    (H k a * (-2 * Complex.I * star (s k) / (1 + Complex.I * z k) ^ 2)) *
      plusAmplitude H s z a

private theorem phase_hasDerivAt (s z : ℂ) (hz : 1 - Complex.I * z ≠ 0) :
    HasDerivAt (cayleyPhase s)
      (2 * Complex.I * s / (1 - Complex.I * z) ^ 2) z := by
  have hn := (((hasDerivAt_id z).const_mul Complex.I).const_add 1).const_mul s
  have hd := (hasDerivAt_const z (1 : ℂ)).sub
    ((hasDerivAt_id z).const_mul Complex.I)
  convert! hn.div hd hz using 1 <;> simp only [cayleyPhase, id_eq, Pi.sub_apply] <;> ring

private theorem dual_hasDerivAt (s z : ℂ) (hz : 1 + Complex.I * z ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ cayleyPhase (star s) (-w))
      (-2 * Complex.I * star s / (1 + Complex.I * z) ^ 2) z := by
  have h := (phase_hasDerivAt (star s) (-z)
    (by simpa only [mul_neg, sub_neg_eq_add] using hz)).comp z
      (hasDerivAt_id z).neg
  convert! h using 1 <;> simp only [mul_neg, sub_neg_eq_add] <;> ring

private theorem phase_coordinate_hasFDerivAt {d : ℕ}
    (s z : Fin d → ℂ) (k : Fin d) (hz : 1 - Complex.I * z k ≠ 0) :
    HasFDerivAt (fun w : Fin d → ℂ ↦ cayleyPhase (s k) (w k))
      ((2 * Complex.I * s k / (1 - Complex.I * z k) ^ 2) •
        (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ)) z := by
  have h := (phase_hasDerivAt (s k) (z k) hz).hasFDerivAt.comp z
    (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt
  convert! h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

private theorem dual_coordinate_hasFDerivAt {d : ℕ}
    (s z : Fin d → ℂ) (k : Fin d) (hz : 1 + Complex.I * z k ≠ 0) :
    HasFDerivAt (fun w : Fin d → ℂ ↦ cayleyPhase (star (s k)) (-w k))
      ((-2 * Complex.I * star (s k) / (1 + Complex.I * z k) ^ 2) •
        (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ)) z := by
  have h := (dual_hasDerivAt (s k) (z k) hz).hasFDerivAt.comp z
    (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt
  convert! h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-- The complete complex Frechet derivative, not merely a real directional
formula. It applies in every finite order and to every fixed matrix H.
Dephasing is obtained by fixing z_0=0 and s_0=1 and deleting that column. -/
theorem paired_cayley_residual_hasFDerivAt
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (s z : Fin d → ℂ)
    (hminus : ∀ k, 1 - Complex.I * z k ≠ 0)
    (hplus : ∀ k, 1 + Complex.I * z k ≠ 0) :
    HasFDerivAt (pairedCayleyResidual H s)
      (ContinuousLinearMap.pi (fun a ↦
        ∑ k, pairedCayleyJacobian H s z a k •
          (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ))) z := by
  apply hasFDerivAt_pi.mpr
  intro a
  have hA := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (phase_coordinate_hasFDerivAt s z k (hminus k)).const_mul (star (H k a)))
  have hB := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (dual_coordinate_hasFDerivAt s z k (hplus k)).const_mul (H k a))
  have h := (hA.mul hB).sub_const (d : ℂ)
  convert! h using 1
  ext v
  simp only [pairedCayleyJacobian, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  conv_rhs => rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The actual square five-variable system: fix the first phase and delete
only the sixth outcome. Full outcome conservation justifies the latter for
Hadamard input; the deleted variable removes the common-phase gauge. -/
def dephasedCayleyResidual (H : Matrix (Fin 6) (Fin 6) ℂ)
    (s z : Fin 5 → ℂ) : Fin 5 → ℂ := fun a ↦
  pairedCayleyResidual H (Fin.cases 1 s) (Fin.cases 0 z) a.castSucc

/-- The five-by-five Jacobian is the indicated submatrix of the full complex
Jacobian. No invertibility is asserted. In particular, the redundant six-by-six
system must not be used to claim an invertible Newton preconditioner. -/
theorem dephased_cayley_residual_hasFDerivAt
    (H : Matrix (Fin 6) (Fin 6) ℂ) (s z : Fin 5 → ℂ)
    (hm : ∀ k, 1 - Complex.I * z k ≠ 0)
    (hp : ∀ k, 1 + Complex.I * z k ≠ 0) :
    HasFDerivAt (dephasedCayleyResidual H s)
      (ContinuousLinearMap.pi (fun a ↦
        ∑ k : Fin 5,
          pairedCayleyJacobian H (Fin.cases 1 s) (Fin.cases 0 z) a.castSucc k.succ •
            (ContinuousLinearMap.proj k : (Fin 5 → ℂ) →L[ℂ] ℂ))) z := by
  let embed : (Fin 5 → ℂ) →L[ℂ] (Fin 6 → ℂ) :=
    ContinuousLinearMap.pi (Fin.cases 0 (fun k ↦ ContinuousLinearMap.proj k))
  let select : (Fin 6 → ℂ) →L[ℂ] (Fin 5 → ℂ) :=
    ContinuousLinearMap.pi (fun a : Fin 5 ↦ ContinuousLinearMap.proj a.castSucc)
  have he (w : Fin 5 → ℂ) : embed w = Fin.cases 0 w := by
    funext k
    refine Fin.cases ?_ (fun j ↦ ?_) k <;> rfl
  have hm6 : ∀ k : Fin 6, 1 - Complex.I * (embed z) k ≠ 0 := by
    intro k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · simp [embed]
    · simpa [embed] using hm j
  have hp6 : ∀ k : Fin 6, 1 + Complex.I * (embed z) k ≠ 0 := by
    intro k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · simp [embed]
    · simpa [embed] using hp j
  have h := select.hasFDerivAt.comp z
    ((paired_cayley_residual_hasFDerivAt H (Fin.cases 1 s) (embed z) hm6 hp6).comp
      z embed.hasFDerivAt)
  convert! h using 1
  ext v a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, select, smul_eq_mul, he]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add]

private theorem dual_on_real (s : ℂ) (t : ℝ) :
    cayleyPhase (star s) (-(t : ℂ)) = star (cayleyPhase s (t : ℂ)) := by
  simp [cayleyPhase, map_div, map_mul, map_add, map_sub,
    Complex.star_def, Complex.conj_I]

/-- Actual real-slice binding. Arbitrary fixed complex phases are supported,
including the quarter-turn phases used in the existing root boxes. -/
theorem paired_cayley_residual_on_real
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (s : Fin d → ℂ)
    (t : Fin d → ℝ) (a : Fin d) :
    pairedCayleyResidual H s (fun k ↦ (t k : ℂ)) a =
      ((Complex.normSq ((Hᴴ *ᵥ (fun k ↦ cayleyPhase (s k) (t k))) a) -
        (d : ℝ) : ℝ) : ℂ) := by
  have hb : minusAmplitude H s (fun k ↦ (t k : ℂ)) a =
      star (plusAmplitude H s (fun k ↦ (t k : ℂ)) a) := by
    simp only [minusAmplitude, plusAmplitude, star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro k _
    rw [dual_on_real]
    exact mul_comm _ _
  unfold pairedCayleyResidual
  rw [hb]
  simp only [plusAmplitude, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_natCast]

private theorem phase_times_dual (s z : ℂ)
    (hs : Complex.normSq s = 1)
    (hm : 1 - Complex.I * z ≠ 0) (hp : 1 + Complex.I * z ≠ 0) :
    cayleyPhase s z * cayleyPhase (star s) (-z) = 1 := by
  calc
    cayleyPhase s z * cayleyPhase (star s) (-z) = s * star s := by
      dsimp [cayleyPhase]
      simp only [mul_neg, sub_neg_eq_add]
      field_simp [hm, hp]
      <;> ring
    _ = 1 := by
      simpa only [Complex.star_def, hs, Complex.ofReal_one] using Complex.mul_conj s

/-- Residual conservation holds throughout the complex domain, by matrix
algebra rather than an univariate identity-theorem argument. Hence a common
coefficient shift in a balanced readout remains valid after complexification. -/
theorem paired_cayley_residual_sum_zero
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (s z : Fin d → ℂ)
    (hGram : H * Hᴴ = (d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
    (hs : ∀ k, Complex.normSq (s k) = 1)
    (hm : ∀ k, 1 - Complex.I * z k ≠ 0)
    (hp : ∀ k, 1 + Complex.I * z k ≠ 0) :
    ∑ a, pairedCayleyResidual H s z a = 0 := by
  let u : Fin d → ℂ := fun k ↦ cayleyPhase (s k) (z k)
  let v : Fin d → ℂ := fun k ↦ cayleyPhase (star (s k)) (-z k)
  have huv (k : Fin d) : u k * v k = 1 :=
    phase_times_dual (s k) (z k) (hs k) (hm k) (hp k)
  have hB (a : Fin d) : minusAmplitude H s z a = (v ᵥ* H) a := by
    simp only [minusAmplitude, Matrix.vecMul, dotProduct, v, mul_comm]
  have hA (a : Fin d) : plusAmplitude H s z a = (Hᴴ *ᵥ u) a := by
    rfl
  have hEnergy : (v ᵥ* H) ⬝ᵥ (Hᴴ *ᵥ u) = (d : ℂ) * (v ⬝ᵥ u) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hGram,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    rfl
  have hmass : v ⬝ᵥ u = (d : ℂ) := by
    simp only [dotProduct]
    simp_rw [mul_comm (v _) (u _), huv]
    simp
  calc
    ∑ a, pairedCayleyResidual H s z a =
        (v ᵥ* H) ⬝ᵥ (Hᴴ *ᵥ u) - ∑ _a : Fin d, (d : ℂ) := by
      simp only [pairedCayleyResidual, hB, hA, Finset.sum_sub_distrib, dotProduct]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [hEnergy, hmass]; simp

#print axioms paired_cayley_residual_hasFDerivAt
#print axioms dephased_cayley_residual_hasFDerivAt
#print axioms paired_cayley_residual_on_real
#print axioms paired_cayley_residual_sum_zero

end D5.S3.Quantum.Tomography.HolomorphicCayleyHadamard

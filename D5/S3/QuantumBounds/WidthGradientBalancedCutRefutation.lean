/- GID: D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/WidthGradientBalancedCutRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.claim; result=D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.result; claim=D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.claim
   digest: A product of four singlets violates the balanced-cut gradient bound. -/

import D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence

/-!
Four singlets within the two halves have zero total spin and gradient square 240.
The balanced-cut conjecture permits only 48 at zero total spin.
-/

set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation

open Matrix
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (localOp pauliMatrix tensorOp)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity pure_state_handshake)
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
  (singletVector singlet)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape (Bits local_adjoint)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (pauli_hermitian)

/-- Computational basis of both sides of the balanced cut. -/
abbrev Sys (m : ℕ) := Bits m × Bits m

/-- A single-site operator, with the first m sites on the first tensor factor. -/
def siteOp (m : ℕ) (k : Fin (2 * m)) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Sys m) (Sys m) ℂ :=
  if h : k.val < m then localOp ⟨k.val, h⟩ A ⊗ₖ 1
  else 1 ⊗ₖ localOp ⟨k.val - m, by omega⟩ A

/-- Squared total spin, using Pauli normalization. -/
def totalSpinSq (m : ℕ) : Matrix (Sys m) (Sys m) ℂ :=
  ∑ l : Fin 3, (∑ k : Fin (2 * m), siteOp m k (pauli l)) ^ 2

/-- The one-based balanced-cut gradient weight `2 (k+1) - 2m - 1`. -/
def gradientWeight (m : ℕ) (k : Fin (2 * m)) : ℂ :=
  (((2 * (k.val + 1) : ℝ) - 2 * m - 1 : ℝ) : ℂ)

/-- Squared gradient spin with the one-based weights 2k - N - 1. -/
def gradientSq (m : ℕ) : Matrix (Sys m) (Sys m) ℂ :=
  ∑ l : Fin 3, (∑ k : Fin (2 * m),
    gradientWeight m k • siteOp m k (pauli l)) ^ 2

/-- The balanced-cut gradient inequality for every even number of at least four qubits. -/
def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ ρ : Matrix (Sys m) (Sys m) ℂ,
    ρ.PosSemidef → ρ.trace = 1 → IsSeparable ρ →
      (ρ * gradientSq m).trace.re ≤
        6 * (2 * (m : ℝ)) +
          (((2 * (m : ℝ)) ^ 4 / 4 +
            2 * (2 * (m : ℝ) - 1) * (2 * (m : ℝ)) * (2 * (m : ℝ) + 1) / 3 -
            6 * (2 * (m : ℝ))) / (2 * (2 * (m : ℝ)))) *
              (ρ * totalSpinSq m).trace.re

private def halfEquiv : Bits 4 ≃ ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) where
  toFun x := ((x 0, x 1), (x 2, x 3))
  invFun p := ![p.1.1, p.1.2, p.2.1, p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl

private lemma half_sum (f : Bits 4 → ℂ) :
    ∑ x, f x = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
      f ![a,b,c,d] := by
  rw [← Equiv.sum_comp halfEquiv.symm]
  simp only [Fintype.sum_prod_type]
  rfl

private def chi (x : Bits 4) : ℂ :=
  (1 / 2 : ℂ) * singletVector (finTwoEquiv (x 0), finTwoEquiv (x 3)) *
    singletVector (finTwoEquiv (x 1), finTwoEquiv (x 2))

private def halfDensity : Matrix (Bits 4) (Bits 4) ℂ := rankOneDensity chi

private lemma chi_normalized : star chi ⬝ᵥ chi = 1 := by
  have hs : ((1 / 2 : ℝ) • rankOneDensity singletVector).trace = 1 :=
    singlet.trace_eq_one
  have ht : (rankOneDensity singletVector).trace = 2 := by
    rw [trace_smul] at hs
    norm_num [Complex.real_smul] at hs
    linear_combination 2 * hs
  have hf : star chi ⬝ᵥ chi =
      (1 / 4 : ℂ) * (rankOneDensity singletVector).trace ^ 2 := by
    simp only [dotProduct, half_sum, chi, rankOneDensity, trace, diag_apply,
      vecMulVec_apply, Pi.star_apply, star_mul, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_two]
    norm_num [finTwoEquiv]
    ring
  rw [hf, ht]
  norm_num

private lemma half_trace_one : halfDensity.trace = 1 := by
  simpa only [halfDensity, rankOneDensity, trace_vecMulVec, dotProduct_comm] using chi_normalized

private lemma half_expectation (A : Matrix (Bits 4) (Bits 4) ℂ) :
    (halfDensity * A).trace = star chi ⬝ᵥ A *ᵥ chi := by
  rw [trace_mul_comm]
  exact (pure_state_handshake chi chi_normalized A).2.2.symm

private def halfSpin (l : Fin 3) : Matrix (Bits 4) (Bits 4) ℂ :=
  ∑ j : Fin 4, localOp j (pauli l)

private def halfGradient (c : ℝ) (l : Fin 3) : Matrix (Bits 4) (Bits 4) ℂ :=
  ∑ j : Fin 4, ((c + 2 * j.val : ℝ) : ℂ) • localOp j (pauli l)

private lemma half_gradient_adjoint (c : ℝ) (l : Fin 3) :
    (halfGradient c l)ᴴ = halfGradient c l := by
  simp only [halfGradient, conjTranspose_sum, conjTranspose_smul, local_adjoint,
    pauli, pauli_hermitian, Complex.star_def, Complex.conj_ofReal]

set_option maxHeartbeats 2000000 in
-- The sums use all sixteen computational basis amplitudes.
private lemma half_spin_annihilates (l : Fin 3) : halfSpin l *ᵥ chi = 0 := by
  fin_cases l
  all_goals
    funext x
    obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, rfl⟩ := halfEquiv.symm.surjective x
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [halfSpin, Matrix.mulVec, dotProduct, half_sum, localOp, tensorOp,
        pauli, pauliMatrix, qubitX, qubitZ, chi, singletVector, finTwoEquiv,
        Fin.sum_univ_succ, Fin.prod_univ_succ, Function.update_apply, Matrix.one_apply,
        Matrix.mul_apply, halfEquiv]

private lemma half_gradient_shift (c : ℝ) (l : Fin 3) :
    halfGradient c l = (c : ℂ) • halfSpin l + halfGradient 0 l := by
  simp only [halfGradient, halfSpin, Complex.ofReal_add,
    zero_add, add_smul, Finset.sum_add_distrib, Finset.smul_sum]

private lemma half_gradient_action (c : ℝ) (l : Fin 3) :
    halfGradient c l *ᵥ chi = halfGradient 0 l *ᵥ chi := by
  rw [half_gradient_shift, add_mulVec, smul_mulVec, half_spin_annihilates, smul_zero,
    zero_add]

private lemma half_gradient_mean (c : ℝ) (l : Fin 3) :
    (halfDensity * halfGradient c l).trace = 0 := by
  rw [half_expectation, half_gradient_action]
  fin_cases l
  all_goals
    norm_num [dotProduct, half_sum, halfGradient, Matrix.mulVec, localOp, tensorOp,
      pauli, pauliMatrix, qubitX, qubitZ, chi, singletVector, finTwoEquiv,
      Fin.sum_univ_succ, Fin.prod_univ_succ, Function.update_apply, Matrix.one_apply,
      Matrix.mul_apply, halfEquiv]

private lemma half_gradient_second (c : ℝ) (l : Fin 3) :
    (halfDensity * (halfGradient c l) ^ 2).trace = 40 := by
  rw [half_expectation, pow_two, ← mulVec_mulVec, dotProduct_mulVec]
  have hrow : star chi ᵥ* halfGradient c l = star (halfGradient c l *ᵥ chi) := by
    rw [star_mulVec, half_gradient_adjoint]
  rw [hrow]
  simp only [half_gradient_action]
  fin_cases l
  all_goals
    norm_num [dotProduct, half_sum, halfGradient, Matrix.mulVec, localOp, tensorOp,
      pauli, pauliMatrix, qubitX, qubitZ, chi, singletVector, finTwoEquiv,
      Fin.sum_univ_succ, Fin.prod_univ_succ, Function.update_apply, Matrix.one_apply,
      Matrix.mul_apply, halfEquiv, map_ofNat] <;>
      ring_nf <;> norm_num [Complex.I_sq]

private lemma half_spin_mean (l : Fin 3) : (halfDensity * halfSpin l).trace = 0 := by
  rw [half_expectation, half_spin_annihilates, dotProduct_zero]

private lemma half_spin_second (l : Fin 3) :
    (halfDensity * (halfSpin l) ^ 2).trace = 0 := by
  rw [half_expectation, pow_two, ← mulVec_mulVec, half_spin_annihilates,
    Matrix.mulVec_zero, dotProduct_zero]

private def rho : Matrix (Sys 4) (Sys 4) ℂ := halfDensity ⊗ₖ halfDensity

private lemma product_second (A B : Matrix (Bits 4) (Bits 4) ℂ) :
    (rho * (A ⊗ₖ 1 + 1 ⊗ₖ B) ^ 2).trace =
      (halfDensity * A ^ 2).trace +
        2 * (halfDensity * A).trace * (halfDensity * B).trace +
          (halfDensity * B ^ 2).trace := by
  simp only [rho, pow_two, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, trace_add, trace_kronecker,
    half_trace_one]
  ring

private lemma total_spin_split (l : Fin 3) :
    (∑ k : Fin (2 * 4), siteOp 4 k (pauli l)) =
      halfSpin l ⊗ₖ 1 + 1 ⊗ₖ halfSpin l := by
  norm_num [Fin.sum_univ_succ, siteOp, halfSpin, add_kronecker, kronecker_add]
  abel

private lemma gradient_split (l : Fin 3) :
    (∑ k : Fin (2 * 4), gradientWeight 4 k • siteOp 4 k (pauli l)) =
        halfGradient (-7) l ⊗ₖ 1 + 1 ⊗ₖ halfGradient 1 l := by
  ext x y
  norm_num [Fin.sum_univ_succ, siteOp, halfGradient, gradientWeight,
    Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma total_spin_value : (rho * totalSpinSq 4).trace = 0 := by
  simp only [totalSpinSq, Matrix.mul_sum, trace_sum, total_spin_split,
    product_second, half_spin_mean, half_spin_second]
  norm_num

private lemma gradient_value : (rho * gradientSq 4).trace = 240 := by
  simp only [gradientSq, Matrix.mul_sum, trace_sum, gradient_split,
    product_second, half_gradient_mean, half_gradient_second]
  norm_num

/-- Four singlets within the two halves give total spin zero and gradient square 240. -/
theorem result : ¬ claim := by
  have hhalf : halfDensity.PosSemidef := posSemidef_vecMulVec_self_star chi
  have hpositive : rho.PosSemidef := hhalf.kronecker hhalf
  have htrace : rho.trace = 1 := by
    rw [rho, trace_kronecker, half_trace_one, one_mul]
  have hsep : IsSeparable rho := by
    refine ⟨1, fun _ => 1, fun _ => halfDensity, fun _ => halfDensity, ?_, ?_, ?_, ?_⟩
    · intro t; norm_num
    · simp
    · intro t; exact ⟨⟨hhalf, half_trace_one⟩, ⟨hhalf, half_trace_one⟩⟩
    · simp [rho]
  intro h
  have hbound := h 4 (by norm_num) rho hpositive htrace hsep
  rw [gradient_value, total_spin_value] at hbound
  norm_num at hbound

end D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation

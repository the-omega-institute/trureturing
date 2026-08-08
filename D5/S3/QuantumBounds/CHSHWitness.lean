/- GID: D5/S3/QuantumBounds/CHSHWitness
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/CHSHWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit a Bell-state CHSH witness attaining the Tsirelson value. -/

/- Library-search audit trail (2026-08-08):
   * The complete pinned `Mathlib.Algebra.Star.CHSH` source was read. Its
     `tsirelson_inequality` is the upstream source for the general bound; this module proves only
     the explicit finite-dimensional witness and does not reproduce that bound.
   * `D5.S3.Quantum.FiniteDimensional` supplies the Pauli matrices and their observable
     certificates. `D5.S3.Quantum.QubitWitnesses` supplies `bellCoefficients`.
   * `Matrix.posSemidef_vecMulVec_self_star` and `Matrix.trace_vecMulVec` supply the rank-one
     positivity and trace interfaces. `Matrix.conjTranspose_kronecker`,
     `Matrix.mul_kronecker_mul`, and `Matrix.one_kronecker_one` supply the lifted CHSH tuple
     certificate. The remaining equalities are explicit two- and four-index calculations.
-/

import D5.S3.Quantum.QubitWitnesses
import Mathlib.Algebra.Star.CHSH

namespace D5.S3.QuantumBounds.CHSHWitness

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

open scoped ComplexOrder
open scoped Kronecker

/-- The two-qubit matrix algebra in the product computational basis. -/
abbrev TwoQubitMatrix := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The normalized Bell vector obtained by flattening `bellCoefficients`. -/
noncomputable def bellVector : Fin 2 × Fin 2 → ℂ :=
  fun ij => bellCoefficients ij.1 ij.2 / (Real.sqrt 2 : ℂ)

/-- The rank-one density matrix of the normalized Bell vector. -/
noncomputable def bellDensity : TwoQubitMatrix :=
  Matrix.vecMulVec bellVector (star bellVector)

/-- Bob's plus Pauli-axis observable. -/
noncomputable def bobObservable0 : QubitMatrix :=
  ((Real.sqrt 2)⁻¹ : ℝ) • (qubitZ + qubitX)

/-- Bob's minus Pauli-axis observable. -/
noncomputable def bobObservable1 : QubitMatrix :=
  ((Real.sqrt 2)⁻¹ : ℝ) • (qubitZ - qubitX)

/-- The CHSH operator for the fixed Pauli and Bob observables. -/
noncomputable def chshOperator : TwoQubitMatrix :=
  qubitZ ⊗ₖ bobObservable0 + qubitZ ⊗ₖ bobObservable1 +
    qubitX ⊗ₖ bobObservable0 - qubitX ⊗ₖ bobObservable1

/-- Alice's first observable lifted to the two-qubit algebra. -/
noncomputable def liftA0 : TwoQubitMatrix :=
  qubitZ ⊗ₖ (1 : QubitMatrix)

/-- Alice's second observable lifted to the two-qubit algebra. -/
noncomputable def liftA1 : TwoQubitMatrix :=
  qubitX ⊗ₖ (1 : QubitMatrix)

/-- Bob's first observable lifted to the two-qubit algebra. -/
noncomputable def liftB0 : TwoQubitMatrix :=
  (1 : QubitMatrix) ⊗ₖ bobObservable0

/-- Bob's second observable lifted to the two-qubit algebra. -/
noncomputable def liftB1 : TwoQubitMatrix :=
  (1 : QubitMatrix) ⊗ₖ bobObservable1

private theorem kronecker_involution (A B : QubitMatrix)
    (hA : A ^ 2 = 1) (hB : B ^ 2 = 1) :
    (A ⊗ₖ B : TwoQubitMatrix) ^ 2 = 1 := by
  rw [pow_two, ← Matrix.mul_kronecker_mul, ← pow_two, ← pow_two, hA, hB,
    Matrix.one_kronecker_one]

private theorem kronecker_self_adjoint (A B : QubitMatrix)
    (hA : star A = A) (hB : star B = B) :
    star (A ⊗ₖ B : TwoQubitMatrix) = A ⊗ₖ B := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hA, hB]

private theorem lifted_observables_commute (A B : QubitMatrix) :
    (A ⊗ₖ (1 : QubitMatrix)) * ((1 : QubitMatrix) ⊗ₖ B) =
      ((1 : QubitMatrix) ⊗ₖ B) * (A ⊗ₖ (1 : QubitMatrix)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The original Kronecker-product definition is the CHSH combination of the lifted tuple. -/
theorem chsh_operator_eq_lifted_chsh :
    chshOperator =
      liftA0 * liftB0 + liftA0 * liftB1 + liftA1 * liftB0 - liftA1 * liftB1 := by
  simp only [liftA0, liftA1, liftB0, liftB1, ← Matrix.mul_kronecker_mul,
    mul_one, one_mul]
  rfl

private theorem complex_sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem complex_sqrt_two_inv_mul_self :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← pow_two, complex_sqrt_two_sq]

private theorem complex_sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)

private theorem four_mul_inv_sqrt_two :
    (4 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = 2 * (Real.sqrt 2 : ℂ) := by
  apply mul_right_cancel₀ complex_sqrt_two_ne_zero
  rw [mul_assoc, inv_mul_cancel₀ complex_sqrt_two_ne_zero, mul_one, mul_assoc,
    ← pow_two, complex_sqrt_two_sq]
  norm_num

/-- The Bell rank-one matrix is positive semidefinite and has trace one. -/
theorem bell_density_is_state :
    bellDensity.PosSemidef ∧ Matrix.trace bellDensity = 1 := by
  constructor
  · exact Matrix.posSemidef_vecMulVec_self_star bellVector
  · rw [bellDensity, Matrix.trace_vecMulVec]
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [bellVector, bellCoefficients, complex_sqrt_two_inv_mul_self]

/-- Bob's two fixed observables are self-adjoint involutions. -/
theorem bob_observables_are_valid :
    (star bobObservable0 = bobObservable0 ∧ bobObservable0 ^ 2 = 1) ∧
      (star bobObservable1 = bobObservable1 ∧ bobObservable1 ^ 2 = 1) := by
  constructor <;> constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bobObservable0, qubitX, qubitZ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [bobObservable0, qubitX, qubitZ, pow_two, Matrix.mul_apply,
        Fin.sum_univ_two, complex_sqrt_two_inv_mul_self]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bobObservable1, qubitX, qubitZ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [bobObservable1, qubitX, qubitZ, pow_two, Matrix.mul_apply,
        Fin.sum_univ_two, complex_sqrt_two_inv_mul_self]

/-- The four lifted observables form a CHSH tuple in the two-qubit matrix algebra. -/
theorem lifted_observables_form_chsh_tuple :
    IsCHSHTuple liftA0 liftA1 liftB0 liftB1 := by
  rcases qubit_weyl_star with ⟨_, hXsa, hZsa, hXinv, hZinv⟩
  rcases bob_observables_are_valid with ⟨⟨hB0sa, hB0inv⟩, hB1sa, hB1inv⟩
  refine
    { A₀_inv := ?_
      A₁_inv := ?_
      B₀_inv := ?_
      B₁_inv := ?_
      A₀_sa := ?_
      A₁_sa := ?_
      B₀_sa := ?_
      B₁_sa := ?_
      A₀B₀_commutes := ?_
      A₀B₁_commutes := ?_
      A₁B₀_commutes := ?_
      A₁B₁_commutes := ?_ }
  · exact kronecker_involution qubitZ 1 hZinv (by simp)
  · exact kronecker_involution qubitX 1 hXinv (by simp)
  · exact kronecker_involution 1 bobObservable0 (by simp) hB0inv
  · exact kronecker_involution 1 bobObservable1 (by simp) hB1inv
  · exact kronecker_self_adjoint qubitZ 1 hZsa (by simp)
  · exact kronecker_self_adjoint qubitX 1 hXsa (by simp)
  · exact kronecker_self_adjoint 1 bobObservable0 (by simp) hB0sa
  · exact kronecker_self_adjoint 1 bobObservable1 (by simp) hB1sa
  · exact lifted_observables_commute qubitZ bobObservable0
  · exact lifted_observables_commute qubitZ bobObservable1
  · exact lifted_observables_commute qubitX bobObservable0
  · exact lifted_observables_commute qubitX bobObservable1

/-- The fixed Bell state attains the positive Tsirelson value `2 * sqrt 2`. -/
theorem bell_chsh_value :
    Matrix.trace (bellDensity * chshOperator) = ((2 * Real.sqrt 2 : ℝ) : ℂ) := by
  calc
    Matrix.trace (bellDensity * chshOperator) =
        (4 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ := by
      simp [bellDensity, bellVector, chshOperator, bobObservable0, bobObservable1,
        bellCoefficients, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply,
        Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        complex_sqrt_two_inv_mul_self]
      ring
    _ = ((2 * Real.sqrt 2 : ℝ) : ℂ) := by
      simpa using four_mul_inv_sqrt_two

end D5.S3.QuantumBounds.CHSHWitness

/- GID: D5/S3/Quantum/CloningMachine
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive the universal cloning machine's reduced spectrum and entropy. -/

import D5.S3.Quantum.QubitWitnesses

namespace D5.S3.Quantum.CloningMachine

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

open scoped BigOperators
open scoped ComplexOrder

/-- The canonical normalized complement of a qubit state. -/
def orthogonalQubit (psi : QubitState) : QubitState :=
  ![-star (psi 1), star (psi 0)]

/-- The canonical complement is orthogonal to its input. -/
theorem orthogonal_qubit_inner (psi : QubitState) :
    star psi ⬝ᵥ orthogonalQubit psi = 0 := by
  simp [orthogonalQubit, dotProduct, Fin.sum_univ_two]
  ring

/-- The machine-qubit reduced state of the universal symmetric cloning isometry. -/
noncomputable def machineReducedState (psi : QubitState) : QubitMatrix :=
  (1 / 3 : Real) • Matrix.vecMulVec psi (star psi) +
    (2 / 3 : Real) • Matrix.vecMulVec (orthogonalQubit psi) (star (orthogonalQubit psi))

/-- The cloning machine's reduced state is positive semidefinite. -/
theorem machine_reduced_posSemidef (psi : QubitState) :
    (machineReducedState psi).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact (Matrix.posSemidef_vecMulVec_self_star psi).smul (by norm_num)
  · exact (Matrix.posSemidef_vecMulVec_self_star (orthogonalQubit psi)).smul (by norm_num)

/-- Taking the canonical complement preserves squared norm. -/
theorem orthogonal_qubit_norm_sq (psi : QubitState) :
    star (orthogonalQubit psi) ⬝ᵥ orthogonalQubit psi = star psi ⬝ᵥ psi := by
  simp [orthogonalQubit, dotProduct, Fin.sum_univ_two]
  ring

private theorem orthogonal_qubit_trace_norm_sq (psi : QubitState) :
    orthogonalQubit psi ⬝ᵥ star (orthogonalQubit psi) = psi ⬝ᵥ star psi := by
  simp [orthogonalQubit, dotProduct, Fin.sum_univ_two]
  ring

/-- A normalized input gives a trace-one machine reduced state. -/
theorem machine_reduced_trace
    (psi : QubitState) (hUnit : star psi ⬝ᵥ psi = 1) :
    Matrix.trace (machineReducedState psi) = 1 := by
  have hUnit' : psi 0 * star (psi 0) + psi 1 * star (psi 1) = 1 := by
    calc
      psi 0 * star (psi 0) + psi 1 * star (psi 1) =
          star (psi 0) * psi 0 + star (psi 1) * psi 1 := by ring
      _ = 1 := by simpa [dotProduct, Fin.sum_univ_two] using hUnit
  have hUnitTrace : psi ⬝ᵥ star psi = 1 := by
    simpa [dotProduct, Fin.sum_univ_two] using hUnit'
  rw [machineReducedState, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_vecMulVec, Matrix.trace_smul, Matrix.trace_vecMulVec,
    orthogonal_qubit_trace_norm_sq, hUnitTrace]
  norm_num

/-- A normalized input produces a positive semidefinite trace-one machine matrix. -/
theorem machine_reduced_is_density
    (psi : QubitState) (hUnit : star psi ⬝ᵥ psi = 1) :
    (machineReducedState psi).PosSemidef ∧ Matrix.trace (machineReducedState psi) = 1 :=
  ⟨machine_reduced_posSemidef psi, machine_reduced_trace psi hUnit⟩

/-- The determinant of every normalized machine reduced state is `2 / 9`. -/
theorem machine_reduced_det
    (psi : QubitState) (hUnit : star psi ⬝ᵥ psi = 1) :
    Matrix.det (machineReducedState psi) = (2 / 9 : Complex) := by
  have hUnit' : star (psi 0) * psi 0 + star (psi 1) * psi 1 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two] using hUnit
  calc
    Matrix.det (machineReducedState psi) =
        (2 / 9 : Complex) *
          (star (psi 0) * psi 0 + star (psi 1) * psi 1) ^ 2 := by
      simp [machineReducedState, orthogonalQubit, Matrix.det_fin_two,
        Matrix.vecMulVec_apply]
      ring
    _ = 2 / 9 := by rw [hUnit']; norm_num

/-- The normalized machine reduced state's characteristic polynomial is input-independent. -/
theorem machine_reduced_charpoly
    (psi : QubitState) (hUnit : star psi ⬝ᵥ psi = 1) :
    (machineReducedState psi).charpoly =
      (Polynomial.X - Polynomial.C (1 / 3 : Complex)) *
        (Polynomial.X - Polynomial.C (2 / 3 : Complex)) := by
  rw [Matrix.charpoly_fin_two, machine_reduced_trace psi hUnit,
    machine_reduced_det psi hUnit]
  have hSum :
      Polynomial.C (1 / 3 : Complex) + Polynomial.C (2 / 3 : Complex) = 1 := by
    rw [← Polynomial.C_add]
    norm_num
  have hProduct :
      Polynomial.C (1 / 3 : Complex) * Polynomial.C (2 / 3 : Complex) =
        Polynomial.C (2 / 9 : Complex) := by
    rw [← Polynomial.C_mul]
    norm_num
  calc
    Polynomial.X ^ 2 - Polynomial.C 1 * Polynomial.X + Polynomial.C (2 / 9 : Complex) =
        Polynomial.X ^ 2 -
          (Polynomial.C (1 / 3 : Complex) + Polynomial.C (2 / 3 : Complex)) *
            Polynomial.X +
          Polynomial.C (1 / 3 : Complex) * Polynomial.C (2 / 3 : Complex) := by
      rw [hSum, hProduct, Polynomial.C_1]
    _ = (Polynomial.X - Polynomial.C (1 / 3 : Complex)) *
        (Polynomial.X - Polynomial.C (2 / 3 : Complex)) := by ring

/-- Every normalized input has machine reduced spectrum exactly `{1 / 3, 2 / 3}`. -/
theorem machine_reduced_spectrum
    (psi : QubitState) (hUnit : star psi ⬝ᵥ psi = 1) :
    spectrum Complex (machineReducedState psi) = {(1 / 3 : Complex), (2 / 3 : Complex)} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, machine_reduced_charpoly psi hUnit]
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- Binary entropy in bits, with mathlib's globally defined real logarithm at the endpoints. -/
noncomputable def binaryEntropyBits (p : Real) : Real :=
  -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

/-- The entropy in bits determined by the cloning machine's two eigenvalues. -/
noncomputable def machineEntropy : Real := binaryEntropyBits (1 / 3)

/-- The cloning machine entropy has the exact closed form `logb 2 3 - 2 / 3`. -/
theorem machine_entropy_closed_form :
    machineEntropy = Real.logb 2 3 - 2 / 3 := by
  have hOneThird : Real.logb 2 (1 / 3) = -Real.logb 2 3 := by
    calc
      Real.logb 2 (1 / 3) = Real.logb 2 1 - Real.logb 2 3 :=
        Real.logb_div one_ne_zero (by norm_num)
      _ = -Real.logb 2 3 := by rw [Real.logb_one]; ring
  have hTwoThird : Real.logb 2 (2 / 3) = 1 - Real.logb 2 3 := by
    calc
      Real.logb 2 (2 / 3) = Real.logb 2 2 - Real.logb 2 3 :=
        Real.logb_div (by norm_num) (by norm_num)
      _ = 1 - Real.logb 2 3 := by rw [Real.logb_self_eq_one (by norm_num)]
  have hOneMinus : (1 - (1 / 3 : Real)) = 2 / 3 := by norm_num
  rw [machineEntropy, binaryEntropyBits, hOneThird, hOneMinus, hTwoThird]
  ring

end D5.S3.Quantum.CloningMachine

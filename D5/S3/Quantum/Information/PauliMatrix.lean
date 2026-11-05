/- GID: D5/S3/Quantum/Information/PauliMatrix
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/PauliMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The generic single-qubit Pauli carrier and its matrix representation. -/

/- pauliMatrix: proof_shape: bind-only; escape_witness: none; consumer: B_formula and the
   stabilizer word construction. -/

import D5.S3.Quantum.FiniteDimensional

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

open D5.S3.Quantum.FiniteDimensional

/-! The Pauli carrier is shared by the generic qubit constructions and by the
    stabilizer counterexample source. -/

/-- The single-qubit Pauli labels. -/
inductive Pauli
  | I | X | Y | Z
  deriving DecidableEq

/-- The four Pauli labels form a finite type. -/
instance : Fintype Pauli := ⟨{.I, .X, .Y, .Z}, fun p => by cases p <;> simp⟩

/-- The Pauli matrices: `X`, `Z` are the frozen `qubitX`, `qubitZ`, and `Y = i X Z`. -/
noncomputable def pauliMatrix : Pauli → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => qubitX
  | .Y => Complex.I • (qubitX * qubitZ)
  | .Z => qubitZ

end D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

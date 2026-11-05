/- GID: D5/S3/Quantum/Measurement/Bloch/QubitBloch
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Bloch/QubitBloch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Generic qubit Bloch coordinates used by parent constructions and weighted rays. -/

/- B_formula: proof_shape: bind-only; escape_witness: none; consumer: scalarB_det and the
   weighted-ray effect factorization. -/

import D5.S3.Quantum.Information.Pauli.PauliMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Quantum.Measurement.FourQubitParentConstruction

/-- The real Bloch coordinates multiply the three Pauli matrices. -/
def B (a : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a 0 : ℂ) • pauliMatrix .X + (a 1 : ℂ) • pauliMatrix .Y +
    (a 2 : ℂ) • pauliMatrix .Z

theorem B_formula (a : EuclideanSpace ℝ (Fin 3)) :
    B a = !![(a 2 : ℂ), (a 0 : ℂ) - Complex.I * (a 1 : ℂ);
      (a 0 : ℂ) + Complex.I * (a 1 : ℂ), -(a 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A real scalar identity is added to the traceless Bloch matrix. -/
def scalarB (t : ℝ) (a : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + B a

end D5.S3.Quantum.Measurement.FourQubitParentConstruction

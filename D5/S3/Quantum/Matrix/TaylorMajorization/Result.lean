/- GID: D5/S3/Quantum/Matrix/TaylorMajorization/Result
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/TaylorMajorization/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refutation of unrestricted Taylor weak majorization by the shifted Pauli family. -/

import D5.S3.Quantum.Matrix.TaylorMajorization.Pauli

open Matrix
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Matrix.TaylorMajorization.Defs
open D5.S3.Quantum.Matrix.TaylorMajorization.Pauli

namespace D5.S3.Quantum.Matrix.TaylorMajorization.Result

/-- The unrestricted Hermitian Taylor weak-majorization claim is false. -/
theorem result : ¬ claim := by
  intro h
  have hZ : qubitZ.IsHermitian := qubit_weyl_star.2.2.1
  have hX : qubitX.IsHermitian := qubit_weyl_star.2.1
  have hA : (qubitZ - (1 : ℂ) • 1).IsHermitian :=
    hZ.sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have htr := weakMaj_trace (h 2 (by omega) _ _ hA hX 5 (by omega))
  have hneg := defect_shift_negative 5 (by decide) (by omega) 1 (by norm_num)
  change (taylorR (qubitZ - (1 : ℂ) • 1) qubitX 5).trace.re -
    (((qubitZ - (1 : ℂ) • 1) + qubitX) ^ 5).trace.re < 0 at hneg
  linarith

end D5.S3.Quantum.Matrix.TaylorMajorization.Result

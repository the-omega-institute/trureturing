/- GID: D5/S3/QuantumStates/UnitWeightSupport
   generality: G
   mirror-B: D5/B/S3/QuantumStates/UnitWeightSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit projection weight forces a positive normalized matrix onto that projection. -/

import D5.S3.QuantumStates.ZeroWeightSupportFace

open scoped ComplexOrder MatrixOrder

namespace D5.S3.QuantumStates.UnitWeightSupport

open Matrix

/- The state and projection are source-semantic primitives: positivity, trace, adjointness,
and idempotence are hypotheses, while the compression is the conclusion. -/
/-- A positive trace-one matrix with unit weight on a self-adjoint idempotent is supported
on that projection. -/
theorem unit_weight_support_face
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho P : Matrix n n ℂ)
    (hRho : rho.PosSemidef)
    (hPstar : Matrix.conjTranspose P = P)
    (hPidem : P * P = P)
    (hTrace : Matrix.trace rho = 1)
    (hWeight : Matrix.trace (rho * P) = 1) :
    rho = P * rho * P := by
  let Q : Matrix n n ℂ := 1 - P
  have hQstar : Matrix.conjTranspose Q = Q := by
    dsimp [Q]
    simp [hPstar]
  have hQidem : Q * Q = Q := by
    dsimp [Q]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPidem]; abel
  have hQtrace : Matrix.trace (rho * Q) = 0 := by
    dsimp [Q]
    rw [mul_sub, Matrix.trace_sub]
    simp [hTrace, hWeight]
  have hComplement := D5.S3.QuantumStates.ZeroWeightSupportFace.zero_weight_support_face
    rho Q hRho hQstar hQidem hQtrace
  have hCompression : rho = (1 - Q) * rho * (1 - Q) := hComplement.2
  simpa [Q] using hCompression

#print axioms unit_weight_support_face

end D5.S3.QuantumStates.UnitWeightSupport

/- GID: D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionKernelAntitone
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionKernelAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality at a longer finite time projection implies equality at every shorter horizon. -/

import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/- Library-search audit trail (2026-08-27):
   * Repository searches for `futureReadoutWord` equality and kernel inclusion
     found only the private consecutive-depth proof `forget_latest_respects`
     and the more abstract finite-family theorem `indexed_readout_monotonicity`;
     neither is the arbitrary-horizon public statement below.
   * Exact pinned-Mathlib hits `Fin.castLE`, `Fin.val_castLE`, and
     `Fin.castLE_injective` supply the coordinate embedding used below.
   * Loogle query `Fin.castLE` returned those coordinate tools and `Fin.take`,
     but no equality-kernel theorem specialized to finite time projections. -/

namespace D5.S3.ConceptDynamics.TimeProjection.FiniteTimeProjectionKernelAntitone

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Equality of readout words at a longer horizon restricts to equality at
every shorter horizon. Equivalently, the longer projection's equality kernel
is contained in the shorter projection's equality kernel. -/
theorem finite_time_projection_kernel_antitone
    {X O : Type*} (q : X -> O) (tau : X -> X)
    {N N' : Nat} (h : N <= N') (x y : X)
    (hlong :
      futureReadoutWord tau q N' x =
        futureReadoutWord tau q N' y) :
    futureReadoutWord tau q N x =
      futureReadoutWord tau q N y := by
  funext i
  simpa only [futureReadoutWord, Fin.val_castLE] using
    congrFun hlong (Fin.castLE (Nat.succ_le_succ h) i)

/- Domain-inhabitance witness for the shortest time projection. -/
example : Fin (0 + 1) :=
  ⟨0, Nat.zero_lt_succ 0⟩

/- Hypothesis-satisfiability witness with two distinct underlying states. -/
example :
    false != true /\
      futureReadoutWord Bool.not (fun _ : Bool => ()) 1 false =
        futureReadoutWord Bool.not (fun _ : Bool => ()) 1 true := by
  constructor
  · decide
  · funext i
    rfl

#print axioms finite_time_projection_kernel_antitone

end D5.S3.ConceptDynamics.TimeProjection.FiniteTimeProjectionKernelAntitone

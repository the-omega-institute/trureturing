/- GID: D5/S3/Quantum/Dynamics/ObserverPullbackTraceIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ObserverPullbackTraceIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Iterated channel evolution and Heisenberg pullback have equal trace readouts. -/

import D5.S3.Quantum.Fibers.FutureStatisticsEquivalence

/- Library-search audit trail (2026-08-27):
   * Exact family primitives `QuantumChannel`, `DensityState`, `evolvedState`, and
     `MatrixAlgebra` construct the source channel iterates and finite matrix carrier.
   * The frozen future-statistics module contains the same induction only as a private helper;
     no public D5 declaration exposes the source's single-state iterated trace identity.
   * Repository and pinned-Mathlib searches found no bindable exact theorem. Pinned Mathlib's
     `Function.iterate_succ_apply` and `Function.iterate_succ_apply'` supply the two iterate
     orientations used in the induction. -/

noncomputable section

open scoped CStarAlgebra ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Dynamics.ObserverPullbackTraceIdentity

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.FutureStatisticsEquivalence
open D5.S3.Quantum.Fibers.OperatorSystemTowerStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A trace-dual Heisenberg map pulls every finite channel iterate back to the
initial density state. The effect is an arbitrary matrix, so the identity also
applies to every physical effect on the same carrier. -/
theorem observer_pullback_trace_identity
    (channel : QuantumChannel d d)
    (heisenberg : MatrixAlgebra d →CP MatrixAlgebra d)
    (hduality : ∀ state effect : MatrixAlgebra d,
      Matrix.trace (channel.toCompletelyPositiveMap state * effect) =
        Matrix.trace (state * heisenberg effect))
    (t : Nat) (rho : DensityState d) (effect : MatrixAlgebra d) :
    Matrix.trace ((evolvedState channel t rho).1 * effect) =
      Matrix.trace
        (rho.1 * ((fun A : MatrixAlgebra d => heisenberg A)^[t]) effect) := by
  induction t generalizing effect with
  | zero => rfl
  | succ t ih =>
      calc
        Matrix.trace ((evolvedState channel (t + 1) rho).1 * effect) =
            Matrix.trace
              ((QuantumChannel.mapState channel (evolvedState channel t rho)).1 * effect) := by
          simp only [evolvedState, Function.iterate_succ_apply']
        _ = Matrix.trace
              (channel.toCompletelyPositiveMap (evolvedState channel t rho).1 * effect) := rfl
        _ = Matrix.trace ((evolvedState channel t rho).1 * heisenberg effect) :=
          hduality _ _
        _ = Matrix.trace
              (rho.1 * ((fun A : MatrixAlgebra d => heisenberg A)^[t])
                (heisenberg effect)) := ih (heisenberg effect)
        _ = Matrix.trace
              (rho.1 * ((fun A : MatrixAlgebra d => heisenberg A)^[t + 1]) effect) := by
          rw [Function.iterate_succ_apply]

#print axioms observer_pullback_trace_identity

end D5.S3.Quantum.Dynamics.ObserverPullbackTraceIdentity

/- GID: D5/S3/Observer/HiddenFlow/ContinuousRigidity
   generality: I
   mirror-B: D5/B/S3/Observer/HiddenFlow/ContinuousRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous additive real flows in the observer hidden-address space are trivial. -/

/- Library-search audit trail (2026-08-12):
   * `IsPreconnected.constant`, `PreconnectedSpace.constant`, and
     `TotallyDisconnectedSpace.eq_of_continuous` were found in the pinned mathlib tree.
   * The local theorem `hidden_fiber_rigidity` already packages the needed product instance and
     connected-image argument, so the flow theorem below is a thin additive specialization.
   * `ContinuousAddMonoidHom.ext`, `map_continuous`, and integer casts into `PadicInt` supply the
     bundled-homomorphism interface and the explicit integer-parameter witness.
-/

import D5.S3.Arith.HiddenFiberRigidity
import D5.S3.Observer.StreamlineTheorem
import Mathlib.Topology.Algebra.ContinuousMonoidHom

namespace D5.S3.Observer.HiddenFlow.ContinuousRigidity

open D5.S3.Observer.StreamlineTheorem

/-- A bundled prime supplies the primality fact required by its ring of p-adic integers. -/
private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Every continuous additive real-parameter flow through the observer's hidden
address space is the zero flow. This excludes continuous real flows only; it
does not classify other parameter groups or force them to be discrete. -/
theorem continuous_hidden_flow_eq_zero
    (flow : ContinuousAddMonoidHom ℝ HiddenAddress) : flow = 0 := by
  apply ContinuousAddMonoidHom.ext
  intro t
  have hconstant : flow t = flow 0 :=
    D5.S3.Arith.HiddenFiberRigidity.hidden_fiber_rigidity
      isPreconnected_univ flow (map_continuous flow).continuousOn
      t (by simp) 0 (by simp)
  simpa using hconstant

/-- Canonical integer casting in every p-adic coordinate gives one explicit
additive hidden jump. This is an anti-vacuity witness, not a consequence of the
continuous-flow rigidity theorem. -/
noncomputable def discreteHiddenJump : ℤ →+ HiddenAddress where
  toFun n p := (n : ℤ_[p.1])
  map_zero' := by
    funext p
    simp
  map_add' m n := by
    funext p
    simp

/-- The chosen integer-parameter hidden jump is nonzero: its value at one has
value one in every coordinate. This does not derive discreteness or classify
all nontrivial hidden actions. -/
theorem discreteHiddenJump_ne_zero : discreteHiddenJump ≠ 0 := by
  intro hzero
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hat : (1 : ℤ_[p.1]) = 0 := by
    simpa [discreteHiddenJump] using
      congrArg (fun jump : ℤ →+ HiddenAddress ↦ jump 1 p) hzero
  exact one_ne_zero hat

end D5.S3.Observer.HiddenFlow.ContinuousRigidity

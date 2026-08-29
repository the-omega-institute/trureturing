/- GID: D5/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous solenoid motion stays on one flow line while hidden jumps remain discrete. -/

import D5.S1.Solenoid.PathOrbitClassification
import D5.S3.Observer.HiddenFlow.DiscreteRigidity

/- Library-search audit trail (2026-08-29):
   * Exact frozen hits `path_joined_iff_real_flow_orbit`, `hidden_fiber_rigidity`,
     and `discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension`
     supply the three source clauses and are applied directly below.
   * Current-tree name and body-shape searches found no frozen theorem combining
     path-orbit classification, arbitrary continuous hidden-map rigidity, and the
     canonical nonzero integer jump in one public statement.
   * Pinned Mathlib supplies `Joined`, `IsPreconnected`, and `ContinuousOn`, but no
     universal-solenoid or prime-adic hidden-address dichotomy. The `loogle` and
     `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenCoding.VisibleHiddenMotionDichotomy

open Set
open D5.S1.Dynamics
open D5.S1.Solenoid.PathOrbitClassification
open D5.S3.Observer.StreamlineTheorem
open D5.S3.Observer.HiddenFlow.ContinuousRigidity
open D5.S3.Observer.HiddenFlow.DiscreteRigidity

noncomputable section

/-- Continuous solenoid reachability is exactly one visible real-flow orbit.
On every preconnected real segment a continuous hidden-address history is
constant, while the canonical integer-address action is nonzero and cannot be
the restriction of a continuous additive real flow. -/
theorem visible_path_hidden_address_dichotomy :
    (forall x y : UniversalSolenoid,
      Joined x y ↔ exists t : Real,
        y = UniversalSolenoid.realFlow t + x) ∧
    (forall (segment : Set Real), IsPreconnected segment ->
      forall (offset : Real -> HiddenAddress), ContinuousOn offset segment ->
        forall {first second : Real}, first ∈ segment -> second ∈ segment ->
          offset first = offset second) ∧
    discreteHiddenJump ≠ 0 ∧
    ¬ exists flow : ContinuousAddMonoidHom Real HiddenAddress,
      flow.toAddMonoidHom.comp (Int.castAddHom Real) = discreteHiddenJump := by
  refine ⟨path_joined_iff_real_flow_orbit, ?_,
    discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension⟩
  intro segment preconnected offset continuous first second firstMem secondMem
  exact D5.S3.Arith.HiddenFiberRigidity.hidden_fiber_rigidity
    preconnected offset continuous first firstMem second secondMem

example : UniversalSolenoid := 0
example : HiddenAddress := 0

#print axioms visible_path_hidden_address_dichotomy

end

end D5.S3.Observer.GoldenCoding.VisibleHiddenMotionDichotomy

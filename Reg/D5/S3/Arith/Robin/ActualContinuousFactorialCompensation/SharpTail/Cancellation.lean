import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Cancellation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Cancellation

/- Source-law components for the enrolled DependentFamily.realize template.
The state domains below are infinite; no finite state catalogue is used.
Each law preserves its original telescope and literal arithmetic readout.
Full four-slot registration still requires whole-family variation and
sensitivity, actual observational dependence, and faithful source selectors
with current binding evidence. The residual continuation is unknown.
No Contract.Registration or declared_validated record is asserted. -/

namespace T_epsilon_quadratic_bound

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => T_epsilon) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    |(V.readout () ()) x| ≤ 8 / x ^ 2

private theorem actual_law : arena.Law actual := @T_epsilon_quadratic_bound

private theorem sourceBridge :
    (type_of% (@T_epsilon_quadratic_bound)) ↔ arena.Law actual := Iff.rfl

end T_epsilon_quadratic_bound

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Cancellation

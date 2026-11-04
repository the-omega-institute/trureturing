import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Arithmetic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Arithmetic

/- Source-law components for the enrolled DependentFamily.realize template.
The state domains below are infinite; no finite state catalogue is used.
Each law preserves its original telescope and literal arithmetic readout.
Full four-slot registration still requires whole-family variation and
sensitivity, actual observational dependence, and faithful source selectors
with current binding evidence. The residual continuation is unknown.
No Contract.Registration or declared_validated record is asserted. -/

namespace J_tail_from_slope

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
  realize signature (fun _ _ => J) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    2 * (V.readout () ()) x = (Real.log x) ^ 2 - gamma ^ 2 + alpha +
      2 * Real.log x * epsilon x + 2 * T_epsilon x

private theorem actual_law : arena.Law actual := @J_tail_from_slope

private theorem sourceBridge :
    (type_of% (@J_tail_from_slope)) ↔ arena.Law actual := Iff.rfl

end J_tail_from_slope

namespace G_tail_decomposition

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
  realize signature (fun _ _ => G) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    (V.readout () ()) x = alpha + (1 + gamma) * Int.fract x - eta x +
      x * (1 + gamma + Real.log x) * epsilon x + 2 * x * T_epsilon x

private theorem actual_law : arena.Law actual := @G_tail_decomposition

private theorem sourceBridge :
    (type_of% (@G_tail_decomposition)) ↔ arena.Law actual := Iff.rfl

end G_tail_decomposition

namespace harmonicPrimitive_bound

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
  realize signature (fun _ _ => harmonicPrimitive) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    |(V.readout () ()) x| ≤ 4 / x

private theorem actual_law : arena.Law actual := @harmonicPrimitive_bound

private theorem sourceBridge :
    (type_of% (@harmonicPrimitive_bound)) ↔ arena.Law actual := Iff.rfl

end harmonicPrimitive_bound

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Arithmetic

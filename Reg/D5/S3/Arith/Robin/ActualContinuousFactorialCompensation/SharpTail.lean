import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail

/- Source-law components for the enrolled DependentFamily.realize template.
The state domains below are infinite; no finite state catalogue is used.
Each law preserves its original telescope and literal arithmetic readout.
Full four-slot registration still requires whole-family variation and
sensitivity, actual observational dependence, and faithful source selectors
with current binding evidence. The residual continuation is unknown.
No Contract.Registration or declared_validated record is asserted. -/

namespace G_centered_decomposition

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
    (V.readout () ()) x - ell = (1 + gamma + Real.log x) * harmonicPrimitive x -
      (eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2)) +
      2 * x * T_epsilon x

private theorem actual_law : arena.Law actual := @G_centered_decomposition

private theorem sourceBridge :
    (type_of% (@G_centered_decomposition)) ↔ arena.Law actual := Iff.rfl

end G_centered_decomposition

namespace G_sharp_tail_bound

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
    |(V.readout () ()) x - ell| ≤ (4 * gamma + 24) * (1 + Real.log x) / x

private theorem actual_law : arena.Law actual := @G_sharp_tail_bound

private theorem sourceBridge :
    (type_of% (@G_sharp_tail_bound)) ↔ arena.Law actual := Iff.rfl

end G_sharp_tail_bound

namespace exists_G_sharp_tail_constant

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
  Law V := ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → |(V.readout () ()) x - (alpha + h1 / 2)| ≤
      C * (1 + Real.log x) / x

private theorem actual_law : arena.Law actual := @exists_G_sharp_tail_constant

private theorem sourceBridge :
    (type_of% (@exists_G_sharp_tail_constant)) ↔ arena.Law actual := Iff.rfl

end exists_G_sharp_tail_constant

namespace tendsto_G_ell

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
  Law V := Tendsto (V.readout () ()) atTop (𝓝 (alpha + h1 / 2))

private theorem actual_law : arena.Law actual := @tendsto_G_ell

private theorem sourceBridge :
    (type_of% (@tendsto_G_ell)) ↔ arena.Law actual := Iff.rfl

end tendsto_G_ell

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail

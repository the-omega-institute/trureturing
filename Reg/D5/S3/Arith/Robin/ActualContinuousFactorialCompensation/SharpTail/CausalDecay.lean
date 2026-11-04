import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.CausalDecay
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.CausalDecay

/- Source-law components for the enrolled DependentFamily.realize template.
The state domains below are infinite; no finite state catalogue is used.
Each law preserves its original telescope and literal arithmetic readout.
Full four-slot registration still requires whole-family variation and
sensitivity, actual observational dependence, and faithful source selectors
with current binding evidence. The residual continuation is unknown.
No Contract.Registration or declared_validated record is asserted. -/

namespace r_centered_decay

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
  realize signature (fun _ _ => r) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ} (ht : 0 ≤ t),
    |(V.readout () ()) t - ell * Real.exp (-t / 2)| ≤
      (4 * gamma + 24) * (1 + t) * Real.exp (-3 * t / 2)

private theorem actual_law : arena.Law actual := @r_centered_decay

private theorem sourceBridge :
    (type_of% (@r_centered_decay)) ↔ arena.Law actual := Iff.rfl

end r_centered_decay

namespace r_centered_weighted_integrable

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
  realize signature (fun _ _ => r) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (a : ℝ) (ha : a < 3 / 2),
    IntegrableOn (fun t : ℝ => Real.exp (a * t) *
      ((V.readout () ()) t - ell * Real.exp (-t / 2))) (Ioi 0)

private theorem actual_law : arena.Law actual := @r_centered_weighted_integrable

private theorem sourceBridge :
    (type_of% (@r_centered_weighted_integrable)) ↔ arena.Law actual := Iff.rfl

end r_centered_weighted_integrable

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.CausalDecay

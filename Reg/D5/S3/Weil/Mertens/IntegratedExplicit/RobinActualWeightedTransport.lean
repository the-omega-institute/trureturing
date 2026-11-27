import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTransport
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for positivity of the logarithmic Robin weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTransport

open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ j u => d j u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {j u : ℝ}, 1 ≤ j → 0 < u → 0 ≤ R.readout () j u

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (j := 1) (u := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [actual, realize, d, H, Real.exp_zero]

def family : Registration arena (type_of% (@d_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@d_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@d_nonneg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace.d_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ j u => d j u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTransport

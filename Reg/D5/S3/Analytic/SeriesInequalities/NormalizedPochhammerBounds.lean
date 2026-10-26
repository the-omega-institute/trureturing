import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
open _root_.D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ k => ∑ j ∈ range k, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, R.readout () () k ≤ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @inverse_square_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse_square_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inverse_square_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => ∑ j ∈ range k, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds

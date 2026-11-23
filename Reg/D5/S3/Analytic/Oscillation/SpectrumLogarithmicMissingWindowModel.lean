import Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
import D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel

/-! The weight readout in the infinite logarithmic model. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel

open _root_.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow (HasLogarithmicSquareTail)
open _root_.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel (exists_infinite_logarithmic_model)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SpectrumCriticalMissingWindowModel (weightSignature weightActual weightRejected weightArenaWithTail
  weight_rejected weight_sensitivity weight_dependence)
open LeanInformationAudit

abbrev logarithmicWeightArena : Arena := weightArenaWithTail HasLogarithmicSquareTail

def logarithmicWeightEvidence :
    Registration logarithmicWeightArena (type_of% @exists_infinite_logarithmic_model) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@exists_infinite_logarithmic_model, weightRejected, weight_rejected _⟩
  sensitivity := weight_sensitivity _
  dependence := weight_dependence

def logarithmicWeightAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_infinite_logarithmic_model) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel.logarithmicWeightUnit
  realizationName :=
    `Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel.logarithmicWeightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨logarithmicWeightArena⟩
  objectArena := .source ⟨logarithmicWeightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logarithmicWeightArena ⟨logarithmicWeightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ p j => p.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms logarithmicWeightAudit

end Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel

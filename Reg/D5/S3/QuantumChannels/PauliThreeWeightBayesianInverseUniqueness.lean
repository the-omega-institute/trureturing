import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Evaluate the source Pauli family at its complete index coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 4)
    (fun _ => Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ μ family => family μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both Hermiticity and involutivity, observing the first source matrix. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ : Fin 4,
    (R.readout () μ sigma)ᴴ = sigma μ ∧ sigma μ * sigma μ = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0).1
  change (0 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 at he
  rw [Matrix.conjTranspose_zero] at he
  exact zero_ne_one he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) ≠ 1
  exact zero_ne_one

def source_registration : Registration arena (type_of% @sigma_properties) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sigma_properties, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sigma_properties) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ μ family => family μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness

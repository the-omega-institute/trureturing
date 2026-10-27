import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the entries of the powers of the cyclic shift. -/

namespace Reg.D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation
open _root_.D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The entry indicator of a cyclic shift, with its power and row fixed. -/
abbrev signature : Signature where
  Params := Σ _ : Fin 5, Fin 5
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p j => if p.2 = j + p.1 then 1 else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p i j : Fin 5), (shift ^ p.val) i j = r.readout () ⟨p, i⟩ j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @shift_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shift_power, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@shift_power) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p j => if p.2 = j + p.1 then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation

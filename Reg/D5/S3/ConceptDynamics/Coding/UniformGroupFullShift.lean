import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.UniformGroupFullShift
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.UniformGroupFullShift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.UniformGroupFullShift

universe u

abbrev coefficientSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ b => b) (fun e => nomatch e)

def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

def coefficientArena : Arena where
  signature := coefficientSignature
  Law R := ∀ {H : Type u} [Group H] [Fintype H] [LinearOrder H]
    (n b : Nat) (i j : Fin n) (g : H),
    ((uniformEndpoint (H := H) n b) i j).coeff g = R.readout () () b

theorem coefficient_actual_law : coefficientArena.{u}.Law coefficientActual := by
  intro H group finite ordered n b i j g
  exact uniformEndpoint_coeff n b i j g

theorem coefficient_rejected_law : ¬ coefficientArena.{u}.Law coefficientRejected := by
  intro h
  have bad := h (H := ULift.{u} Unit) 1 1 0 0 1
  rw [uniformEndpoint_coeff] at bad
  exact Nat.one_ne_zero bad

def coefficientRegistration : Registration coefficientArena.{u}
    (type_of% (@uniformEndpoint_coeff.{u})) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨coefficient_actual_law, coefficientRejected, coefficient_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected, ?_, rfl, coefficient_rejected_law⟩
      intro j hji
      exact (hji (by cases j; cases i; rfl)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : Nat), x ≠ y
    exact ⟨(), 0, 1, Nat.zero_ne_one⟩

noncomputable def coefficient_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@uniformEndpoint_coeff.{u})
      (Realization coefficientSignature) Unit Unit := {
  unitName :=
    `D5.S3.ConceptDynamics.Coding.UniformGroupFullShift.uniformEndpoint_coeff.__information_unit,
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.UniformGroupFullShift.coefficientRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨coefficientArena.{u}⟩,
  objectArena := .source ⟨coefficientArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source coefficientArena.{u} ⟨coefficientRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize coefficientSignature (fun _ _ b => b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.UniformGroupFullShift,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms coefficientRegistration

end Reg.D5.S3.ConceptDynamics.Coding.UniformGroupFullShift

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanCompanionMinimality
import Reg.Support.DependentFamily

/-! Source-bound observation of the Boolean product map, with both slice alternatives fixed. -/

namespace Reg.D5.S3.Observer.Separation.BooleanCompanionMinimality

open _root_.D5.S3.Observer.Separation.BooleanCompanionMinimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev Parameters := (A : Type) × (B : Type) × (A → B → Bool)

abbrev signature : Signature where
  Params := Parameters
  State p := p.1 × p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ab => p.2.2 ab.1 ab.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Keep the full source telescope and both slice alternatives; vary the product readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type} [Nonempty A] [Nonempty B] (ψ : A → B → Bool),
    Function.Surjective (fun p : A × B => R.readout () ⟨A, B, ψ⟩ p) ↔
      ((∃ b, Function.Surjective (fun a => ψ a b)) ∨
        (∃ a, Function.Surjective (fun b => ψ a b)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible := (@h Bool Unit inferInstance inferInstance (fun a _ => a)).mpr
    (Or.inl ⟨(), fun z => ⟨z, rfl⟩⟩)
  obtain ⟨p, hp⟩ := impossible true
  exact Bool.noConfusion hp

def source_registration : Registration arena (type_of% @binary_effective_image_surjective_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binary_effective_image_surjective_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Bool, Unit, fun a _ => a⟩, (false, ()), (true, ()), ?_⟩
    exact Bool.noConfusion

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@binary_effective_image_surjective_iff) (Realization signature) Unit Unit := {
  unitName := .str
    `D5.S3.Observer.Separation.BooleanCompanionMinimality.binary_effective_image_surjective_iff
    "__information_unit"
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanCompanionMinimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p ab => p.2.2 ab.1 ab.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Separation.BooleanCompanionMinimality
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration

end Reg.D5.S3.Observer.Separation.BooleanCompanionMinimality

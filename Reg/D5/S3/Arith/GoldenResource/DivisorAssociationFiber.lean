import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.DivisorAssociationFiber
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.GoldenResource.DivisorAssociationFiber

open _root_.D5.S3.Arith.GoldenResource.DivisorAssociationFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Sigma (fun _ : ℕ => Sigma (fun _ : ℕ => ℕ))
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p A => ((box A p.1 p.2.1 p.2.2).image q).card)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ A B C D : ℕ,
    r.readout () ⟨B, ⟨C, D⟩⟩ A =
      (B + 1) * ((A + 1) * (C + 1) + D * (A + C + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h 0 0 0 0
  norm_num [rejected, realize] at ht

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _i
  refine ⟨⟨0, ⟨0, 0⟩⟩, 0, 1, ?_⟩
  change ((box 0 0 0 0).image q).card ≠ ((box 1 0 0 0).image q).card
  rw [image_card, image_card]
  decide

def family : Registration arena (type_of% image_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨image_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    image_card (type_of% (realize signature
      (fun _ p A => ((box A p.1 p.2.1 p.2.2).image q).card) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.GoldenResource.DivisorAssociationFiber.image_card.__information_unit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.DivisorAssociationFiber.family
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
    (fun _ p A => ((box A p.1 p.2.1 p.2.2).image q).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.DivisorAssociationFiber
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.GoldenResource.DivisorAssociationFiber

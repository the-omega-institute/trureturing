import Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
import D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion

/-! A source-bound audit of the complete guarded-toggle commutation criterion. -/

namespace Reg.D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open _root_.D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion
open _root_.Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles

noncomputable section
universe u

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {P : Type u} [order : PartialOrder P] (x y : P),
    (∀ S : Set P, S.OrdConnected →
      R.readout () ⟨P, order, x⟩ (toggle y S) = toggle y (toggle x S)) ↔
    x = y ∨ (¬ x ≤ y ∧ ¬ y ≤ x) ∨
      (IsMin x ∧ IsMax y ∧ x ⋖ y) ∨
      (IsMin y ∧ IsMax x ∧ y ⋖ x)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let P := ULift.{u} Unit
  let x : P := ⟨()⟩
  have bad := ((@h P (equalityOrder P) x x).mpr (Or.inl rfl))
    ∅ (equalityOrder_connected ∅)
  have member := congrArg (fun T : Set P => x ∈ T) bad
  simp [rejected, realize, toggle, equalityOrder_connected, Set.mem_symmDiff,
    x] at member

def source_registration :
    Registration arena.{u} (type_of% @toggles_commute_iff.{u}) where
  actual := realize signature.{u} observed.{u} noAnchor.{u}
  bridge := Iff.rfl
  variation := ⟨@toggles_commute_iff.{u}, rejected, rejected_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@toggles_commute_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} observed.{u} noAnchor.{u})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion

import D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift
import Reg.D5.S3.Combinatorics.Circle.ThreeNegativeSmallestALargestBJointLift

/-! The original three coordinates and both physical source readouts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift
open _root_.Reg.D5.S3.Combinatorics.Circle.ThreeNegativeSmallestALargestBJointLift
open private actual_dependence
  from Reg.D5.S3.Combinatorics.Circle.ThreeNegativeSmallestALargestBJointLift

noncomputable section

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : ℕ) (_ha : 2 ≤ a) (_hab : a = b) (_hbc : b < c),
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ, j ≤ a + b + c ∧
      R.readout false ⟨a, b, c⟩ (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      R.readout true ⟨a, b, c⟩ (2 * (1 + 2 ^ a + 2 ^ (a + b))) (earWord (a + b + c) sigma j)

private theorem actual_law : arena.Law actual := by
  intro a b c ha hab hbc
  exact actualSource_three_negative_equal_inner_large_c_joint_lift a b c ha hab hbc

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, j, hj, hold, hnew⟩ := h 2 2 3 (by decide) rfl (by decide)
  simp [rejected, realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma, j, hj, hold, hnew⟩ := h 2 2 3 (by decide) rfl (by decide)
  cases side
  · simp [deleted, rejected, realize] at hold
  · simp [deleted, rejected, realize] at hnew

def source_registration : Registration arena
    (type_of% (@actualSource_three_negative_equal_inner_large_c_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side, ?_, rfl, deleted_law side⟩
      intro j hj
      simp [deleted, realize, hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift.actualSource_three_negative_equal_inner_large_c_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift.actualSource_three_negative_equal_inner_large_c_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift

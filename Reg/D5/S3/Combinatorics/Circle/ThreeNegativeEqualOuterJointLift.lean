import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact two-readout registration for the complete marked equal-outer joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

noncomputable section

abbrev Params := Σ a : ℕ, Σ b : ℕ, List (Fin (a + b + a))

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def orderPredicate (side : Bool) (p : Params) (seed : ℕ) : Prop :=
  match side with
  | false => OriginalOrder (p.1 + p.2.1 + p.1) seed p.2.2
  | true => OriginalOrder (p.1 + p.2.1 + p.1 + 1) seed
      (earWord (p.1 + p.2.1 + p.1) p.2.2 (p.1 + 1))

def actual : Realization signature :=
  realize signature (fun side p seed =>
    @decide (orderPredicate side p seed) (Classical.propDecidable _)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed => if j = side then false else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ) (_ha : 2 ≤ a) (_hab : a < b),
    ∃ sigma : List (Fin (a + b + a)),
      R.readout false ⟨a, b, sigma⟩ (1 + 2 ^ a + 2 ^ (a + b)) = true ∧
      R.readout true ⟨a, b, sigma⟩ (2 * (1 + 2 ^ a + 2 ^ (a + b))) = true

private theorem actual_law : arena.Law actual := by
  intro a b ha hab
  obtain ⟨sigma, hold, hnew⟩ := actualSource_three_negative_equal_outer_joint_lift a b ha hab
  refine ⟨sigma, ?_, ?_⟩ <;> simp [actual, realize, orderPredicate, hold, hnew]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, hold, _⟩ := h 2 3 (by decide) (by decide)
  simp [rejected, realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma, hold, hnew⟩ := h 2 3 (by decide) (by decide)
  cases side
  · simp [deleted, realize] at hold
  · simp [deleted, realize] at hnew

private def identityWord : List (Fin 7) := List.finRange 7

private theorem zero_old : OriginalOrder 7 0 identityWord := by
  have hf : actualSource 7 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem zero_new : OriginalOrder 8 0 (earWord 7 identityWord 3) := by
  have hf : actualSource 8 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨by decide, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem bad_old : ¬ OriginalOrder 7 2 identityWord := by
  intro h
  have hh := h.2.2 6
  norm_num [identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 8 1 (earWord 7 identityWord 3) := by
  intro h
  have hh := h.2.2 4
  norm_num [earWord, identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2, 3, identityWord⟩, 0, 2, ?_⟩
    simp [actual, realize, orderPredicate, zero_old, bad_old]
  · refine ⟨⟨2, 3, identityWord⟩, 0, 1, ?_⟩
    simp [actual, realize, orderPredicate, zero_new, bad_new]

def source_registration : Registration arena
    (type_of% (@actualSource_three_negative_equal_outer_joint_lift)) where
  actual := actual
  bridge := by
    classical
    simp [actual, realize, orderPredicate]
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

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift)
    (type_of% (realize signature (fun side p seed =>
      @decide (orderPredicate side p seed) (Classical.propDecidable _)) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun side p seed =>
    @decide (orderPredicate side p seed) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }, {
      path := #["body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

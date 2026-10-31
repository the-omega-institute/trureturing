import D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift
import Batteries.Tactic.OpenPrivate
import Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact two-readout registration for the complete ordered-cone physical joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift

noncomputable section

abbrev Params := Σ _ : ℕ, Σ _ : ℕ, ℕ

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (p.1 + p.2.1 + p.2.2)) → Prop
    | true => List (Fin (p.1 + p.2.1 + p.2.2 + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (p.1 + p.2.1 + p.2.2) seed
    | true => OriginalOrder (p.1 + p.2.1 + p.2.2 + 1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed => if j = side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : ℕ) (_ha : 2 ≤ a) (_hab : a < b) (_hbc : b ≤ c),
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ,
      j ≤ a + b + c ∧
      R.readout false ⟨a, b, c⟩ (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      R.readout true ⟨a, b, c⟩ (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + c) sigma j)

private theorem actual_law : arena.Law actual := by
  exact actualSource_three_negative_ordered_cone_joint_lift

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, j, hj, hold, hnew⟩ := h 3 2 4 (by decide) (by decide) (by decide)
  simp [rejected, realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma, j, hj, hold, hnew⟩ := h 3 2 4 (by decide) (by decide) (by decide)
  cases side
  · simp [deleted, rejected, realize] at hold
  · simp [deleted, rejected, realize] at hnew

open private identityWord zero_old zero_new bad_old bad_new from
  Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2, 3, 2⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 7 0 identityWord = OriginalOrder 7 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2, 3, 2⟩, 0, 1, ?_⟩
    intro he
    have hp := congrFun he (earWord 7 identityWord 3)
    change OriginalOrder 8 0 (earWord 7 identityWord 3) =
      OriginalOrder 8 1 (earWord 7 identityWord 3) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_three_negative_ordered_cone_joint_lift)) where
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

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift.actualSource_three_negative_ordered_cone_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift.actualSource_three_negative_ordered_cone_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift
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

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift

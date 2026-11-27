import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact two-readout registration for the complete minimum-two marked joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

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
  Law R := ∀ (a b c : ℕ) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c)
      (_hmin : min a (min b c)=2),
    ∃ sigma : List (Fin (a+b+c)), ∃ j : ℕ, j≤a+b+c ∧
      R.readout false ⟨a,b,c⟩ (1+2^a+2^(a+b)) sigma ∧
      R.readout true ⟨a,b,c⟩ (2*(1+2^a+2^(a+b))) (earWord (a+b+c) sigma j)

private theorem actual_law : arena.Law actual := by
  intro a b c ha hb hc hmin
  exact actualSource_three_negative_minimum_two_joint_lift a b c ha hb hc hmin

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,hj,hold,hnew⟩ := h 2 2 2 (by decide) (by decide) (by decide) (by decide)
  simp [rejected,realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,j,hj,hold,hnew⟩ := h 2 2 2 (by decide) (by decide) (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

private def identityWord : List (Fin 6) := List.finRange 6

private theorem zero_old : OriginalOrder 6 0 identityWord := by
  have hf : actualSource 6 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem zero_new : OriginalOrder 7 0 (earWord 6 identityWord 0) := by
  have hf : actualSource 7 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨by decide, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem bad_old : ¬ OriginalOrder 6 2 identityWord := by
  intro h
  have hh := h.2.2 5
  norm_num [identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 7 1 (earWord 6 identityWord 0) := by
  intro h
  have hh := h.2.2 1
  norm_num [earWord, identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2, 2, 2⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 6 0 identityWord = OriginalOrder 6 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2, 2, 2⟩, 0, 1, ?_⟩
    intro he
    have hp := congrFun he (earWord 6 identityWord 0)
    change OriginalOrder 7 0 (earWord 6 identityWord 0) =
      OriginalOrder 7 1 (earWord 6 identityWord 0) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_three_negative_minimum_two_joint_lift)) where
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
    (@_root_.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift.actualSource_three_negative_minimum_two_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift.actualSource_three_negative_minimum_two_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
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

namespace PairedChains

noncomputable section

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p => match side with
    | false => fun i => centered (modulus (p.1 + p.2.1 + p.2.2))
        ((2 : ℤ) ^ i * (1 + (2 : ℤ) ^ p.1 + (2 : ℤ) ^ p.1 * (2 : ℤ) ^ p.2.1))
    | true => fun i => centered (modulus (p.1 + p.2.1 + p.2.2 + 1))
        ((2 : ℤ) ^ i * (2 * (1 + (2 : ℤ) ^ p.1 + (2 : ℤ) ^ p.1 * (2 : ℤ) ^ p.2.1))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature
    (fun j p i => if j = side then rejected.readout j p i else actual.readout j p i)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : ℕ) (_ha : 2 ≤ a) (_hb : 2 ≤ b) (_hc : 2 ≤ c),
    let r : ℤ := 2 ^ a
    let s : ℤ := 2 ^ b
    let t : ℤ := 2 ^ c
    let k := a + b + c
    let N := modulus k
    let v := 1 + r + r * s
    let B := 1 + t + t * r
    let L := 1 + s + s * t
    let f := R.readout false ⟨a, b, c⟩
    let g := R.readout true ⟨a, b, c⟩
    (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
      (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
      (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧
        g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
      (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
        g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
      f (c - 1) = -(N - B) / 2 ∧ f (c + b - 1) = -(N - L) / 2 ∧
      f (k - 1) = -(N - v) / 2 ∧
      g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
      g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
      g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v

private theorem actual_law : arena.Law actual := by
  intro a b c ha hb hc
  exact paired_chains a b c ha hb hc

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 2 2 2 (by decide) (by decide) (by decide)
  norm_num [rejected, realize, modulus] at h0

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  have h0 := h 2 2 2 (by decide) (by decide) (by decide)
  cases side <;> norm_num [deleted, rejected, realize, modulus] at h0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  refine ⟨⟨2, 2, 2⟩, 0, 1, ?_⟩
  cases side <;> norm_num [actual, realize, centered, modulus]

def source_registration : Registration arena (type_of% (@paired_chains)) where
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
    (@_root_.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift.paired_chains)
    (type_of% (realize signature actual.readout actual.anchor))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift.paired_chains.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift.PairedChains.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
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

end PairedChains

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

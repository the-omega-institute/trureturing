import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift
import Reg.Support.DependentFamily

/-! The two roles observe the native old and new order predicates. Both retain
their physical words, zero totals and every prefix at the literal first cut for every d>=2 and m>=1. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output role p := match role with
    | false => List (Fin (p.1 * p.2)) → Prop
    | true => List (Fin (p.1 * p.2 + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role p => match role with
    | false => OriginalOrder (p.1 * p.2)
    | true => OriginalOrder (p.1 * p.2 + 1))
    (fun e => nomatch e)

def reject_old : Realization signature :=
  realize signature (fun role p => match role with
    | false => fun _ _ => False
    | true => OriginalOrder (p.1 * p.2 + 1)) (fun e => nomatch e)

def reject_new : Realization signature :=
  realize signature (fun role p => match role with
    | false => OriginalOrder (p.1 * p.2)
    | true => fun _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d m : ℕ, 2 ≤ d → 1 ≤ m →
    let k := d * m
    let t := (2 ^ (d * m) - 1) / (2 ^ d - 1)
    R.readout false ⟨d,m⟩ t (List.finRange k) ∧
      R.readout true ⟨d,m⟩ (2*t) (earWord k (List.finRange k) 0)

private theorem reject_old_law : ¬ arena.Law reject_old := by
  intro h
  exact (h 2 1 (by omega) (by omega)).1

private theorem reject_new_law : ¬ arena.Law reject_new := by
  intro h
  exact (h 2 1 (by omega) (by omega)).2

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role with
  | false =>
    refine ⟨⟨3,1⟩, 0, 1, ?_⟩
    intro he
    have hz : OriginalOrder 3 0 [2,1,0] := by
      refine ⟨by decide, ?_, ?_⟩
      · norm_num [actualSource, centered, modulus]
      · intro n
        simp [actualSource, centered, modulus]
        change 0 ≤ (List.take n (List.replicate 3 (0 : ℤ))).sum ∧
          (List.take n (List.replicate 3 (0 : ℤ))).sum ≤ 3
        simp only [List.take_replicate, List.sum_replicate, smul_zero]
        omega
    have hh : OriginalOrder 3 1 [2,1,0] := (congrFun he [2,1,0]).mp hz
    have hp := (hh.2.2 1).1
    norm_num [actualSource, centered, modulus] at hp
  | true =>
    refine ⟨⟨3,1⟩, 0, 1, ?_⟩
    intro he
    have hz : OriginalOrder 4 0 [3,2,1,0] := by
      refine ⟨by decide, ?_, ?_⟩
      · norm_num [actualSource, centered, modulus]
      · intro n
        simp [actualSource, centered, modulus]
        change 0 ≤ (List.take n (List.replicate 4 (0 : ℤ))).sum ∧
          (List.take n (List.replicate 4 (0 : ℤ))).sum ≤ 7
        simp only [List.take_replicate, List.sum_replicate, smul_zero]
        omega
    have hh : OriginalOrder 4 1 [3,2,1,0] := (congrFun he [3,2,1,0]).mp hz
    have hp := (hh.2.2 1).1
    norm_num [actualSource, centered, modulus] at hp

def source_registration : Registration arena
    (type_of%
      (@periodic_first_ear_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨periodic_first_ear_joint_lift, reject_old, reject_old_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i with
      | false =>
        refine ⟨reject_old, ?_, rfl, reject_old_law⟩
        intro j hji
        cases j with
        | false => exact False.elim (hji rfl)
        | true => rfl
      | true =>
        refine ⟨reject_new, ?_, rfl, reject_new_law⟩
        intro j hji
        cases j with
        | false => rfl
        | true => exact False.elim (hji rfl)
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@periodic_first_ear_joint_lift)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift.periodic_first_ear_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift.source_registration
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
    (fun role p => match role with
      | false => OriginalOrder (p.1 * p.2)
      | true => OriginalOrder (p.1 * p.2 + 1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift

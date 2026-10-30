import D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! # Exact source-family registration of the same-cut physical repetition lift -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift

noncomputable section

abbrev Params := Σ d : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : List (Fin d), ℕ

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (p.1 * p.2.2.1)) → Prop
    | true => List (Fin (p.1 * p.2.2.1 + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (p.1 * p.2.2.1) seed
    | true => OriginalOrder (p.1 * p.2.2.1 + 1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun r p seed =>
    if r = side then rejected.readout r p seed else actual.readout r p seed) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d w m : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (j : ℕ) (hj : j ≤ d)
    (hold : OriginalOrder d w alpha)
    (hnew : OriginalOrder (d + 1) (2 * w) (earWord d alpha j)),
    R.readout false ⟨d, w, m, alpha, j⟩ (w * geom d m) (repeatedWord d m hm alpha) ∧
      R.readout true ⟨d, w, m, alpha, j⟩ (2 * (w * geom d m))
        (earWord (d * m) (repeatedWord d m hm alpha) j)

private theorem base_old : OriginalOrder 2 1 [0, 1] := by
  refine ⟨by decide, by decide, ?_⟩
  intro n
  have hh := inStrip_prefix (f := actualSource 2 1) (B := 1) (h := 0)
    (l := [0, 1]) (by norm_num [InStrip, actualSource, centered, modulus]) n
  simpa [modulus] using hh

private theorem base_new : OriginalOrder 3 2 (earWord 2 [0, 1] 1) := by
  refine ⟨by decide, by decide, ?_⟩
  intro n
  have hh := inStrip_prefix (f := actualSource 3 2) (B := 3) (h := 0)
    (l := earWord 2 [0, 1] 1) (by norm_num [earWord, InStrip, actualSource, centered, modulus]) n
  simpa [modulus] using hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 1 2 (by decide) (by decide) (by decide) (by decide)
    [0, 1] 1 (by decide) base_old base_new
  exact hh.1

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  have hh := h 2 1 2 (by decide) (by decide) (by decide) (by decide)
    [0, 1] 1 (by decide) base_old base_new
  cases side
  · simpa [deleted, rejected, realize] using hh.1
  · simpa [deleted, rejected, realize] using hh.2

private def identityWord : List (Fin 4) := List.finRange 4

private theorem zero_old : OriginalOrder 4 0 identityWord := by
  have hf : actualSource 4 0 = fun _ => (0 : ℤ) := by
    funext i; fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [hf]
  · intro n; simp [hf, modulus]

private theorem zero_new : OriginalOrder 5 0 (earWord 4 identityWord 0) := by
  have hf : actualSource 5 0 = fun _ => (0 : ℤ) := by
    funext i; fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨by decide, ?_, ?_⟩
  · simp [hf]
  · intro n; simp [hf, modulus]

private theorem bad_old : ¬ OriginalOrder 4 2 identityWord := by
  intro h
  have hh := h.2.2 3
  norm_num [identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 5 1 (earWord 4 identityWord 0) := by
  intro h
  have hh := h.2.2 1
  norm_num [earWord, identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2, 1, 2, [0, 1], 1⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 4 0 identityWord = OriginalOrder 4 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2, 1, 2, [0, 1], 1⟩, 0, 1, ?_⟩
    intro he
    have hp := congrFun he (earWord 4 identityWord 0)
    change OriginalOrder 5 0 (earWord 4 identityWord 0) =
      OriginalOrder 5 1 (earWord 4 identityWord 0) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena (type_of% (@periodic_repetition_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨periodic_repetition_joint_lift, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side, ?_, rfl, deleted_law side⟩
      intro r hr
      simp [deleted, realize, hr]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift.periodic_repetition_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift.periodic_repetition_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift
    definition := none
    coordinates := #[0, 1, 2, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift

import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact eight-binder, four-coordinate dependent-family mirror bound to
actualSource_first_peak_saddle_joint_lift itself. Both actual OriginalOrder
readouts, source equivalence, family laws, variation, sensitivity and
observational dependence are included. The audit has no endpoint argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle

noncomputable section

/-- Exactly four natural binders and four original order hypotheses. -/
private abbrev Endpoint : Prop :=
  ∀ (a b c d : ℕ) (_hc : 2≤c) (_hcd : c<d) (_hdb : d<b) (_hba : b<a),
    ∃ sigma : List (Fin (a+b+c+d)), ∃ cut : ℕ, cut≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut)

private abbrev Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

private abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  -- The declared role order agrees with the old/new source occurrence order.
  finiteRole := ⟨⟨{false, true}, by simp⟩, fun side => by cases side <;> simp⟩
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (p.1 + p.2.1 + p.2.2.1 + p.2.2.2)) → Prop
    | true => List (Fin (p.1 + p.2.1 + p.2.2.1 + p.2.2.2 + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (p.1 + p.2.1 + p.2.2.1 + p.2.2.2) seed
    | true => OriginalOrder (p.1 + p.2.1 + p.2.2.1 + p.2.2.2 + 1) seed) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

private def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed => if j = side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_hc : 2≤c) (_hcd : c<d) (_hdb : d<b) (_hba : b<a),
    ∃ sigma : List (Fin (a+b+c+d)), ∃ cut : ℕ, cut≤a+b+c+d ∧
      R.readout false ⟨a,b,c,d⟩ (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      R.readout true ⟨a,b,c,d⟩ (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut)

private theorem source_equivalence : Endpoint ↔ arena.Law actual := Iff.rfl

private theorem actual_law : arena.Law actual :=
  source_equivalence.mp actualSource_first_peak_saddle_joint_lift

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma,cut,hcut,hold,hnew⟩ := h 5 4 2 3 (by decide) (by decide) (by decide) (by decide)
  simp [rejected,realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma,cut,hcut,hold,hnew⟩ := h 5 4 2 3 (by decide) (by decide) (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

private def identityWord : List (Fin 14) := List.finRange 14

private theorem zero_old : OriginalOrder 14 0 identityWord := by
  have hf : actualSource 14 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem zero_new : OriginalOrder 15 0 (earWord 14 identityWord 0) := by
  have hf : actualSource 15 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨by decide, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem bad_old : ¬ OriginalOrder 14 2 identityWord := by
  intro h
  have hh := h.2.2 13
  norm_num [identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 15 1 (earWord 14 identityWord 0) := by
  intro h
  have hh := h.2.2 1
  norm_num [earWord, identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨5, 4, 2, 3⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 14 0 identityWord = OriginalOrder 14 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨5, 4, 2, 3⟩, 0, 1, ?_⟩
    intro he
    have hp := congrFun he (earWord 14 identityWord 0)
    change OriginalOrder 15 0 (earWord 14 identityWord 0) =
      OriginalOrder 15 1 (earWord 14 identityWord 0) at hp
    exact bad_new (hp.mp zero_new)

private def source_registration : Registration arena
    (type_of% (@actualSource_first_peak_saddle_joint_lift)) where
  actual := actual
  bridge := source_equivalence
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
    _root_.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.actualSource_first_peak_saddle_joint_lift
    (type_of% (realize signature actual.readout actual.anchor))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.actualSource_first_peak_saddle_joint_lift.__information_unit
  realizationName := ``source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
    definition := none
    coordinates := #[0, 1, 2, 3]
    -- Bool.false selects the old occurrence; Bool.true selects the enlarged occurrence.
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end

end Reg.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle

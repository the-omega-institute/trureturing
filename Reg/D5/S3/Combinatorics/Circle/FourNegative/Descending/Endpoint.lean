import D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact eight-binder, four-coordinate source registration, retaining the literal cut d. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.Descending

noncomputable section

abbrev Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (p.1 + p.2.1 + p.2.2.1 + p.2.2.2)) → Prop
    | true => List (Fin (p.1 + p.2.1 + p.2.2.1 + p.2.2.2 + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (p.1 + p.2.1 + p.2.2.1 + p.2.2.2) seed
    | true => OriginalOrder (p.1 + p.2.1 + p.2.2.1 + p.2.2.2 + 1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed => if j = side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_hd : 2 ≤ d) (_hdc : d < c) (_hcb : c ≤ b) (_hba : b < a),
    ∃ sigma : List (Fin (a + b + c + d)),
      R.readout false ⟨a, b, c, d⟩ (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧
      R.readout true ⟨a, b, c, d⟩ (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + d) sigma d)

private theorem actual_law : arena.Law actual := by
  intro a b c d hd hdc hcb hba
  obtain ⟨sigma, hold, hnew⟩ := actualSource_descending_joint_lift a b c d hd hdc hcb hba
  exact ⟨sigma, hold, hnew⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, hold, _⟩ := h 4 3 3 2 (by decide) (by decide) (by decide) (by decide)
  simp [rejected, realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma, hold, hnew⟩ := h 4 3 3 2 (by decide) (by decide) (by decide) (by decide)
  cases side
  · simp [deleted, rejected, realize] at hold
  · simp [deleted, rejected, realize] at hnew

private def identityWord : List (Fin 12) := List.finRange 12

private theorem zero_old : OriginalOrder 12 0 identityWord := by
  have hf : actualSource 12 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem zero_new : OriginalOrder 13 0 (earWord 12 identityWord 2) := by
  have hf : actualSource 13 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨by decide, ?_, ?_⟩
  · simp [hf]
  · intro n
    simp [hf, modulus]

private theorem bad_old : ¬ OriginalOrder 12 2 identityWord := by
  intro h
  have hh := h.2.2 11
  norm_num [identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 13 1 (earWord 12 identityWord 2) := by
  intro h
  have hh := h.2.2 3
  norm_num [earWord, identityWord, List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨4, 3, 3, 2⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he identityWord
    change OriginalOrder 12 0 identityWord = OriginalOrder 12 2 identityWord at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨4, 3, 3, 2⟩, 0, 1, ?_⟩
    intro he
    have hp := congrFun he (earWord 12 identityWord 2)
    change OriginalOrder 13 0 (earWord 12 identityWord 2) =
      OriginalOrder 13 1 (earWord 12 identityWord 2) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_descending_joint_lift)) where
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
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.Descending.actualSource_descending_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.Descending.actualSource_descending_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
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

end Reg.D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

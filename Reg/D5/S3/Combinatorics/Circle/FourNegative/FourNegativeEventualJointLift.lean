import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Four independent source coordinates and a common old/new physical witness. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
noncomputable section

abbrev Params := Σ _a : ℕ, Σ _b : ℕ, Σ _c : ℕ, ℕ
private def size (p : Params) : ℕ := p.1 + p.2.1 + p.2.2.1 + p.2.2.2
abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (size p)) → Prop
    | true => List (Fin (size p + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (size p) seed
    | true => OriginalOrder (size p + 1) seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed =>
    if j = side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_ha : 2 ≤ a) (_hb : 2 ≤ b) (_hc : 2 ≤ c)
      (_hd : a + b + c + 3 ≤ d),
    ∃ sigma : List (Fin (a + b + c + d)), ∃ j : ℕ,
      j ≤ a + b + c + d ∧
      R.readout false ⟨a, b, c, d⟩ (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧
      R.readout true ⟨a, b, c, d⟩ (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + d) sigma j)

private theorem actual_law : arena.Law actual := by
  intro a b c d ha hb hc hd
  exact actualSource_four_negative_eventual_joint_lift a b c d ha hb hc hd

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, j, _, hold, _⟩ := h 2 2 2 9 (by decide) (by decide) (by decide) (by decide)
  simp [rejected, realize] at hold

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  obtain ⟨sigma, j, _, hold, hnew⟩ := h 2 2 2 9 (by decide) (by decide) (by decide) (by decide)
  cases side
  · simp [deleted, rejected, realize] at hold
  · simp [deleted, rejected, realize] at hnew

private theorem zero_old : OriginalOrder 15 0 (List.finRange 15) := by
  have hf : actualSource 15 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  have hz (xs : List (Fin 15)) : (xs.map (actualSource 15 0)).sum = 0 := by
    rw [hf]
    induction xs <;> simp_all
  refine ⟨List.Perm.refl _, hz _, ?_⟩
  intro n
  rw [hz]
  norm_num [modulus]

private theorem zero_new : OriginalOrder 16 0 (List.finRange 16) := by
  have hf : actualSource 16 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  have hz (xs : List (Fin 16)) : (xs.map (actualSource 16 0)).sum = 0 := by
    rw [hf]
    induction xs <;> simp_all
  refine ⟨List.Perm.refl _, hz _, ?_⟩
  intro n
  rw [hz]
  norm_num [modulus]

private theorem bad_old : ¬ OriginalOrder 15 2 (List.finRange 15) := by
  intro h
  have hh := h.2.2 14
  norm_num [List.finRange_succ, actualSource, centered, modulus] at hh

private theorem bad_new : ¬ OriginalOrder 16 2 (List.finRange 16) := by
  intro h
  have hh := h.2.2 15
  norm_num [List.finRange_succ, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2, 2, 2, 9⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he (List.finRange 15)
    change OriginalOrder 15 0 (List.finRange 15) = OriginalOrder 15 2 (List.finRange 15) at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2, 2, 2, 9⟩, 0, 2, ?_⟩
    intro he
    have hp := congrFun he (List.finRange 16)
    change OriginalOrder 16 0 (List.finRange 16) = OriginalOrder 16 2 (List.finRange 16) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_four_negative_eventual_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side, ?_, rfl, deleted_law side⟩
      intro j hj; simp [deleted, realize, hj]
    · intro e; exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift.actualSource_four_negative_eventual_joint_lift)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift.actualSource_four_negative_eventual_joint_lift.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

import D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Repetition
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.PhysicalJointRepetition

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.PhysicalJointRepetition

abbrev Input := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

abbrev signature : Signature where
  Params := Input
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
  realize signature
    (fun side p seed => match side with
      | false =>
          OriginalOrder (p.1 * p.2.2.1) seed
      | true =>
          OriginalOrder (p.1 * p.2.2.1 + 1) seed)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature
    (fun j p seed => if h : j = side then h ▸ rejected.readout side p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d w r cut : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
      (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (hcut : cut ≤ d)
      (tau : List (Fin d)),
    OriginalOrder d w tau →
    OriginalOrder (d + 1) (2 * w) (earWord d tau cut) →
    R.readout false ⟨d, w, r, cut⟩ (w * geom d r)
        (repeatWord d r (Nat.zero_lt_of_lt hr) tau) ∧
      R.readout true ⟨d, w, r, cut⟩ (2 * (w * geom d r))
        (earWord (d * r)
          (repeatWord d r (Nat.zero_lt_of_lt hr) tau) cut)

private theorem actual_law : arena.Law actual := by
  intro d w r cut hd hw0 hw hr hcut tau hold hnew
  simpa [actual, realize] using
    (physical_joint_repetition d w r cut hd hw0 hw hr hcut tau hold hnew)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hold : OriginalOrder 2 1 [0, 1] := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    cases n with
    | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
    | succ n =>
        cases n <;> norm_num [OriginalOrder, actualSource, centered, modulus]
  have hnew : OriginalOrder 3 2 (earWord 2 [0, 1] 0) := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    cases n with
    | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
    | succ n =>
        cases n with
        | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
        | succ n =>
            cases n with
            | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
            | succ n => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
  simpa [rejected, realize] using
    (h 2 1 2 0 (by omega) (by omega) (by omega) (by omega) (by omega)
      [0, 1] hold hnew)

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  have hold : OriginalOrder 2 1 [0, 1] := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    cases n with
    | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
    | succ n =>
        cases n <;> norm_num [OriginalOrder, actualSource, centered, modulus]
  have hnew : OriginalOrder 3 2 (earWord 2 [0, 1] 0) := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    cases n with
    | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
    | succ n =>
        cases n with
        | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
        | succ n =>
            cases n with
            | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
            | succ n => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
  cases side with
  | false =>
      have hh := (h 2 1 2 0 (by omega) (by omega) (by omega) (by omega) (by omega)
        [0, 1] hold hnew).1
      dsimp [deleted, rejected, actual, realize] at hh
  | true =>
      have hh := (h 2 1 2 0 (by omega) (by omega) (by omega) (by omega) (by omega)
        [0, 1] hold hnew).2
      dsimp [deleted, rejected, actual, realize] at hh

private theorem source_bridge :
    (type_of% (@physical_joint_repetition)) ↔ arena.Law actual := by
  constructor
  · intro h d w r cut hd hw0 hw hr hcut tau hold hnew
    simpa [actual, realize] using
      (h d w r cut hd hw0 hw hr hcut tau hold hnew)
  · intro h d w r cut hd hw0 hw hr hcut tau hold hnew
    simpa [actual, realize] using
      (h d w r cut hd hw0 hw hr hcut tau hold hnew)

private def identityWord4 : List (Fin 4) := [0, 1, 2, 3]

private theorem zero4 : OriginalOrder 4 0 identityWord4 := by
  have hf : actualSource 4 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [identityWord4, hf]
  · intro n
    have hs : ((identityWord4.take n).map (actualSource 4 0)).sum = 0 := by
      rw [hf]
      simp
    rw [hs]
    norm_num [modulus]

private theorem bad4 : ¬ OriginalOrder 4 2 identityWord4 := by
  intro h
  have hh := h.2.2 3
  norm_num [identityWord4, List.finRange_succ, actualSource, centered, modulus] at hh

private def identityWord5 : List (Fin 5) := [0, 1, 2, 3, 4]

private theorem zero5 : OriginalOrder 5 0 identityWord5 := by
  have hf : actualSource 5 0 = fun _ => (0 : ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · simp [identityWord5, hf]
  · intro n
    have hs : ((identityWord5.take n).map (actualSource 5 0)).sum = 0 := by
      rw [hf]
      simp
    rw [hs]
    norm_num [modulus]

private theorem bad5 : ¬ OriginalOrder 5 2 identityWord5 := by
  intro h
  have hh := (h.2.2 4).1
  norm_num [identityWord5, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  let p : Input := ⟨2, 1, 2, 0⟩
  refine ⟨p, 0, 2, ?_⟩
  cases side with
  | false =>
      intro he
      apply bad4
      have hp := congrFun he identityWord4
      simpa [actual, realize, p] using (hp.mp zero4)
  | true =>
      intro he
      apply bad5
      have hp := congrFun he identityWord5
      simpa [actual, realize, p] using (hp.mp zero5)

def source_registration : Registration arena (type_of% (@physical_joint_repetition)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i with
      | false =>
        refine ⟨deleted false, ?_, rfl, deleted_law false⟩
        intro j hji
        cases j with
        | false => exact False.elim (hji rfl)
        | true => simp [deleted, realize]
      | true =>
        refine ⟨deleted true, ?_, rfl, deleted_law true⟩
        intro j hji
        cases j with
        | false => simp [deleted, realize]
        | true => exact False.elim (hji rfl)
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.PhysicalJointRepetition.physical_joint_repetition)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.PhysicalJointRepetition.physical_joint_repetition.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.PhysicalJointRepetition.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Repetition
    definition := none
    coordinates := #[0, 1, 2, 3]
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

end Reg.D5.S3.Combinatorics.Circle.PhysicalJointRepetition

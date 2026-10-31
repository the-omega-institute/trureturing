import D5.S3.Combinatorics.Circle.PhysicalJointRepetition
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

structure Input where
  d : ℕ
  w : ℕ
  r : ℕ
  cut : ℕ
  hd : 2 ≤ d
  hw0 : 1 ≤ w
  hw : w ≤ 2 ^ (d - 1) - 1
  hr : 2 ≤ r
  hcut : cut ≤ d

abbrev signature : Signature where
  Params := Input
  State p := List (Fin p.d)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun side p tau => match side with
      | false =>
          OriginalOrder (p.d * p.r) (p.w * geom p.d p.r)
            (repeatWord p.d p.r (Nat.zero_lt_of_lt p.hr) tau)
      | true =>
          OriginalOrder (p.d * p.r + 1) (2 * (p.w * geom p.d p.r))
            (earWord (p.d * p.r)
              (repeatWord p.d p.r (Nat.zero_lt_of_lt p.hr) tau) p.cut))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature
    (fun j p tau => if j = side then False else actual.readout j p tau)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Input) (tau : List (Fin p.d)),
    OriginalOrder p.d p.w tau →
    OriginalOrder (p.d + 1) (2 * p.w) (earWord p.d tau p.cut) →
    R.readout false p tau ∧ R.readout true p tau

private theorem actual_law : arena.Law actual := by
  intro p tau hold hnew
  simpa [actual, realize] using
    (physical_joint_repetition p.d p.w p.r p.cut p.hd p.hw0 p.hw p.hr p.hcut
      tau hold hnew)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Input := {
    d := 2, w := 1, r := 2, cut := 0,
    hd := by omega, hw0 := by omega, hw := by omega, hr := by omega, hcut := by omega }
  have hold : OriginalOrder p.d p.w [0, 1] := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    cases n with
    | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
    | succ n =>
        cases n <;> norm_num [OriginalOrder, actualSource, centered, modulus]
  have hnew : OriginalOrder (p.d + 1) (2 * p.w) (earWord p.d [0, 1] p.cut) := by
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
  simpa [rejected, realize] using (h p [0, 1] hold hnew)

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  let p : Input := {
    d := 2, w := 1, r := 2, cut := 0,
    hd := by omega, hw0 := by omega, hw := by omega, hr := by omega, hcut := by omega }
  have hold : OriginalOrder p.d p.w [0, 1] := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    cases n with
    | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
    | succ n =>
        cases n <;> norm_num [OriginalOrder, actualSource, centered, modulus]
  have hnew : OriginalOrder (p.d + 1) (2 * p.w) (earWord p.d [0, 1] p.cut) := by
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
  | false => simpa [deleted, actual, realize] using (h p [0, 1] hold hnew).1
  | true => simpa [deleted, actual, realize] using (h p [0, 1] hold hnew).2

private theorem source_bridge :
    (type_of% (@physical_joint_repetition)) ↔ arena.Law actual := by
  constructor
  · intro h p tau hold hnew
    simpa [actual, realize] using
      (h p.d p.w p.r p.cut p.hd p.hw0 p.hw p.hr p.hcut tau hold hnew)
  · intro h d w r cut hd hw0 hw hr hcut tau hold hnew
    let p : Input := {
      d := d
      w := w
      r := r
      cut := cut
      hd := hd
      hw0 := hw0
      hw := hw
      hr := hr
      hcut := hcut }
    simpa [actual, realize] using (h p tau hold hnew)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  let p : Input := {
    d := 2
    w := 1
    r := 2
    cut := 0
    hd := by omega
    hw0 := by omega
    hw := by omega
    hr := by omega
    hcut := by omega }
  refine ⟨p, [0, 1], [1, 0], ?_⟩
  cases side with
  | false =>
      have hgood := (actual_law p [0, 1] (by
        refine ⟨by decide, by decide, ?_⟩
        intro n
        cases n with
        | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
        | succ n =>
            cases n <;> norm_num [OriginalOrder, actualSource, centered, modulus]) (by
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
                | succ n => norm_num [OriginalOrder, earWord, actualSource, centered, modulus])).1
      have hbad : ¬ OriginalOrder (p.d * p.r) (p.w * geom p.d p.r)
          (repeatWord p.d p.r (Nat.zero_lt_of_lt p.hr) [1, 0]) := by
        intro h
        have hh := h.2.2 1
        norm_num [OriginalOrder, repeatWord, blockLabel, actualSource, centered, modulus,
          geom, List.finRange] at hh
      intro he
      apply hbad
      have htransport : actual.readout false p [1, 0] := by
        rw [← he]
        simpa [actual, realize] using hgood
      exact htransport
  | true =>
      have hgood := (actual_law p [0, 1] (by
        refine ⟨by decide, by decide, ?_⟩
        intro n
        cases n with
        | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
        | succ n =>
            cases n <;> norm_num [OriginalOrder, actualSource, centered, modulus]) (by
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
                | succ n => norm_num [OriginalOrder, earWord, actualSource, centered, modulus])).2
      have hbad : ¬ OriginalOrder (p.d * p.r + 1) (2 * (p.w * geom p.d p.r))
          (earWord (p.d * p.r)
            (repeatWord p.d p.r (Nat.zero_lt_of_lt p.hr) [1, 0]) p.cut) := by
        intro h
        have hh := h.2.2 2
        norm_num [OriginalOrder, earWord, repeatWord, blockLabel, actualSource, centered,
          modulus, geom, List.finRange] at hh
      intro he
      apply hbad
      have htransport : actual.readout true p [1, 0] := by
        rw [← he]
        simpa [actual, realize] using hgood
      exact htransport

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
    owner := `D5.S3.Combinatorics.Circle.PhysicalJointRepetition
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.PhysicalJointRepetition

import D5.S3.Combinatorics.Circle.PhysicalJointRepetition
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.PhysicalJointRepetition

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
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
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p tau =>
      OriginalOrder (p.d * p.r) (p.w * geom p.d p.r)
          (repeatWord p.d p.r (by omega) tau) ∧
        OriginalOrder (p.d * p.r + 1) (2 * (p.w * geom p.d p.r))
          (earWord (p.d * p.r) (repeatWord p.d p.r (by omega) tau) p.cut))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Input) (tau : List (Fin p.d)),
    OriginalOrder p.d p.w tau →
    OriginalOrder (p.d + 1) (2 * p.w) (earWord p.d tau p.cut) →
    R.readout () p tau

private theorem actual_law : arena.Law actual := by
  intro p tau hold hnew
  exact physical_joint_repetition p.d p.w p.r p.cut p.hd p.hw0 p.hw p.hr p.hcut
    tau hold hnew

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Input := {
    d := 2, w := 1, r := 2, cut := 0,
    hd := by omega, hw0 := by omega, hw := by omega, hr := by omega, hcut := by omega }
  have hold : OriginalOrder p.d p.w [0, 1] := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    norm_num [OriginalOrder, actualSource, centered, modulus]
  have hnew : OriginalOrder (p.d + 1) (2 * p.w) (earWord p.d [0, 1] p.cut) := by
    refine ⟨by decide, by decide, ?_⟩
    intro n
    norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
  exact (h p [0, 1] hold hnew)

private theorem source_bridge :
    (type_of% (@physical_joint_repetition)) ↔ arena.Law actual := by
  constructor
  · intro h p tau hold hnew
    exact h p.d p.w p.r p.cut p.hd p.hw0 p.hw p.hr p.hcut tau hold hnew
  · intro h d w r cut hd hw0 hw hr hcut tau hold hnew
    let p : Input := { d := d, w := w, r := r, cut := cut,
      hd := hd, hw0 := hw0, hw := hw, hr := hr, hcut := hcut }
    exact h p tau hold hnew

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let p : Input := { d := 2, w := 1, r := 2, cut := 0,
    hd := by omega, hw0 := by omega, hw := by omega, hr := by omega, hcut := by omega }
  refine ⟨p, [0, 1], [1, 0], ?_⟩
  have hgood := actual_law p [0, 1] (by
    refine ⟨by decide, by decide, ?_⟩
    intro n; norm_num [OriginalOrder, actualSource, centered, modulus]) (by
    refine ⟨by decide, by decide, ?_⟩
    intro n; norm_num [OriginalOrder, earWord, actualSource, centered, modulus])
  have hbad : ¬ OriginalOrder p.d p.w
      (repeatWord p.d p.r (by omega) [1, 0]) := by
    intro h
    have hh := h.2.2 1
    norm_num [OriginalOrder, repeatWord, blockLabel, actualSource, centered, modulus] at hh
  intro he
  exact hbad (by simpa [actual, realize] using (he ▸ hgood).1)

def source_registration : Registration arena (type_of% (@physical_joint_repetition)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.PhysicalJointRepetition

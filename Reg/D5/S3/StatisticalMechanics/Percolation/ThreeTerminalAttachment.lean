import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Registration of the entire independent attachment pushforward. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

structure Parameters where
  input : Mode → ℝ
  rate : ℝ

abbrev signature : Signature where
  Params := Parameters
  State _ := Port × Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p st => transfer st.1 p.input p.rate st.2) (fun e => nomatch e)

def bad : Realization signature := realize _
  (fun _ _ st => if st.2 = .ab ∨ st.2 = .bc then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Mode → ℝ) (_hp : ∀ s, 0 ≤ p s)
    (_hn : ∑ s, p s = 1) (C : ℝ) (_hC : 1 ≤ C) (q : ℝ)
    (_hq : q ∈ Set.Icc 0 1) (_hlow : 0 ≤ delta p)
    (_hbound : delta p+p .all*p .ac ≤ C*p .ac),
    ∀ port, 0 ≤ delta (fun s => R.readout () ⟨p,q⟩ (port,s)) ∧
      delta (fun s => R.readout () ⟨p,q⟩ (port,s))+
        R.readout () ⟨p,q⟩ (port,.all)*R.readout () ⟨p,q⟩ (port,.ac) ≤
        C*R.readout () ⟨p,q⟩ (port,.ac)

private theorem rejected : ¬ arena.Law bad := by
  classical
  intro h
  let p : Mode → ℝ := fun s => if s = .all then 1 else 0
  have hp : ∀ s, 0 ≤ p s := by intro s; simp only [p]; positivity
  have hn : ∑ s, p s = 1 := by simp [p]
  have hlo : 0 ≤ delta p := by norm_num [p,delta]
  have hbound : delta p+p .all*p .ac ≤ 1*p .ac := by norm_num [p,delta]
  have hh := (h p hp hn 1 le_rfl 1 (by norm_num) hlo hbound .a).1
  norm_num [bad,realize,delta] at hh

private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  let p : Mode → ℝ := fun s => if s = .all then 1 else 0
  have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
  refine ⟨⟨p,1⟩,(.a,.all),(.a,.separate),?_⟩
  norm_num [actual,realize,transfer,detach,p,henum,Fintype.sum_bool]

def registration : Registration arena (type_of% @attachment_invariant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attachment_invariant,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_attachment_invariant : Contract.Registration (@attachment_invariant)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.register_attachment_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p st => transfer st.1 p.input p.rate st.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.register_attachment_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_attachment_invariant

abbrev signedArena : Arena where
  signature := signature
  Law R := ∀ (p : Mode → ℝ) (_hp : ∀ s, 0 ≤ p s)
    (_hn : ∑ s, p s = 1) (C : ℝ) (_hC : 1 ≤ C) (q : ℝ)
    (_hq : q ∈ Set.Icc 0 1)
    (_hbound : |delta p|+p .all*p .ac ≤ C*p .ac),
    ∀ port, |delta (fun s => R.readout () ⟨p,q⟩ (port,s))|+
        R.readout () ⟨p,q⟩ (port,.all)*R.readout () ⟨p,q⟩ (port,.ac) ≤
        C*R.readout () ⟨p,q⟩ (port,.ac)

private theorem signedRejected : ¬ signedArena.Law bad := by
  classical
  intro h
  let p : Mode → ℝ := fun s => if s = .all then 1 else 0
  have hp : ∀ s, 0 ≤ p s := by intro s; simp only [p]; positivity
  have hn : ∑ s, p s = 1 := by simp [p]
  have hbound : |delta p|+p .all*p .ac ≤ 1*p .ac := by norm_num [p,delta]
  have hh := h p hp hn 1 le_rfl 1 (by norm_num) hbound .a
  norm_num [bad,realize,delta] at hh

def signedRegistration : Registration signedArena (type_of% @attachment_signed_invariant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attachment_signed_invariant,bad,signedRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,signedRejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_attachment_signed_invariant : Contract.Registration (@attachment_signed_invariant)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.register_attachment_signed_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.signedRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨signedArena⟩
  objectArena := .source ⟨signedArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source signedArena ⟨signedRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p st => transfer st.1 p.input p.rate st.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.register_attachment_signed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_attachment_signed_invariant

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment

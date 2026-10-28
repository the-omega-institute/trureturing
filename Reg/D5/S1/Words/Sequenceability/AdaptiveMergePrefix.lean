import D5.S1.Words.Sequenceability.AdaptiveMergePrefix
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.AdaptiveMergePrefix
open _root_.D5.S1.Words.Sequenceability.AdaptiveMergePrefix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ G : Type u, AddCommGroup G × (ℕ × ℕ)
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w =>
    letI := p.2.1
    ((w.drop p.2.2.1).take (p.2.2.2-p.2.2.1)).sum) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => letI := p.2.1; 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [inst : AddCommGroup G] (w : List G),
    @Good G inst w ↔
      ∀ i j : ℕ, i < j → j ≤ w.length → (i ≠ 0 ∨ j ≠ w.length) →
        R.readout () ⟨G,inst,(i,j)⟩ w ≠ 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let G := ULift.{u} ℤ
  have hg : Good ([1,2] : List G) := by
    intro i j hij hj heq
    have hj2 : j ≤ 2 := by simpa using hj
    have hi2 : i < 2 := by omega
    have hc : (i=0 ∧ j=1) ∨ (i=0 ∧ j=2) ∨ (i=1 ∧ j=2) := by omega
    rcases hc with hc | hc | hc <;> rcases hc with ⟨rfl,rfl⟩ <;>
      norm_num [prefixSum, _root_.D5.S1.Words.Sequenceability.SeparatedPrefixReflection.pref] at *
    have hbad := congrArg ULift.down heq
    norm_num at hbad
  exact (@h G inferInstance [1,2]).mp hg 0 1 (by omega) (by simp)
    (Or.inr (by simp)) rfl

-- Exact original telescope, with the actual interval sum as the enrolled observation.
def family : Registration arena.{u} (type_of% (@good_iff_proper_intervals.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@good_iff_proper_intervals.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℤ,inferInstance,(0,1)⟩,[1],[2],?_⟩
    change (1 : ULift.{u} ℤ) ≠ 2
    intro heq
    have hbad := congrArg ULift.down heq
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@good_iff_proper_intervals.{u}) (Realization signature.{u})
    (type_of% (@Good.{u})) Unit where
  unitName := `D5.S1.Words.Sequenceability.AdaptiveMergePrefix.good_iff_proper_intervals.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.AdaptiveMergePrefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Good.{u})
  -- Exact dependent source reconstruction is unfinished; no invented occurrence path.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S1.Words.Sequenceability.AdaptiveMergePrefix

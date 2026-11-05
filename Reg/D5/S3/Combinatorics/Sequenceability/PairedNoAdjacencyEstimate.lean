import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate
open _root_.D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open _root_.D5.S3.Combinatorics.CircularWords.DisjointBlockContraction

noncomputable section

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ r => (noAdjacency r).card) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 12 ≤ r →
    (4*(r:ℚ)^2-11*r+9) / (3*(2*r-1)*(2*r-3)) ≤
      (R.readout () () r : ℚ) / ((2*r-1).factorial : ℚ)

abbrev sourceScope := type_of% (@no_adjacency_lower_bound)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := no_adjacency_lower_bound

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 12) (by decide)
  norm_num [rejected, DependentFamily.realize] at hh

private theorem zero_rank_card : (noAdjacency 0).card = 1 := by
  have ha : alphabet 0 = ∅ := Finset.card_eq_zero.mp (by simp [alphabet_card])
  simp [noAdjacency, ha, circles, orders]

private theorem count_dependence : (noAdjacency 0).card ≠ (noAdjacency 12).card := by
  rw [zero_rank_card]
  have hb := no_adjacency_lower_bound (r := 12) (by decide)
  intro he
  rw [←he] at hb
  norm_num at hb

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 12, count_dependence⟩

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@no_adjacency_lower_bound) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate.no_adjacency_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ r => (noAdjacency r).card) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate

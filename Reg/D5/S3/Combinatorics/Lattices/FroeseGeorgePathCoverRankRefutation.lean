import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation
import Reg.Support.SingleDependentReadout

/-! Readouts of the source rank and its three consecutive rank counts. -/

namespace Reg.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation

open _root_.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation
open _root_.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation.Branch
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace RankPreservation

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Split Vertex) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ A => sourceRank Vertex A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ A => sourceRank Vertex A + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ A : Split Vertex, R.readout () () A = idealRank (idealEquiv A)

private def emptyIdeal : Ideal := ⟨∅, by simpa using (isLowerSet_empty : IsLowerSet (∅ : Set Node))⟩
private def fullIdeal : Ideal :=
  ⟨Finset.univ, by simpa using (isLowerSet_univ : IsLowerSet (Set.univ : Set Node))⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A := idealEquiv.symm (emptyIdeal, emptyIdeal)
  have bad := h A
  change sourceRank Vertex A + 1 = idealRank (idealEquiv A) at bad
  exact Nat.succ_ne_self _ (bad.trans (idealEquiv_preserves_rank A).symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have role : i = () := Subsingleton.elim _ _
  subst i
  refine ⟨(), idealEquiv.symm (emptyIdeal, emptyIdeal), idealEquiv.symm (fullIdeal, fullIdeal), ?_⟩
  change sourceRank Vertex _ ≠ sourceRank Vertex _
  simp only [idealEquiv_preserves_rank, OrderIso.apply_symm_apply]
  decide

def family : Registration arena (type_of% @idealEquiv_preserves_rank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨idealEquiv_preserves_rank, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@idealEquiv_preserves_rank) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation.RankPreservation.unit
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation.RankPreservation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => sourceRank Vertex A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RankPreservation

namespace ThreeRankCounts

inductive RankObservation
  | six | seven | eight
  deriving DecidableEq

instance : Fintype RankObservation where
  elems := {.six, .seven, .eight}
  complete i := by cases i <;> decide

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := RankObservation
  finiteRole := inferInstance
  nonemptyRole := ⟨.six⟩
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => rankCount Vertex k) (fun e => nomatch e)

def rejected (i : RankObservation) : Realization signature :=
  realize signature (fun j _ k => if j = i then (rankCount Vertex k).succ else rankCount Vertex k)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout .six () 6 = 15 ∧ R.readout .seven () 7 = 14 ∧ R.readout .eight () 8 = 17

private theorem rejected_law (i : RankObservation) : ¬ arena.Law (rejected i) := by
  intro h
  obtain ⟨h6, h7, h8⟩ := witness_rank_counts
  cases i
  · have hbad := h.1
    simp [rejected, realize, h6] at hbad
  · have hbad := h.2.1
    simp [rejected, realize, h7] at hbad
  · have hbad := h.2.2
    simp [rejected, realize, h8] at hbad

def family : Registration arena (type_of% @witness_rank_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨witness_rank_counts, rejected .six, rejected_law .six⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext p k
      simp [rejected, actual, realize, hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 6, 7, ?_⟩
    change rankCount Vertex 6 ≠ rankCount Vertex 7
    rw [witness_rank_counts.1, witness_rank_counts.2.1]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@witness_rank_counts) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation.ThreeRankCounts.unit
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation.ThreeRankCounts.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => rankCount Vertex k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ThreeRankCounts
end
end Reg.D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation

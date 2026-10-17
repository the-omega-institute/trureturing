import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution

open _root_.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
open _root_.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles
open _root_.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => edgeMultisetDimension n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dimension_zero : edgeMultisetDimension 0 = 0 := by
  apply le_antisymm _ bot_le
  unfold edgeMultisetDimension
  have h : Resolves (∅ : Finset (Vertex 0)) := by
    intro e
    exact isEmptyElim e
  exact le_trans (iInf_le _ ⟨∅, h⟩) (by simp)

namespace Dimension

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 3 ≤ n → R.readout () () n = ⊤

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 3) (by omega)
  change (0 : ℕ∞) = ⊤ at hh
  exact ENat.zero_ne_top hh

def source_registration : Registration arena (type_of% @edgeMultisetDimension_eq_top) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@edgeMultisetDimension_eq_top, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 3, ?_⟩
    change edgeMultisetDimension 0 ≠ edgeMultisetDimension 3
    rw [dimension_zero, edgeMultisetDimension_eq_top (by omega)]
    exact ENat.zero_ne_top

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@edgeMultisetDimension_eq_top) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution.Dimension.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution.Dimension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => edgeMultisetDimension n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Dimension
namespace SourceResult

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (hn : 3 ≤ n) (S : Set (Vertex n)),
    (∃ a b c d : Vertex n,
      (graph n).Adj a b ∧ (graph n).Adj c d ∧ s(a,b) ≠ s(c,d) ∧
      S.toFinite.toFinset.val.map (fun z => min ((graph n).dist z a) ((graph n).dist z b)) =
        S.toFinite.toFinset.val.map (fun z => min ((graph n).dist z c) ((graph n).dist z d))) ∧
      R.readout () () n = ⊤

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h (n := 3) (by omega) ∅).2
  change (0 : ℕ∞) = ⊤ at hh
  exact ENat.zero_ne_top hh

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 3, ?_⟩
    change edgeMultisetDimension 0 ≠ edgeMultisetDimension 3
    rw [dimension_zero, edgeMultisetDimension_eq_top (by omega)]
    exact ENat.zero_ne_top

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution.SourceResult.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution.SourceResult.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => edgeMultisetDimension n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end SourceResult

#print axioms Dimension.source_registration
#print axioms SourceResult.source_registration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionResolution

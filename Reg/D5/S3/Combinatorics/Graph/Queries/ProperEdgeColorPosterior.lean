import D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The number of matching proper edge colorings depends on the candidate graph. -/

namespace Reg.D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior

open _root_.D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ cycle => matchingColorCount cycle) (fun e => nomatch e)

private def zeroCount : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ cycle : Bool, R.readout () () cycle = (if cycle then 2 else 1) ∧
      properColorCount cycle = (if cycle then 18 else 12)) ∧
    (SimpleGraph.pathGraph 4).neighborFinset 1 = (SimpleGraph.cycleGraph 4).neighborFinset 1 ∧
    (SimpleGraph.pathGraph 4).neighborFinset 2 = (SimpleGraph.cycleGraph 4).neighborFinset 2 ∧
    cyclePosterior = 4 / 7

private theorem zeroCount_invalid : ¬ arena.Law zeroCount := by
  intro h
  have hc : (0 : ℕ) = 1 := (h.1 false).1
  exact Nat.zero_ne_one hc

def evidence : Registration arena (type_of% proper_edge_colors_change_posterior) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨proper_edge_colors_change_posterior, zeroCount, zeroCount_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroCount, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroCount_invalid⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨(), false, true, ?_⟩
    have path : matchingColorCount false = 1 :=
      (proper_edge_colors_change_posterior.1 false).1
    have cycle : matchingColorCount true = 2 :=
      (proper_edge_colors_change_posterior.1 true).1
    change matchingColorCount false ≠ matchingColorCount true
    rw [path, cycle]
    decide

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      proper_edge_colors_change_posterior (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior.proper_edge_colors_change_posterior
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ cycle => matchingColorCount cycle) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior

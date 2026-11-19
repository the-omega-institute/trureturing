import D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Combinatorics.SimpleGraph.Star
import Reg.Support.DependentFamily

/-! The update of the queried set when a known vertex is queried. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle

noncomputable section
universe u

private abbrev querySignature : Signature where
  Params := Σ V : Type u, V
  State p := Set p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def registerQuery : Realization querySignature.{u} :=
  realize querySignature (fun _ p Q => insert p.2 Q) (fun e => nomatch e)

private def ignoreQuery : Realization querySignature.{u} :=
  realize querySignature (fun _ _ Q => Q) (fun e => nomatch e)

private abbrev cycleArena : Arena where
  signature := querySignature.{u}
  Law R := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (root x : V) (Q : Set V) (_history : RootedExploration G root Q)
    (_known : (exposed G Q).Reachable root x) (_forest : (exposed G Q).IsAcyclic),
    let queriedAfter := R.readout () ⟨V, x⟩ Q
    ¬ (exposed G queriedAfter).IsAcyclic ↔ x ∉ Q ∧
      ∃ y, G.Adj x y ∧ y ∉ Q ∧ (exposed G Q).Reachable root y

private theorem rejectsIgnore : ¬ cycleArena.{u}.Law ignoreQuery := by
  intro law
  let V := ULift.{u} (Fin 3)
  let G : SimpleGraph V := ⊤
  let root : V := ⟨0⟩
  let x : V := ⟨1⟩
  let y : V := ⟨2⟩
  let Q : Set V := {root}
  have hx : x ∉ Q := by decide
  have hy : y ∉ Q := by decide
  have hrx : root ≠ x := by decide
  have hry : root ≠ y := by decide
  have hxy : G.Adj x y := by
    change x ≠ y
    decide
  have hGraph : exposed G Q = SimpleGraph.starGraph root := by
    ext a b
    change (a ≠ b ∧ (a ∈ Q ∨ b ∈ Q)) ↔ _
    simp [Q]
  have forest : (exposed G Q).IsAcyclic := by
    rw [hGraph]
    exact SimpleGraph.isAcyclic_starGraph root
  have known : (exposed G Q).Reachable root x := by
    rw [hGraph]
    exact (SimpleGraph.starGraph_center_adj hrx).reachable
  have knownY : (exposed G Q).Reachable root y := by
    rw [hGraph]
    exact (SimpleGraph.starGraph_center_adj hry).reachable
  have history : RootedExploration G root Q := by
    simpa [Q] using (RootedExploration.step (G := G) (root := root)
      .start (SimpleGraph.Reachable.refl root))
  exact (law G root x Q history known forest).mpr ⟨hx, y, hxy, hy, knownY⟩ forest

private theorem dependence : ObservationalDependence querySignature.{u} registerQuery := by
  intro _
  let V := ULift.{u} Bool
  let x : V := ⟨false⟩
  let y : V := ⟨true⟩
  refine ⟨⟨V, x⟩, ∅, {y}, ?_⟩
  change insert x (∅ : Set V) ≠ insert x {y}
  intro h
  have hy : y ∈ insert x ({y} : Set V) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hny : y ∉ insert x (∅ : Set V) := by decide
  exact hny (h ▸ hy)

def cycleEvidence : Registration cycleArena.{u} (type_of% (@first_observed_cycle.{u})) where
  actual := registerQuery
  bridge := Iff.rfl
  variation := ⟨@first_observed_cycle.{u}, ignoreQuery, rejectsIgnore⟩
  sensitivity := ⟨fun i => ⟨ignoreQuery, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejectsIgnore⟩, fun e => nomatch e⟩
  dependence := dependence

def cycleRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@first_observed_cycle.{u}) (Realization querySignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle.first_observed_cycle
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle.cycleEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cycleArena.{u}⟩
  objectArena := .source ⟨cycleArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cycleArena.{u} ⟨cycleEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize querySignature (fun _ p Q => insert p.2 Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.FirstObservedCycle

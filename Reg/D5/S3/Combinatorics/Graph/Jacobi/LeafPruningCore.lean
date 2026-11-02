import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.LeafPruningCore
import Reg.Support.DependentFamily

/-! Faithful full-source truth-readout attempt for actual core maximality.
The selected conclusion holds throughout this legal source family, hence
this particular readout has no observational dependence. Other encodings
are not excluded. No validated registration is claimed; see #24489. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.LeafPruningCore

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Source where
  Flag : Type
  finiteFlag : Finite Flag
  graph : FlagGraph Flag
  pruning : @FlagGraph.LeafPruning Flag finiteFlag graph
  vertices : Set graph.VertexOrbit
  degree : ∀ v ∈ vertices, ¬graph.HasAnchor v →
    2 ≤ Nat.card {f : Flag // graph.vertexOf f = v ∧ graph.vertexOf (graph.edge f) ∈ vertices}

attribute [instance] Source.finiteFlag

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ s => s.vertices ⊆ {v | s.pruning.rank v = s.pruning.steps})
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (F : Type) (hF : Finite F) (G : FlagGraph F)
    (P : @FlagGraph.LeafPruning F hF G) (S : Set G.VertexOrbit),
    (∀ v ∈ S, ¬G.HasAnchor v →
      2 ≤ Nat.card {f : F // G.vertexOf f = v ∧ G.vertexOf (G.edge f) ∈ S}) →
    S ⊆ {v | P.rank v = P.steps}

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.Flag s.finiteFlag s.graph s.pruning s.vertices s.degree
  · intro h F hF G P S hS
    exact h ⟨F, hF, G, P, S, hS⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact s.pruning.terminal_core_greatest s.vertices s.degree

theorem selected_source_has_no_observational_dependence :
    ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  cases p
  apply hxy
  exact propext ⟨fun _ => actual_law y, fun _ => actual_law x⟩

theorem selected_source_has_no_registration :
    ¬ ∃ R : Registration arena originalStatement, R.actual = actual := by
  rintro ⟨R, he⟩
  exact selected_source_has_no_observational_dependence (he ▸ R.dependence)

end Reg.D5.S3.Combinatorics.Graph.Jacobi.LeafPruningCore

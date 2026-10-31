import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.FlagPruning
import Reg.Support.DependentFamily

/-! Faithful source-family attempt for the actual pruning vanishing theorem.
The exact lawful source readout is zero throughout this family; this attempt
therefore proves the observational-dependence slot unavailable. It declares
no successful registration and does not change the mathematical conclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.FlagPruning

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Source where
  Flag : Type
  finiteFlag : Finite Flag
  graph : FlagGraph Flag
  pruning : @FlagGraph.LeafPruning Flag finiteFlag graph
  connected : graph.incidence.Connected
  stable : graph.Stable
  component : @FlagGraph.LeafPruning.DeletedComponent Flag finiteFlag graph pruning
  branching : 2 ≤ @FlagGraph.LeafPruning.componentLeafCount Flag finiteFlag graph pruning component

attribute [instance] Source.finiteFlag

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := JacobiSpace
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ s => classOf s.graph) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s = 0

def originalStatement : Prop :=
  ∀ (F : Type) (hF : Finite F) (G : FlagGraph F)
    (P : @FlagGraph.LeafPruning F hF G)
    (_hc : G.incidence.Connected) (_hs : G.Stable)
    (c : @FlagGraph.LeafPruning.DeletedComponent F hF G P),
    2 ≤ @FlagGraph.LeafPruning.componentLeafCount F hF G P c → @classOf F hF G = 0

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.Flag s.finiteFlag s.graph s.pruning s.connected s.stable s.component s.branching
  · intro h F hF G P hc hs c hl
    exact h ⟨F, hF, G, P, hc, hs, c, hl⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact FlagGraph.LeafPruning.pruned_branching_component_vanishes s.graph s.pruning
    s.connected s.stable s.component s.branching

theorem selected_source_has_no_observational_dependence :
    ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  cases p
  exact hxy ((actual_law x).trans (actual_law y).symm)

theorem selected_source_has_no_registration :
    ¬ ∃ R : Registration arena originalStatement, R.actual = actual := by
  rintro ⟨R, he⟩
  exact selected_source_has_no_observational_dependence (he ▸ R.dependence)

end Reg.D5.S3.Combinatorics.Graph.Jacobi.FlagPruning

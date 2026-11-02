import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.LeafPruningExistence
import Reg.Support.DependentFamily

/-! Full-source truth-readout attempt for terminal pruning existence.
The source retains every finite flag carrier and every actual graph, without
connectivity, stability, or an assumed pruning. Its chosen existence readout
is true throughout the legal source family, so actual observational
dependence fails for this readout. This does not rule out other encodings.
No validated registration is claimed; audit remains unfinished under #24489. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.LeafPruningExistence

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Source where
  Flag : Type
  finiteFlag : Finite Flag
  graph : FlagGraph Flag

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
  realize signature (fun _ _ s => Nonempty s.graph.LeafPruning) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (F : Type) (hF : Finite F) (G : FlagGraph F),
    Nonempty (@FlagGraph.LeafPruning F hF G)

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.Flag s.finiteFlag s.graph
  · intro h F hF G
    exact h ⟨F, hF, G⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact s.graph.exists_leaf_pruning

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

end Reg.D5.S3.Combinatorics.Graph.Jacobi.LeafPruningExistence

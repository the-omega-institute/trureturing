import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.LeafPruningRanks
import Reg.Support.DependentFamily

/-! Full-source truth-readout attempts for the six consumed rank helpers.
Each state retains the complete theorem telescope. The actual conclusion is
true throughout its lawful source family, so this chosen readout has no
observational dependence. These attempts declare no successful registration
and do not exclude a different encoding. Audit remains unfinished: #24489. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.LeafPruningRanks

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace DeletedAcyclic

structure Source where
  V : Type
  graph : SimpleGraph V
  pruning : Pruning.LeafRanks graph

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
  realize signature (fun _ _ s => (s.graph.induce {v | s.pruning.rank v < s.pruning.cut}).IsAcyclic) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (P : Pruning.LeafRanks G),
    (G.induce {v | P.rank v < P.cut}).IsAcyclic

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.V s.graph s.pruning
  · intro h V G P
    exact h ⟨V, G, P⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact Pruning.deleted_acyclic s.pruning

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

end DeletedAcyclic

namespace CycleRetained

structure Source where
  V : Type
  graph : SimpleGraph V
  pruning : Pruning.LeafRanks graph
  vertex : V
  walk : graph.Walk vertex vertex
  cycle : walk.IsCycle

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
  realize signature (fun _ _ s => ∀ w ∈ s.walk.support, s.pruning.cut ≤ s.pruning.rank w) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (P : Pruning.LeafRanks G)
    (v : V) (c : G.Walk v v), c.IsCycle → ∀ w ∈ c.support, P.cut ≤ P.rank w

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.V s.graph s.pruning s.vertex s.walk s.cycle
  · intro h V G P v c hc
    exact h ⟨V, G, P, v, c, hc⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact Pruning.cycle_retained s.pruning s.walk s.cycle

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

end CycleRetained

namespace RetainedPath

structure Source where
  V : Type
  graph : SimpleGraph V
  pruning : Pruning.LeafRanks graph
  start : V
  finish : V
  walk : graph.Walk start finish
  path : walk.IsPath
  start_retained : pruning.cut ≤ pruning.rank start
  finish_retained : pruning.cut ≤ pruning.rank finish

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
  realize signature (fun _ _ s => ∀ w ∈ s.walk.support, s.pruning.cut ≤ s.pruning.rank w) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (P : Pruning.LeafRanks G)
    (u v : V) (p : G.Walk u v), p.IsPath → P.cut ≤ P.rank u →
    P.cut ≤ P.rank v → ∀ w ∈ p.support, P.cut ≤ P.rank w

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.V s.graph s.pruning s.start s.finish s.walk s.path s.start_retained s.finish_retained
  · intro h V G P u v p hp hu hv
    exact h ⟨V, G, P, u, v, p, hp, hu, hv⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact Pruning.retained_path s.pruning s.walk s.path s.start_retained s.finish_retained

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

end RetainedPath

namespace RetainedConnected

structure Source where
  V : Type
  graph : SimpleGraph V
  pruning : Pruning.LeafRanks graph
  connected : graph.Connected
  retained : ∃ v, pruning.cut ≤ pruning.rank v

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
  realize signature (fun _ _ s => (s.graph.induce {v | s.pruning.cut ≤ s.pruning.rank v}).Connected) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (P : Pruning.LeafRanks G),
    G.Connected → (∃ v, P.cut ≤ P.rank v) →
    (G.induce {v | P.cut ≤ P.rank v}).Connected

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.V s.graph s.pruning s.connected s.retained
  · intro h V G P hc hn
    exact h ⟨V, G, P, hc, hn⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact Pruning.retained_connected s.pruning s.connected s.retained

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

end RetainedConnected

namespace BoundaryUnique

structure Source where
  V : Type
  graph : SimpleGraph V
  pruning : Pruning.LeafRanks graph
  component : (Pruning.DeletedGraph pruning).ConnectedComponent
  first : Pruning.ComponentBoundary pruning component
  second : Pruning.ComponentBoundary pruning component

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
  realize signature (fun _ _ s => s.first.inside.val = s.second.inside.val ∧ s.first.outside = s.second.outside) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (P : Pruning.LeafRanks G)
    (c : (Pruning.DeletedGraph P).ConnectedComponent)
    (A B : Pruning.ComponentBoundary P c),
    A.inside.val = B.inside.val ∧ A.outside = B.outside

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.V s.graph s.pruning s.component s.first s.second
  · intro h V G P c A B
    exact h ⟨V, G, P, c, A, B⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact Pruning.component_boundary_unique s.pruning s.first s.second

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

end BoundaryUnique

namespace BoundaryNonempty

structure Source where
  V : Type
  graph : SimpleGraph V
  pruning : Pruning.LeafRanks graph
  connected : graph.Connected
  retained : ∃ v, pruning.cut ≤ pruning.rank v
  component : (Pruning.DeletedGraph pruning).ConnectedComponent

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
  realize signature (fun _ _ s => Nonempty (Pruning.ComponentBoundary s.pruning s.component)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (P : Pruning.LeafRanks G),
    G.Connected → (∃ v, P.cut ≤ P.rank v) →
    ∀ c : (Pruning.DeletedGraph P).ConnectedComponent,
      Nonempty (Pruning.ComponentBoundary P c)

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.V s.graph s.pruning s.connected s.retained s.component
  · intro h V G P hc hn c
    exact h ⟨V, G, P, hc, hn, c⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact Pruning.component_boundary_nonempty s.pruning s.connected s.retained s.component

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

end BoundaryNonempty

end Reg.D5.S3.Combinatorics.Graph.Jacobi.LeafPruningRanks

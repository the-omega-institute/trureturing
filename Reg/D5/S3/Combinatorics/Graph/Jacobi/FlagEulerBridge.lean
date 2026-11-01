import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.FlagEulerBridge
import Reg.Support.DependentFamily

/-! Full-source truth-readout attempts for the two Euler bridge theorems.
Each state keeps the complete original telescope. The chosen conclusion
readout is true throughout its legal source family, so it lacks actual
observational dependence. This excludes only these specified readouts,
not every possible encoding. Audit remains unfinished under #24489. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.FlagEulerBridge

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace IncidenceEulerGenus

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
  realize signature (fun _ _ s =>
    Nat.card s.graph.incidence.edgeSet + 1 - Nat.card s.graph.IncidenceVertex =
      s.graph.eulerGenus) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (F : Type) (hF : Finite F) (G : FlagGraph F),
    Nat.card G.incidence.edgeSet + 1 - Nat.card G.IncidenceVertex = @FlagGraph.eulerGenus F hF G

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.Flag s.finiteFlag s.graph
  · intro h F hF G
    exact h ⟨F, hF, G⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact s.graph.incidence_euler_genus

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

end IncidenceEulerGenus

namespace PositiveEulerGenus

structure Source where
  Flag : Type
  finiteFlag : Finite Flag
  graph : FlagGraph Flag
  connected : graph.incidence.Connected

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
  realize signature (fun _ _ s =>
    0 < s.graph.eulerGenus ↔ ¬ s.graph.incidence.IsAcyclic) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ (F : Type) (hF : Finite F) (G : FlagGraph F),
    G.incidence.Connected → (0 < @FlagGraph.eulerGenus F hF G ↔ ¬G.incidence.IsAcyclic)

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.Flag s.finiteFlag s.graph s.connected
  · intro h F hF G hc
    exact h ⟨F, hF, G, hc⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact s.graph.positive_euler_genus_iff_cycle s.connected

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

end PositiveEulerGenus

end Reg.D5.S3.Combinatorics.Graph.Jacobi.FlagEulerBridge

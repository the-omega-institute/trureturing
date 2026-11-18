import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.ZeroForcing.ContingentThreshold
import Reg.Support.DependentFamily

/-! Full-source truth-readout attempts. The complete original telescopes, including
empty graph and zero-budget fibers, are retained. These selected readouts are
constant true on their lawful families, so the observational-dependence slot
fails. This excludes these readouts only; it does not exclude other realizations
and declares no validated Contract.Registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.ZeroForcing.ContingentThreshold
open _root_.D5.S3.Combinatorics.Graph.ZeroForcing.ContingentThreshold
open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u

namespace Chronology

structure Source where
  V : Type u
  finiteV : Fintype V
  eqV : DecidableEq V
  graph : SimpleGraph V
  placement : Finset V

attribute [local instance] Source.finiteV Source.eqV

abbrev signature : Signature where
  Params := Unit
  State _ := Source.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ _ s =>
    (∃ L, LegalRun s.graph s.placement L Finset.univ) ↔
      IsZeroForcing s.graph (s.placement : Set s.V)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ s : Source.{u}, R.readout () () s

theorem exact_source_bridge : (type_of% (@chronological_iff_zero_forcing.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h s
    exact h s.graph s.placement
  · intro h V fv eq G S
    exact h ⟨V, fv, eq, G, S⟩

theorem actual_law : arena.{u}.Law actual := by
  intro s
  exact chronological_iff_zero_forcing s.graph s.placement

private noncomputable def witness : Source.{u} where
  V := ULift.{u} (Fin 1)
  finiteV := inferInstance
  eqV := inferInstance
  graph := ⊥
  placement := Finset.univ

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h witness

theorem variation_evidence : Variation arena.{u} actual :=
  ⟨actual_law, rejected, rejected_law⟩

theorem sensitivity_evidence : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro i
    exact nomatch i

theorem selected_readout_has_no_observational_dependence :
    ¬ ObservationalDependence signature.{u} actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  cases p
  apply hxy
  exact propext ⟨fun _ => actual_law y, fun _ => actual_law x⟩

theorem selected_readout_has_no_registration :
    ¬ ∃ R : Registration arena.{u} (type_of% (@chronological_iff_zero_forcing.{u})), R.actual = actual := by
  rintro ⟨R, he⟩
  exact selected_readout_has_no_observational_dependence (he ▸ R.dependence)

#print axioms exact_source_bridge
#print axioms selected_readout_has_no_registration

end Chronology

namespace Critical

structure Source where
  V : Type u
  finiteV : Fintype V
  eqV : DecidableEq V
  graph : SimpleGraph V
  adjacency : DecidableRel graph.Adj
  white : Finset V
  nonempty : white.Nonempty

attribute [local instance] Source.finiteV Source.eqV Source.adjacency

abbrev signature : Signature where
  Params := Unit
  State _ := Source.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ _ s =>
    (criticalEdges s.graph s.white : Set (Sym2 s.V)) ⊆ s.graph.edgeSet ∧
    (criticalEdges s.graph s.white).card = (boundary s.graph s.white).card ∧
    IsFort (s.graph.deleteEdges (criticalEdges s.graph s.white : Set (Sym2 s.V))) s.white ∧
    ∀ F : Finset (Sym2 s.V), IsFort (s.graph.deleteEdges (F : Set (Sym2 s.V))) s.white →
      criticalEdges s.graph s.white ⊆ F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ s : Source.{u}, R.readout () () s

theorem exact_source_bridge : (type_of% (@critical_edges_fort_minimality.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h s
    exact h s.graph s.white s.nonempty
  · intro h V fv eq G da W hw
    exact h ⟨V, fv, eq, G, da, W, hw⟩

theorem actual_law : arena.{u}.Law actual := by
  intro s
  exact critical_edges_fort_minimality s.graph s.white s.nonempty

private noncomputable def witness : Source.{u} where
  V := ULift.{u} (Fin 1)
  finiteV := inferInstance
  eqV := inferInstance
  graph := ⊥
  adjacency := inferInstance
  white := Finset.univ
  nonempty := ⟨ULift.up 0, Finset.mem_univ _⟩

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h witness

theorem variation_evidence : Variation arena.{u} actual :=
  ⟨actual_law, rejected, rejected_law⟩

theorem sensitivity_evidence : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro i
    exact nomatch i

theorem selected_readout_has_no_observational_dependence :
    ¬ ObservationalDependence signature.{u} actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  cases p
  apply hxy
  exact propext ⟨fun _ => actual_law y, fun _ => actual_law x⟩

theorem selected_readout_has_no_registration :
    ¬ ∃ R : Registration arena.{u} (type_of% (@critical_edges_fort_minimality.{u})), R.actual = actual := by
  rintro ⟨R, he⟩
  exact selected_readout_has_no_observational_dependence (he ▸ R.dependence)

#print axioms exact_source_bridge
#print axioms selected_readout_has_no_registration

end Critical

namespace Threshold

structure Source where
  V : Type u
  finiteV : Fintype V
  eqV : DecidableEq V
  graph : SimpleGraph V
  adjacency : DecidableRel graph.Adj
  placement : Finset V
  budget : ℕ

attribute [local instance] Source.finiteV Source.eqV Source.adjacency

abbrev signature : Signature where
  Params := Unit
  State _ := Source.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ _ s =>
    Contingent s.graph s.placement s.budget ↔
      (s.budget : ℕ∞) < lambda s.graph s.placement) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ s : Source.{u}, R.readout () () s

theorem exact_source_bridge : (type_of% (@contingent_iff_lambda_gt.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h s
    exact h s.graph s.placement s.budget
  · intro h V fv eq G da S k
    exact h ⟨V, fv, eq, G, da, S, k⟩

theorem actual_law : arena.{u}.Law actual := by
  intro s
  exact contingent_iff_lambda_gt s.graph s.placement s.budget

private noncomputable def witness : Source.{u} where
  V := ULift.{u} (Fin 1)
  finiteV := inferInstance
  eqV := inferInstance
  graph := ⊥
  adjacency := inferInstance
  placement := Finset.univ
  budget := 0

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h witness

theorem variation_evidence : Variation arena.{u} actual :=
  ⟨actual_law, rejected, rejected_law⟩

theorem sensitivity_evidence : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro i
    exact nomatch i

theorem selected_readout_has_no_observational_dependence :
    ¬ ObservationalDependence signature.{u} actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  cases p
  apply hxy
  exact propext ⟨fun _ => actual_law y, fun _ => actual_law x⟩

theorem selected_readout_has_no_registration :
    ¬ ∃ R : Registration arena.{u} (type_of% (@contingent_iff_lambda_gt.{u})), R.actual = actual := by
  rintro ⟨R, he⟩
  exact selected_readout_has_no_observational_dependence (he ▸ R.dependence)

#print axioms exact_source_bridge
#print axioms selected_readout_has_no_registration

end Threshold

end Reg.D5.S3.Combinatorics.Graph.ZeroForcing.ContingentThreshold

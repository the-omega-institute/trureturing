import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators Matrix
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private zero_feasible zero_infeasible two_feasible from
  D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber
universe u

structure Parameters where
  Vertex : Type u
  finiteVertex : Fintype Vertex
  equalVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex
  connected : graph.Connected
  color : Vertex → Bool
  proper : ∀ u v, graph.Adj u v → color u ≠ color v

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Parameters.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ _ p => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact settingNumber p.graph)
  (fun e => nomatch e)

private def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)

def fullLaw (r : Realization signature.{u}) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∀ connected : G.Connected, ∀ color : V → Bool,
    ∀ proper : (∀ u v, G.Adj u v → color u ≠ color v),
    (feasibleSettingCounts G).Nonempty ∧
      r.readout () () ⟨V, inferInstance, inferInstance, G, connected, color, proper⟩ =
        min 2 (nonlinearNeighborhoods G).card

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law := fullLaw

private def starGraph : SimpleGraph (ULift.{u} (Fin 3)) :=
  SimpleGraph.fromRel (fun a b => a.down = 0 ∧ b.down ≠ 0)

private def starColor (v : ULift.{u} (Fin 3)) : Bool := v.down == 0

private theorem star_proper : ∀ u v, starGraph.{u}.Adj u v → starColor u ≠ starColor v := by
  rintro ⟨u⟩ ⟨v⟩
  fin_cases u <;> fin_cases v <;> simp [starGraph, SimpleGraph.fromRel_adj, starColor]

private theorem star_connected : starGraph.{u}.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨0⟩, ?_⟩
  rintro ⟨v⟩
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact (show starGraph.Adj ⟨0⟩ ⟨1⟩ by
      simp [starGraph, SimpleGraph.fromRel_adj]).reachable
  · exact (show starGraph.Adj ⟨0⟩ ⟨2⟩ by
      simp [starGraph, SimpleGraph.fromRel_adj]).reachable

private theorem star_large : 2 ≤ (starGraph.{u}.neighborFinset ⟨0⟩).card := by
  have hN : starGraph.{u}.neighborFinset ⟨0⟩ = {⟨1⟩, ⟨2⟩} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset]
    rcases y with ⟨y⟩
    fin_cases y <;> simp [starGraph, SimpleGraph.fromRel_adj]
  rw [hN]
  decide

@[reducible] private def singletonParameters : Parameters.{u} where
  Vertex := ULift.{u} Unit
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := ⊥
  connected := by
    rw [SimpleGraph.connected_bot_iff]
    exact ⟨inferInstance, inferInstance⟩
  color := fun _ => true
  proper := by simp

@[reducible] private def sample : Parameters.{u} where
  Vertex := ULift.{u} (Fin 3)
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := starGraph
  connected := star_connected
  color := starColor
  proper := star_proper

private theorem actual_law : fullLaw actual.{u} := by
  intro V _ _ G connected color proper
  exact setting_number_classification G connected color proper

private theorem rejected_law : ¬ fullLaw rejected.{u} := by
  intro h
  have hx := (h singletonParameters.Vertex ⊥ (by
    rw [SimpleGraph.connected_bot_iff]; exact ⟨inferInstance, inferInstance⟩) (fun _ => true)
    (by simp)).2
  norm_num [rejected, realize, nonlinearNeighborhoods] at hx

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  rintro ⟨⟩
  refine ⟨(), singletonParameters, sample, ?_⟩
  have hempty : nonlinearNeighborhoods singletonParameters.graph = ∅ := by
    simp [nonlinearNeighborhoods, singletonParameters]
  have hzero : 0 ∈ feasibleSettingCounts singletonParameters.graph :=
    zero_feasible singletonParameters.graph singletonParameters.color
      singletonParameters.proper hempty
  have hinf : settingNumber singletonParameters.graph = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact csInf_le (OrderBot.bddBelow _) hzero
  have hmem : starGraph.{u}.neighborFinset ⟨0⟩ ∈ nonlinearNeighborhoods starGraph :=
    Finset.mem_image.mpr ⟨⟨0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, star_large⟩, rfl⟩
  have hpositive : 1 ≤ (nonlinearNeighborhoods starGraph.{u}).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  have hnotzero := zero_infeasible starGraph starColor star_proper hpositive
  have hnonempty : (feasibleSettingCounts starGraph.{u}).Nonempty :=
    ⟨2, two_feasible starGraph starColor star_proper⟩
  intro he
  have heq : settingNumber starGraph.{u} = 0 := by
    change settingNumber singletonParameters.graph = settingNumber starGraph at he
    rw [hinf] at he
    exact he.symm
  exact hnotzero (heq ▸ (csInf_mem hnonempty : settingNumber starGraph ∈ feasibleSettingCounts starGraph))

def familyRegistration : Registration arena.{u}
    (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → ∀ color : V → Bool,
      (∀ u v, G.Adj u v → color u ≠ color v) →
      (feasibleSettingCounts G).Nonempty ∧
        settingNumber G = min 2 (nonlinearNeighborhoods G).card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj; exact (hj (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration
    (@_root_.D5.S3.Quantum.Fibers.BipartiteBlockade.setting_number_classification.{u})
    (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber.setting_number_classification.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ p => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact settingNumber p.graph)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber

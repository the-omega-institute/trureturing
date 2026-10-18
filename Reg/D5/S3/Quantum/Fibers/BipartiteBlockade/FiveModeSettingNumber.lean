import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber
import D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators Matrix
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private zero_feasible zero_infeasible two_feasible from
  D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber
open private five_contract_iff from
  D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber
open private sample singletonParameters starGraph starColor star_proper star_large from
  Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber
universe u

def actual : Realization SettingNumber.signature.{u} := realize SettingNumber.signature
  (fun _ _ p => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact fiveModeSettingNumber p.graph)
  (fun e => nomatch e)

private def rejected : Realization SettingNumber.signature.{u} := realize SettingNumber.signature
  (fun _ _ _ => 3) (fun e => nomatch e)

def fullLaw (r : Realization SettingNumber.signature.{u}) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∀ connected : G.Connected, ∀ color : V → Bool,
    ∀ proper : (∀ u v, G.Adj u v → color u ≠ color v),
    (∀ v, (G.neighborFinset v).card ≤ 2) →
    feasibleFiveModeCounts G = feasibleSettingCounts G ∧
      (feasibleFiveModeCounts G).Nonempty ∧
      r.readout () () ⟨V, inferInstance, inferInstance, G, connected, color, proper⟩ =
        min 2 (nonlinearNeighborhoods G).card

@[reducible] def arena : Arena where
  signature := SettingNumber.signature.{u}
  Law := fullLaw

private theorem actual_law : fullLaw actual.{u} := by
  intro V _ _ G connected color proper degree
  exact five_mode_setting_number_classification G connected color proper degree

private theorem rejected_law : ¬ fullLaw rejected.{u} := by
  intro h
  have hx := (h singletonParameters.Vertex ⊥ (by
    rw [SimpleGraph.connected_bot_iff]; exact ⟨inferInstance, inferInstance⟩) (fun _ => true)
    (by simp) (by simp)).2.2
  norm_num [rejected, realize, nonlinearNeighborhoods] at hx

private theorem same_counts {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (degree : ∀ v, (G.neighborFinset v).card ≤ 2) :
    feasibleFiveModeCounts G = feasibleSettingCounts G := by
  ext k
  constructor
  · rintro ⟨drives, positive, sufficient⟩
    exact ⟨drives, positive, (five_contract_iff G color proper degree drives).mp sufficient⟩
  · rintro ⟨drives, positive, sufficient⟩
    exact ⟨drives, positive, (five_contract_iff G color proper degree drives).mpr sufficient⟩

private theorem actual_dependence : ObservationalDependence SettingNumber.signature.{u} actual := by
  rintro ⟨⟩
  letI : DecidableRel singletonParameters.{u}.graph.Adj :=
    fun _ _ => Classical.propDecidable _
  letI : DecidableRel starGraph.{u}.Adj := fun _ _ => Classical.propDecidable _
  refine ⟨(), singletonParameters, sample, ?_⟩
  have hsingleDegree : ∀ v, (singletonParameters.graph.neighborFinset v).card ≤ 2 := by
    simp [singletonParameters]
  have hstarDegree : ∀ v, (starGraph.{u}.neighborFinset v).card ≤ 2 := by
    intro v
    have hh := starGraph.degree_lt_card_verts v
    simpa only [SimpleGraph.card_neighborFinset_eq_degree, Fintype.card_ulift,
      Fintype.card_fin, Nat.lt_succ_iff] using hh
  have hempty : nonlinearNeighborhoods singletonParameters.graph = ∅ := by
    simp [nonlinearNeighborhoods, singletonParameters]
  have hzero : 0 ∈ feasibleSettingCounts singletonParameters.graph :=
    zero_feasible singletonParameters.graph singletonParameters.color
      singletonParameters.proper hempty
  have hinf : fiveModeSettingNumber singletonParameters.graph = 0 := by
    change sInf (feasibleFiveModeCounts _) = 0
    rw [same_counts _ singletonParameters.color singletonParameters.proper hsingleDegree]
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
    change fiveModeSettingNumber singletonParameters.graph = fiveModeSettingNumber starGraph at he
    rw [hinf] at he
    change 0 = sInf (feasibleFiveModeCounts starGraph) at he
    rw [same_counts starGraph starColor star_proper hstarDegree] at he
    exact he.symm
  exact hnotzero (heq ▸ (csInf_mem hnonempty : settingNumber starGraph ∈ feasibleSettingCounts starGraph))

def familyRegistration : Registration arena.{u}
    (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → ∀ color : V → Bool,
      (∀ u v, G.Adj u v → color u ≠ color v) →
      (∀ v, (G.neighborFinset v).card ≤ 2) →
      feasibleFiveModeCounts G = feasibleSettingCounts G ∧
        (feasibleFiveModeCounts G).Nonempty ∧
        fiveModeSettingNumber G = min 2 (nonlinearNeighborhoods G).card) where
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
    (@_root_.D5.S3.Quantum.Fibers.BipartiteBlockade.five_mode_setting_number_classification.{u})
    (Realization SettingNumber.signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber.five_mode_setting_number_classification.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize SettingNumber.signature
    (fun _ _ p => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact fiveModeSettingNumber p.graph)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber

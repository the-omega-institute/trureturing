import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Reg.Support.DependentFamily

open _root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open _root_.D5.S0.Computability.Coding.PrefixFreeCode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ENNReal

namespace Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ α : Type u, α → ℝ
  State := fun p => Set (List p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p F => codeMass p.2 F) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete source telescope and both local lets are retained. Only the
terminal total mass observation is replaced. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (_hp : ∀ a, 0 < p a) (_hsum : ∑ a, p a = 1)
    (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List α)),
    let o := fun n => priority p (tie n)
    let G := greedyCode o b
    Legal b G ∧
    (∀ N, IsGreatest {x : ℝ | ∃ F, Legal b F ∧
        (∀ v ∈ F, v.length ≤ N) ∧ x = truncatedMass p F N}
      (truncatedMass p G N)) ∧
    IsGreatest {x : ℝ≥0∞ | ∃ F, Legal b F ∧ x = codeMass p F}
      (R.readout () ⟨α, p⟩ G)

theorem singleton_legal {α : Type u} [Fintype α] [DecidableEq α] (a : α) :
    Legal (fun _ => 1) ({[a]} : Set (List α)) := by
  classical
  refine ⟨?_, by simp, ?_⟩
  · intro v hv w hw _
    simpa using (Set.mem_singleton_iff.mp hv).trans (Set.mem_singleton_iff.mp hw).symm
  · intro n
    have hs : level ({[a]} : Set (List α)) n ⊆ ({[a]} : Finset (List α)) := by
      intro v hv
      have hm : v ∈ ({[a]} : Set (List α)) := by
        exact ((@Finset.mem_filter (List α)
          (fun w => w ∈ ({[a]} : Set (List α)))
          (fun _ => Classical.propDecidable _) (words n) v).mp hv).2
      exact Finset.mem_singleton.mpr (Set.mem_singleton_iff.mp hm)
    simpa using Finset.card_le_card hs

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let a : ULift.{u} Unit := ⟨()⟩
  have hh := h (α := ULift.{u} Unit) (fun _ => 1) (by intro _; norm_num)
    (by simp) (fun _ => 1) (fun _ => inferInstance)
  have hmass : codeMass (fun _ : ULift.{u} Unit => 1)
      ({[a]} : Set (List (ULift.{u} Unit))) = 1 := by
    simp [codeMass, wordMass]
  have he := hh.2.2.2 (show (1 : ℝ≥0∞) ∈
      {x | ∃ F, Legal (fun _ => 1) F ∧ x = codeMass (fun _ : ULift.{u} Unit => 1) F} from
    ⟨{[a]}, singleton_legal a, hmass.symm⟩)
  change (1 : ℝ≥0∞) ≤ 0 at he
  exact not_le_of_gt zero_lt_one he

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨depth_budget_iid_greedy_optimality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, fun _ => 1⟩, ∅, {[]}, ?_⟩
    simp [actual, realize, codeMass, wordMass]

register_information_theorem depth_budget_iid_greedy_optimality in arena
  readout via (realize signature.{u}
    (fun _ p F => codeMass p.2 F) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality

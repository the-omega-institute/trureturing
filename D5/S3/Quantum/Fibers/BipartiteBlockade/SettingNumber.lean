/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/SettingNumber
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/SettingNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The minimum number of positive acceleration settings is the number of nonlinear neighborhoods capped at two. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery
import D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Fibers.BipartiteBlockade
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed collection of drives identifies all blockade means among actual
positive semidefinite trace-one states using occupation and acceleration data. -/
def settingsSufficient (G : SimpleGraph V) {k : ℕ} (drives : Fin k → V → ℝ) : Prop :=
  ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
    ρ.PosSemidef → Matrix.trace ρ = 1 → σ.PosSemidef → Matrix.trace σ = 1 →
    (∀ v, occupationMean G ρ v = occupationMean G σ v) →
    (∀ i v, acceleration G (drives i) ρ v = acceleration G (drives i) σ v) →
    ∀ v, blockadeMean G ρ v = blockadeMean G σ v

/-- Counts admitting predetermined strictly positive drives with the source data contract. -/
def feasibleSettingCounts (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ drives : Fin k → V → ℝ,
    (∀ i v, 0 < drives i v) ∧ settingsSufficient G drives}

/-- The least feasible count; the classification proves this set is nonempty. -/
def settingNumber (G : SimpleGraph V) : ℕ := sInf (feasibleSettingCounts G)

private theorem zero_feasible (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (empty : nonlinearNeighborhoods G = ∅) : 0 ∈ feasibleSettingCounts G := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro ρ σ _ htρ _ htσ hm _
    apply (small_setting_recovery G color proper (fun _ => 1) (by simp)).1 empty ρ σ
    · rw [htρ, htσ]
    · exact hm

private theorem one_feasible (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (one : (nonlinearNeighborhoods G).card ≤ 1) : 1 ∈ feasibleSettingCounts G := by
  refine ⟨fun _ _ => 1, by intros; norm_num, ?_⟩
  intro ρ σ _ htρ _ htσ hm ha
  apply (small_setting_recovery G color proper (fun _ => 1) (by simp)).2 one ρ σ
  · rw [htρ, htσ]
  · exact hm
  · exact ha 0

private theorem two_feasible (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) :
    2 ∈ feasibleSettingCounts G := by
  let drives : Fin 2 → V → ℝ := fun i =>
    if i = 0 then fun _ => 1 else colorScaledDrive color (fun _ => 1)
  refine ⟨drives, ?_, ?_⟩
  · intro i v
    dsimp only [drives]
    split_ifs
    · norm_num
    · dsimp only [colorScaledDrive]
      split_ifs <;> norm_num
  · intro ρ σ _ _ _ _ hm ha v
    have hρ := two_color_readout_inverse G color proper (fun _ => 1) ρ v (by norm_num)
    have hσ := two_color_readout_inverse G color proper (fun _ => 1) σ v (by norm_num)
    have h₀ : ∀ x, acceleration G (fun _ => 1) ρ x = acceleration G (fun _ => 1) σ x := by
      simpa only [drives, ite_true] using ha 0
    have h₁ : ∀ x, acceleration G (colorScaledDrive color (fun _ => 1)) ρ x =
        acceleration G (colorScaledDrive color (fun _ => 1)) σ x := by
      simpa only [drives, show (1 : Fin 2) ≠ 0 by decide, ite_false] using ha 1
    rw [hρ, hσ, hm v, h₀ v, h₁ v]

private theorem zero_infeasible (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (positive : 1 ≤ (nonlinearNeighborhoods G).card) : 0 ∉ feasibleSettingCounts G := by
  intro ⟨drives, _, sufficient⟩
  obtain ⟨N, hN⟩ := Finset.card_pos.mp positive
  obtain ⟨v, hv, _⟩ := Finset.mem_image.mp hN
  have large : 2 ≤ (G.neighborFinset v).card := (Finset.mem_filter.mp hv).2
  obtain ⟨ρ, σ, hρ, tρ, hσ, tσ, hm, hb⟩ := physical_zero_setting_lower G color proper v large
  exact hb (sufficient ρ σ hρ tρ hσ tσ hm (fun i => Fin.elim0 i) v)

private theorem one_infeasible (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (two : 2 ≤ (nonlinearNeighborhoods G).card) : 1 ∉ feasibleSettingCounts G := by
  intro ⟨drives, positive, sufficient⟩
  obtain ⟨N, hN, M, hM, distinct⟩ := Finset.one_lt_card.mp two
  obtain ⟨u, hu, huN⟩ := Finset.mem_image.mp hN
  obtain ⟨w, hw, hwM⟩ := Finset.mem_image.mp hM
  have largeU := (Finset.mem_filter.mp hu).2
  have largeW := (Finset.mem_filter.mp hw).2
  have hdistinct : G.neighborFinset u ≠ G.neighborFinset w := by
    intro he; exact distinct (huN.symm.trans (he.trans hwM))
  obtain ⟨ρ, σ, hρ, tρ, hσ, tσ, hm, ha, v, hb⟩ :=
    physical_single_setting_lower G connected color proper (drives 0)
      (fun x => ne_of_gt (positive 0 x)) u w largeU largeW hdistinct
  apply hb
  apply sufficient ρ σ hρ tρ hσ tσ
  · intro x; exact congrArg Complex.re (hm x)
  · intro i x
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact congrArg (fun z : ℂ => -z.re) (ha x)

/-- For every finite connected properly two-colored simple graph, the minimum
number of strictly positive, predetermined acceleration settings is exactly
its number of distinct nonlinear open neighborhoods, capped at two. Lower
bounds quantify over actual complex density matrices, including coherences. -/
theorem setting_number_classification (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v) :
    (feasibleSettingCounts G).Nonempty ∧
      settingNumber G = min 2 (nonlinearNeighborhoods G).card := by
  have htwo := two_feasible G color proper
  have hnonempty : (feasibleSettingCounts G).Nonempty := ⟨2, htwo⟩
  refine ⟨hnonempty, ?_⟩
  apply (csInf_eq_iff hnonempty _).mpr
  constructor
  · by_cases hzero : (nonlinearNeighborhoods G).card = 0
    · have hempty : nonlinearNeighborhoods G = ∅ := Finset.card_eq_zero.mp hzero
      simpa only [hzero, Nat.min_zero] using zero_feasible G color proper hempty
    · by_cases hone : (nonlinearNeighborhoods G).card = 1
      · simpa only [hone, show min 2 1 = 1 by decide] using
          one_feasible G color proper (by omega)
      · have hlarge : 2 ≤ (nonlinearNeighborhoods G).card := by omega
        simpa only [min_eq_left hlarge] using htwo
  · intro k hk
    by_contra h
    have hk' : k < min 2 (nonlinearNeighborhoods G).card := by omega
    have ksmall : k = 0 ∨ k = 1 := by omega
    rcases ksmall with rfl | rfl
    · exact zero_infeasible G color proper (by omega) hk
    · exact one_infeasible G connected color proper (by omega) hk

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.setting_number_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setting_number_classification
end D5.S3.Quantum.Fibers.BipartiteBlockade

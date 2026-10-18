/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/FiveModeSettingNumber
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/FiveModeSettingNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: In degree at most two, recovering all five-mode Born laws has the same sharp positive-drive setting number. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.SettingNumber

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Fibers.BipartiteBlockade
open private small_vertex_recovery from D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every degree-two center's entire Born marginal is identified by the same
fixed occupations and acceleration data among actual density matrices. -/
def fiveModeSettingsSufficient (G : SimpleGraph V) {k : ℕ}
    (drives : Fin k → V → ℝ) : Prop :=
  ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
    ρ.PosSemidef → Matrix.trace ρ = 1 → σ.PosSemidef → Matrix.trace σ = 1 →
    (∀ v, occupationMean G ρ v = occupationMean G σ v) →
    (∀ i v, acceleration G (drives i) ρ v = acceleration G (drives i) σ v) →
    ∀ u v w, (∀ x, G.Adj v x ↔ x = u ∨ x = w) → u ≠ w →
      bornModeLaw G u v w ρ = bornModeLaw G u v w σ

/-- Feasible positive-drive counts for the entire five-mode law contract. -/
def feasibleFiveModeCounts (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ drives : Fin k → V → ℝ,
    (∀ i v, 0 < drives i v) ∧ fiveModeSettingsSufficient G drives}

/-- The minimum count for all degree-two five-mode Born marginals. -/
def fiveModeSettingNumber (G : SimpleGraph V) : ℕ := sInf (feasibleFiveModeCounts G)

private theorem five_formula (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ = 1) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (huw : u ≠ w) :
    bornModeLaw G u v w ρ =
      ![blockadeMean G ρ v - occupationMean G ρ v,
        1 - blockadeMean G ρ v - occupationMean G ρ w,
        occupationMean G ρ v,
        1 - blockadeMean G ρ v - occupationMean G ρ u,
        blockadeMean G ρ v - 1 + occupationMean G ρ u + occupationMean G ρ w] := by
  have h := (born_five_mode_reconstruction G u v w hN huw color proper
    (fun _ => 1) (by norm_num) ρ hρ ht).2.2.1
  rw [← two_color_readout_inverse G color proper (fun _ => 1) ρ v (by norm_num)] at h
  exact h

private theorem five_contract_iff (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (degree : ∀ v, (G.neighborFinset v).card ≤ 2) {k : ℕ}
    (drives : Fin k → V → ℝ) :
    fiveModeSettingsSufficient G drives ↔ settingsSufficient G drives := by
  constructor
  · intro sufficient ρ σ hρ htρ hσ htσ hm ha v
    by_cases hsmall : (G.neighborFinset v).card ≤ 1
    · exact small_vertex_recovery G ρ σ (by rw [htρ, htσ]) hm v hsmall
    · have htwo : (G.neighborFinset v).card = 2 := by have := degree v; omega
      obtain ⟨u, w, huw, hNset⟩ := Finset.card_eq_two.mp htwo
      have hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w := by
        intro x
        rw [← SimpleGraph.mem_neighborFinset, hNset]
        simp
      have he := congrFun (sufficient ρ σ hρ htρ hσ htσ hm ha u v w hN huw) 0
      rw [five_formula G color proper ρ hρ htρ u v w hN huw,
        five_formula G color proper σ hσ htσ u v w hN huw] at he
      simp only [Matrix.cons_val_zero] at he
      linarith [hm v]
  · intro sufficient ρ σ hρ htρ hσ htσ hm ha u v w hN huw
    have hb := sufficient ρ σ hρ htρ hσ htσ hm ha
    rw [five_formula G color proper ρ hρ htρ u v w hN huw,
      five_formula G color proper σ hσ htσ u v w hN huw,
      hb v, hm u, hm v, hm w]

/-- In a finite connected bipartite graph of maximum degree two, the feasible
settings for all degree-two five-mode laws and all blockades coincide. Their
common minimum is min(2,d), with d the number of distinct nonlinear neighborhoods. -/
theorem five_mode_setting_number_classification (G : SimpleGraph V)
    (connected : G.Connected) (color : V → Bool)
    (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (degree : ∀ v, (G.neighborFinset v).card ≤ 2) :
    feasibleFiveModeCounts G = feasibleSettingCounts G ∧
      (feasibleFiveModeCounts G).Nonempty ∧
      fiveModeSettingNumber G = min 2 (nonlinearNeighborhoods G).card := by
  have heq : feasibleFiveModeCounts G = feasibleSettingCounts G := by
    ext k
    constructor
    · rintro ⟨drives, positive, sufficient⟩
      exact ⟨drives, positive, (five_contract_iff G color proper degree drives).mp sufficient⟩
    · rintro ⟨drives, positive, sufficient⟩
      exact ⟨drives, positive, (five_contract_iff G color proper degree drives).mpr sufficient⟩
  have hc := setting_number_classification G connected color proper
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]; exact hc.1
  · change sInf (feasibleFiveModeCounts G) = _
    rw [heq]
    exact hc.2

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.five_mode_setting_number_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms five_mode_setting_number_classification
end D5.S3.Quantum.Fibers.BipartiteBlockade

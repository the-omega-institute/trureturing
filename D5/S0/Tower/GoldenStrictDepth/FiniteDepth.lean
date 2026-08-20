/- GID: D5/S0/Tower/GoldenStrictDepth/FiniteDepth
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenStrictDepth/FiniteDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite strict golden backward-survivor depth is nonempty. -/

import D5.S0.Tower.Champions.GoldenPermanentSurvivors

/- Library-search audit trail (2026-08-18):
   * Repository search found the strict permanent set proved empty
     (`golden_strict_permanent_set_eq_empty`) and every champion identity used
     below, but no statement about individual finite depths.
   * Emptiness of the all-depth intersection does not decide any finite level:
     the levels are open sets, so the nested intersection may be empty while
     every level is nonempty.  This file supplies that separation.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`, `pow_pos`, and ordered-field
     lemmas; no external theorem specializes to this piecewise golden map. -/

namespace D5.S0.Tower.GoldenStrictDepth.FiniteDepth

open D5.S0.Tower.Champions.GoldenSurvivorTubes

local notation "φ" => Real.goldenRatio

/-- The uniform perturbation budget for the boundary period-three orbit. -/
noncomputable def goldenPerturbationBudget : Real :=
  goldenThreshold * goldenInverse ^ 2

theorem golden_threshold_pos : 0 < goldenThreshold := by
  rw [golden_threshold_eq]
  have := golden_inverse_pos
  positivity

theorem golden_one_sub_threshold : 1 - goldenThreshold = φ / 2 := by
  rw [golden_threshold_eq, golden_inverse_sq]; ring

theorem golden_phi_mul_threshold : φ * goldenThreshold = goldenInverse / 2 := by
  rw [golden_threshold_eq]
  calc φ * (goldenInverse ^ 2 / 2)
      = goldenInverse * φ * goldenInverse / 2 := by ring
    _ = goldenInverse / 2 := by rw [golden_inverse_mul]; ring

theorem golden_threshold_eq_half_one_sub_inverse :
    goldenThreshold = (1 - goldenInverse) / 2 := by
  rw [golden_threshold_eq, golden_inverse_sq, golden_inverse_eq_sub_one]; ring

theorem golden_perturbation_budget_pos : 0 < goldenPerturbationBudget := by
  have := golden_threshold_pos
  have := golden_inverse_pos
  rw [goldenPerturbationBudget]
  positivity

theorem golden_budget_lt_threshold :
    goldenPerturbationBudget < goldenThreshold := by
  have hpos := golden_threshold_pos
  have hgi := golden_inverse_pos
  have hlt := golden_inverse_lt_one
  have hsq : goldenInverse ^ 2 < 1 := by nlinarith
  rw [goldenPerturbationBudget]
  nlinarith

theorem golden_budget_lt_threshold_mul_inverse :
    goldenPerturbationBudget < goldenThreshold * goldenInverse := by
  have hpos := golden_threshold_pos
  have hgi := golden_inverse_pos
  have hlt := golden_inverse_lt_one
  have hsq : goldenInverse ^ 2 < goldenInverse := by nlinarith
  rw [goldenPerturbationBudget]
  nlinarith

theorem golden_threshold_lt_half : goldenThreshold < 1 / 2 := by
  rw [golden_threshold_eq]
  have hgi := golden_inverse_pos
  have hlt := golden_inverse_lt_one
  nlinarith

theorem golden_budget_lt_inverse_half :
    goldenPerturbationBudget < goldenInverse / 2 := by
  have hpos := golden_threshold_pos
  have hgi := golden_inverse_pos
  have hlt := golden_inverse_lt_one
  have hhalf := golden_threshold_lt_half
  rw [goldenPerturbationBudget]
  nlinarith

theorem golden_budget_lt_inverse : goldenPerturbationBudget < goldenInverse := by
  have := golden_budget_lt_inverse_half
  have := golden_inverse_pos
  linarith

/-- Membership of a large state, stated through the two-sided window. -/
theorem golden_large_mem (u : Real)
    (hlow : goldenThreshold < u) (hhigh : u < 1 - goldenThreshold) :
    (⟨.large, u⟩ : GoldenSurvivorState) ∈ goldenStrictSurvivorSet := by
  change goldenThreshold < goldenStateArm ⟨.large, u⟩
  simp only [goldenStateArm, lt_min_iff]
  exact ⟨hlow, by linarith⟩

/-- Membership of a small state, whose arm carries the inverse scaling. -/
theorem golden_small_mem (u : Real)
    (hlow : φ * goldenThreshold < u) (hhigh : u < 1 - φ * goldenThreshold) :
    (⟨.small, u⟩ : GoldenSurvivorState) ∈ goldenStrictSurvivorSet := by
  change goldenThreshold < goldenStateArm ⟨.small, u⟩
  simp only [goldenStateArm]
  have hgi := golden_inverse_pos
  have hmin : φ * goldenThreshold < min u (1 - u) := by
    rw [lt_min_iff]; exact ⟨hlow, by linarith⟩
  calc goldenThreshold = goldenInverse * (φ * goldenThreshold) := by
        rw [← mul_assoc, golden_inverse_mul, one_mul]
    _ < goldenInverse * min u (1 - u) := by
        exact mul_lt_mul_of_pos_left hmin hgi

theorem golden_one_le_phi : (1 : Real) ≤ φ := le_of_lt Real.one_lt_goldenRatio

theorem golden_one_le_pow (n : Nat) : (1 : Real) ≤ φ ^ n :=
  one_le_pow₀ golden_one_le_phi

/-- The three perturbed phases of the boundary period-three orbit all survive to
every finite strict depth, provided the perturbation stays inside the budget
after being expanded `n` times. -/
theorem golden_perturbed_champion_mem :
    ∀ (n : Nat) (a : Real), 0 < a → φ ^ n * a < goldenPerturbationBudget →
      (⟨.large, (1 - goldenThreshold) - a⟩ : GoldenSurvivorState) ∈
          goldenBackwardSurvivor goldenStrictSurvivorSet n ∧
        (⟨.small, 1 / 2 - φ * a⟩ : GoldenSurvivorState) ∈
          goldenBackwardSurvivor goldenStrictSurvivorSet n ∧
        (⟨.large, 1 / 2 - a⟩ : GoldenSurvivorState) ∈
          goldenBackwardSurvivor goldenStrictSurvivorSet n := by
  intro n
  induction n with
  | zero =>
      intro a hpos hbound
      have hsmall : a < goldenPerturbationBudget := by simpa using hbound
      exact ⟨goldenLargeA a hpos hsmall, goldenSmallB a hpos hsmall,
        goldenLargeC a hpos hsmall⟩
  | succ n ih =>
      intro a hpos hbound
      have hphi : (0 : Real) < φ := lt_of_lt_of_le zero_lt_one golden_one_le_phi
      have hstep : φ ^ n * (φ * a) < goldenPerturbationBudget := by
        have hrw : φ ^ n * (φ * a) = φ ^ (n + 1) * a := by ring
        rw [hrw]; exact hbound
      have hnext := ih (φ * a) (mul_pos hphi hpos) hstep
      have hsmall : a < goldenPerturbationBudget := by
        have hge : a ≤ φ ^ (n + 1) * a := by
          nlinarith [golden_one_le_pow (n + 1), hpos]
        linarith
      refine ⟨?_, ?_, ?_⟩
      · rw [golden_backward_survivor_succ]
        refine ⟨goldenLargeA a hpos hsmall, ?_⟩
        rw [Set.mem_preimage]
        have hbranch : ¬ ((1 - goldenThreshold) - a ≤ goldenInverse) := by
          have hone := golden_one_sub_threshold
          have hinv := golden_inverse_eq_sub_one
          have hbud := golden_budget_lt_threshold
          have hthr : goldenThreshold = 1 - φ / 2 := by linarith [hone]
          refine not_le.mpr ?_
          rw [hinv]
          linarith [hone, hthr]
        simp only [goldenTransition, if_neg hbranch]
        have hrw : φ ^ 2 * ((1 - goldenThreshold) - a) - φ = 1 / 2 - φ * (φ * a) := by
          have hone := golden_one_sub_threshold
          have hsq := Real.goldenRatio_sq
          nlinarith [hone, hsq]
        rw [hrw]
        exact hnext.2.1
      · rw [golden_backward_survivor_succ]
        refine ⟨goldenSmallB a hpos hsmall, ?_⟩
        rw [Set.mem_preimage]
        simp only [goldenTransition]
        exact hnext.2.2
      · rw [golden_backward_survivor_succ]
        refine ⟨goldenLargeC a hpos hsmall, ?_⟩
        rw [Set.mem_preimage]
        have hbranch : (1 : Real) / 2 - a ≤ goldenInverse := by
          have := golden_half_le_inverse
          linarith
        simp only [goldenTransition, if_pos hbranch]
        have hrw : φ * (1 / 2 - a) = (1 - goldenThreshold) - φ * a := by
          have hone := golden_one_sub_threshold
          linarith [hone]
        rw [hrw]
        exact hnext.1
where
  goldenLargeA (a : Real) (hpos : 0 < a) (hsmall : a < goldenPerturbationBudget) :
      (⟨.large, (1 - goldenThreshold) - a⟩ : GoldenSurvivorState) ∈
        goldenStrictSurvivorSet := by
    have hinv := golden_inverse_eq_sub_one
    have hone := golden_one_sub_threshold
    have hbud := golden_budget_lt_inverse
    refine golden_large_mem _ ?_ (by linarith)
    have h2 : (1 : Real) - 2 * goldenThreshold = goldenInverse := by
      rw [hinv]; linarith [hone]
    linarith [h2]
  goldenSmallB (a : Real) (hpos : 0 < a) (hsmall : a < goldenPerturbationBudget) :
      (⟨.small, 1 / 2 - φ * a⟩ : GoldenSurvivorState) ∈ goldenStrictSurvivorSet := by
    have hmul := golden_phi_mul_threshold
    have hbud := golden_budget_lt_threshold_mul_inverse
    have hgi := golden_inverse_pos
    have hgilt := golden_inverse_lt_one
    have hthr := golden_threshold_pos
    have hphimul := golden_inverse_mul
    have hphi : (0 : Real) < φ := lt_of_lt_of_le zero_lt_one golden_one_le_phi
    have hkey : φ * a < goldenThreshold := by nlinarith
    have hthreq := golden_threshold_eq_half_one_sub_inverse
    have hpa : 0 < φ * a := mul_pos hphi hpos
    refine golden_small_mem _ ?_ ?_
    · rw [hmul]; linarith
    · rw [hmul]; linarith
  goldenLargeC (a : Real) (hpos : 0 < a) (hsmall : a < goldenPerturbationBudget) :
      (⟨.large, 1 / 2 - a⟩ : GoldenSurvivorState) ∈ goldenStrictSurvivorSet := by
    have hone := golden_one_sub_threshold
    have hbud := golden_budget_lt_inverse_half
    have hinv := golden_inverse_eq_sub_one
    have hthr := golden_threshold_pos
    refine golden_large_mem _ ?_ (by linarith)
    have hhalf : (1 : Real) / 2 - goldenThreshold = goldenInverse / 2 := by
      rw [hinv]; linarith [hone]
    linarith [hhalf]

/-- Every finite strict golden backward-survivor depth is nonempty. -/
theorem golden_strict_backward_survivor_nonempty (n : Nat) :
    (goldenBackwardSurvivor goldenStrictSurvivorSet n).Nonempty := by
  have hpowpos : (0 : Real) < φ ^ n :=
    pow_pos (lt_of_lt_of_le zero_lt_one golden_one_le_phi) n
  have hbudget := golden_perturbation_budget_pos
  refine ⟨⟨.large,
    (1 - goldenThreshold) - goldenPerturbationBudget / (2 * φ ^ n)⟩, ?_⟩
  refine (golden_perturbed_champion_mem n _ (by positivity) ?_).1
  have hcancel : φ ^ n * (goldenPerturbationBudget / (2 * φ ^ n)) =
      goldenPerturbationBudget / 2 := by
    field_simp
  rw [hcancel]
  linarith

/-- In particular depth sixty is nonempty. -/
theorem golden_strict_backward_survivor_sixty_nonempty :
    (goldenBackwardSurvivor goldenStrictSurvivorSet 60).Nonempty :=
  golden_strict_backward_survivor_nonempty 60

/-- The separation statement: every finite depth is nonempty even though the
all-depth intersection is empty. -/
theorem golden_finite_depths_nonempty_and_permanent_empty :
    (∀ n : Nat, (goldenBackwardSurvivor goldenStrictSurvivorSet n).Nonempty) ∧
      D5.S0.Tower.Champions.GoldenPermanentSurvivors.goldenStrictPermanentSet = ∅ :=
  ⟨golden_strict_backward_survivor_nonempty,
    D5.S0.Tower.Champions.GoldenPermanentSurvivors.golden_strict_permanent_set_eq_empty⟩

end D5.S0.Tower.GoldenStrictDepth.FiniteDepth

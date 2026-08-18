/- GID: D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciSurvivors/StrictFiniteDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite strict Tribonacci backward-survivor depth is nonempty. -/

import D5.S0.Tower.TribonacciSurvivors.TribonacciPermanentSurvivors

/- Library-search audit trail (2026-08-18):
   * Repository search found the strict permanent set proved empty
     (`tribonacci_strict_permanent_set_eq_empty`) and every champion identity
     used below, but no statement about individual finite depths.
   * Emptiness of the all-depth intersection does not decide any finite level:
     the levels here are open sets, so the nested intersection may be empty
     while every level is nonempty.  This file supplies that separation.
   * Pinned Mathlib supplies only `pow_pos` and ordered-field lemmas; no
     external theorem specializes to this transition. -/

namespace D5.S0.Tower.TribonacciSurvivors.StrictFiniteDepth

open D5.S0.Tower.TribonacciSurvivors.TribonacciPermanentSurvivors
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "State" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState
local notation "transition" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition
local notation "gapLength" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength


/-- The uniform perturbation budget: the slack of the middle champion
coordinate above the strict threshold. -/
noncomputable def tribonacciPerturbationBudget : Real :=
  tribonacciMiddleCoordinate - tribonacciThreshold

theorem tribonacci_perturbation_budget_pos : 0 < tribonacciPerturbationBudget := by
  have h := tribonacci_threshold_lt_middle
  simp only [tribonacciPerturbationBudget]
  linarith

/-- The budget stays below the threshold, so a perturbed large coordinate never
crosses the left branch boundary. -/
theorem tribonacci_perturbation_budget_lt_threshold :
    tribonacciPerturbationBudget < tribonacciThreshold := by
  have hlow := tribonacci_nine_fifths_lt
  have hhigh := tribonacci_lt_forty_six_fifths
  have hpos : (0 : Real) < t := by linarith
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
  have hkey : t - 1 < 2 * (1 - t⁻¹) := by nlinarith
  simp only [tribonacciPerturbationBudget, tribonacciMiddleCoordinate, tribonacciThreshold]
  linarith

/-- The large champion coordinate sits exactly one threshold above the branch
boundary. -/
theorem tribonacci_large_sub_inverse :
    tribonacciLargeCoordinate - t⁻¹ = tribonacciThreshold := by
  have hcomp := tribonacci_large_complement
  simp only [tribonacciThreshold] at hcomp ⊢
  linarith

theorem tribonacci_one_le_constant : (1 : Real) ≤ t :=
  le_of_lt D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant

theorem tribonacci_one_le_pow (n : Nat) : (1 : Real) ≤ t ^ n :=
  one_le_pow₀ tribonacci_one_le_constant

/-- The two perturbed champion states of the period-two orbit both survive to
every finite strict depth, provided the perturbation stays inside the budget
after being expanded `n` times. -/
theorem tribonacci_perturbed_champion_mem :
    ∀ (n : Nat) (eps : Real), 0 < eps → t ^ n * eps < tribonacciPerturbationBudget →
      (⟨.large, tribonacciLargeCoordinate - eps⟩ : State) ∈
          tribonacciBackwardSurvivor tribonacciStrictSurvivorSet n ∧
        (⟨.combined, tribonacciMiddleCoordinate - eps⟩ : State) ∈
          tribonacciBackwardSurvivor tribonacciStrictSurvivorSet n := by
  intro n
  induction n with
  | zero =>
      intro eps hpos hbound
      have hsmall : eps < tribonacciPerturbationBudget := by
        simpa using hbound
      have hmid := tribonacci_threshold_lt_middle
      have hlarge := tribonacci_middle_lt_large
      have hcomp := tribonacci_large_complement
      have hmid2 : t - 1 = 2 * tribonacciMiddleCoordinate := by
        simp only [tribonacciMiddleCoordinate]; ring
      have hbudget : tribonacciPerturbationBudget =
          tribonacciMiddleCoordinate - tribonacciThreshold := rfl
      constructor
      · show (⟨.large, tribonacciLargeCoordinate - eps⟩ : State) ∈
          tribonacciStrictSurvivorSet
        rw [tribonacci_strict_mem_iff]
        refine ⟨by rw [hbudget] at hsmall; linarith, ?_⟩
        simp only [tribonacciPeriodicGapLength]
        linarith
      · show (⟨.combined, tribonacciMiddleCoordinate - eps⟩ : State) ∈
          tribonacciStrictSurvivorSet
        rw [tribonacci_strict_mem_iff]
        refine ⟨by rw [hbudget] at hsmall; linarith, ?_⟩
        simp only [tribonacciPeriodicGapLength]
        linarith [hmid2]
  | succ n ih =>
      intro eps hpos hbound
      have hpowpos : (0 : Real) < t ^ n :=
        pow_pos (lt_of_lt_of_le zero_lt_one tribonacci_one_le_constant) n
      have htpos : (0 : Real) < t :=
        lt_of_lt_of_le zero_lt_one tribonacci_one_le_constant
      have hstep : t ^ n * (t * eps) < tribonacciPerturbationBudget := by
        have hrw : t ^ n * (t * eps) = t ^ (n + 1) * eps := by ring
        rw [hrw]; exact hbound
      have hnext := ih (t * eps) (mul_pos htpos hpos) hstep
      have hsmall : eps < tribonacciPerturbationBudget := by
        have hge : eps ≤ t ^ (n + 1) * eps := by
          nlinarith [tribonacci_one_le_pow (n + 1), hpos]
        linarith
      have hmid := tribonacci_threshold_lt_middle
      have hlarge := tribonacci_middle_lt_large
      have hcomp := tribonacci_large_complement
      have hmid2 : t - 1 = 2 * tribonacciMiddleCoordinate := by
        simp only [tribonacciMiddleCoordinate]; ring
      have hbudget : tribonacciPerturbationBudget =
          tribonacciMiddleCoordinate - tribonacciThreshold := rfl
      have hbudlt := tribonacci_perturbation_budget_lt_threshold
      constructor
      · rw [tribonacci_backward_survivor_succ]
        refine ⟨?_, ?_⟩
        · rw [tribonacci_strict_mem_iff]
          refine ⟨by rw [hbudget] at hsmall; linarith, ?_⟩
          simp only [tribonacciPeriodicGapLength]
          linarith
        · rw [Set.mem_preimage]
          have hbranch : ¬ (tribonacciLargeCoordinate - eps ≤ t⁻¹) := by
            have := tribonacci_large_sub_inverse
            push_neg
            linarith
          simp only [tribonacciPeriodicTransition, if_neg hbranch]
          have hrw : t * (tribonacciLargeCoordinate - eps) - 1 =
              tribonacciMiddleCoordinate - t * eps := by
            have := tribonacci_large_branch
            linarith [this]
          rw [hrw]
          exact hnext.2
      · rw [tribonacci_backward_survivor_succ]
        refine ⟨?_, ?_⟩
        · rw [tribonacci_strict_mem_iff]
          refine ⟨by rw [hbudget] at hsmall; linarith, ?_⟩
          simp only [tribonacciPeriodicGapLength]
          linarith [hmid2]
        · rw [Set.mem_preimage]
          have hbranch : tribonacciMiddleCoordinate - eps ≤ t⁻¹ := by
            have := tribonacci_middle_le_inverse
            linarith
          simp only [tribonacciPeriodicTransition, if_pos hbranch]
          have hrw : t * (tribonacciMiddleCoordinate - eps) =
              tribonacciLargeCoordinate - t * eps := by
            have := tribonacci_middle_scale
            linarith [this]
          rw [hrw]
          exact hnext.1

/-- Every finite strict backward-survivor depth is nonempty. -/
theorem tribonacci_strict_backward_survivor_nonempty (n : Nat) :
    (tribonacciBackwardSurvivor tribonacciStrictSurvivorSet n).Nonempty := by
  have hpowpos : (0 : Real) < t ^ n :=
    pow_pos (lt_of_lt_of_le zero_lt_one tribonacci_one_le_constant) n
  have hbudget := tribonacci_perturbation_budget_pos
  refine ⟨⟨.large,
    tribonacciLargeCoordinate - tribonacciPerturbationBudget / (2 * t ^ n)⟩, ?_⟩
  refine (tribonacci_perturbed_champion_mem n _ (by positivity) ?_).1
  have hcancel : t ^ n * (tribonacciPerturbationBudget / (2 * t ^ n)) =
      tribonacciPerturbationBudget / 2 := by
    field_simp
  rw [hcancel]
  linarith

/-- In particular depth sixty is nonempty: the strict forbidden region does not
become empty at any announced finite depth. -/
theorem tribonacci_strict_backward_survivor_sixty_nonempty :
    (tribonacciBackwardSurvivor tribonacciStrictSurvivorSet 60).Nonempty :=
  tribonacci_strict_backward_survivor_nonempty 60

/-- The separation statement: every finite depth is nonempty even though the
all-depth intersection is empty. -/
theorem tribonacci_finite_depths_nonempty_and_permanent_empty :
    (∀ n : Nat, (tribonacciBackwardSurvivor tribonacciStrictSurvivorSet n).Nonempty) ∧
      tribonacciStrictPermanentSet = ∅ :=
  ⟨tribonacci_strict_backward_survivor_nonempty, tribonacci_strict_permanent_set_eq_empty⟩

end D5.S0.Tower.TribonacciSurvivors.StrictFiniteDepth

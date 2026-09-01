/- GID: D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict Tribonacci permanent survival is empty; the closed carrier is nonempty. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin

/- Library-search audit trail (2026-08-17):
   * Repository search found the exact Tribonacci transition, champion
     period-two orbit, finite periodic enumeration through period five, and
     periodic maximin, but no arbitrary-orbit permanent-survivor theorem.
   * Pinned Mathlib supplies `exists_pow_lt_of_lt_one` for the geometric
     contraction step. No external theorem specializes it to this transition.
   * The finite periodic enumeration is not used as arbitrary-orbit
     completeness; the expanding-map argument below is proved directly. -/

namespace D5.S0.Tower.TribonacciSurvivors.TribonacciPermanentSurvivors

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "State" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState
local notation "transition" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition
local notation "gapLength" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength
local notation "stateArm" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin.tribonacciPeriodicStateArm

/-- The strict Tribonacci threshold, equal to the period-two champion value. -/
noncomputable def tribonacciThreshold : Real := (1 - t⁻¹) / 2

/-- States whose nearer normalized arm lies strictly above the threshold. -/
def tribonacciStrictSurvivorSet : Set State :=
  {state | tribonacciThreshold < stateArm state}

/-- The corresponding closed threshold domain. -/
def tribonacciClosedSurvivorSet : Set State :=
  {state | tribonacciThreshold ≤ stateArm state}

/-- Finite backward survival under the deterministic three-gap transition. -/
noncomputable def tribonacciBackwardSurvivor (F : Set State) : Nat → Set State
  | 0 => F
  | n + 1 => F ∩ transition ⁻¹' tribonacciBackwardSurvivor F n

/-- States that survive every finite backward depth for the strict threshold. -/
def tribonacciStrictPermanentSet : Set State :=
  {state | ∀ n, state ∈ tribonacciBackwardSurvivor tribonacciStrictSurvivorSet n}

/-- States that survive every finite backward depth for the closed threshold. -/
def tribonacciClosedPermanentSet : Set State :=
  {state | ∀ n, state ∈ tribonacciBackwardSurvivor tribonacciClosedSurvivorSet n}

/-- The large and combined coordinates of the threshold period-two orbit. -/
noncomputable def tribonacciLargeCoordinate : Real := (t ^ 2 - t) / 2

noncomputable def tribonacciMiddleCoordinate : Real := (t - 1) / 2

noncomputable def tribonacciChampionLargeState : State :=
  ⟨.large, tribonacciLargeCoordinate⟩

noncomputable def tribonacciChampionCombinedState : State :=
  ⟨.combined, tribonacciMiddleCoordinate⟩

/-- The reciprocal square is the contraction factor for one backward
`large -> combined -> large` cycle. -/
noncomputable def tribonacciPairContraction : Real := (t ^ 2)⁻¹

theorem tribonacci_threshold_eq_championValue :
    tribonacciThreshold =
      D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue t := by
  rw [D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue_tribonacciConstant]
  rfl

theorem tribonacci_backward_survivor_succ (F : Set State) (n : Nat) :
    tribonacciBackwardSurvivor F (n + 1) =
      F ∩ transition ⁻¹' tribonacciBackwardSurvivor F n := by
  simp [tribonacciBackwardSurvivor]

theorem tribonacci_strict_mem_iff (state : State) :
    state ∈ tribonacciStrictSurvivorSet ↔
      tribonacciThreshold < state.coordinate ∧
        state.coordinate < gapLength state.kind - tribonacciThreshold := by
  rw [tribonacciStrictSurvivorSet]
  change tribonacciThreshold <
      min state.coordinate (gapLength state.kind - state.coordinate) ↔ _
  rw [lt_min_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

theorem tribonacci_closed_mem_iff (state : State) :
    state ∈ tribonacciClosedSurvivorSet ↔
      tribonacciThreshold ≤ state.coordinate ∧
        state.coordinate ≤ gapLength state.kind - tribonacciThreshold := by
  rw [tribonacciClosedSurvivorSet]
  change tribonacciThreshold ≤
      min state.coordinate (gapLength state.kind - state.coordinate) ↔ _
  rw [le_min_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

theorem tribonacci_threshold_pos : 0 < tribonacciThreshold := by
  simpa only [tribonacciThreshold, zpow_neg, zpow_one] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_low_pos

theorem tribonacci_threshold_lt_middle :
    tribonacciThreshold < tribonacciMiddleCoordinate := by
  simpa only [tribonacciThreshold, tribonacciMiddleCoordinate, zpow_neg, zpow_one] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_low_lt_middle

theorem tribonacci_middle_lt_large :
    tribonacciMiddleCoordinate < tribonacciLargeCoordinate := by
  simpa only [tribonacciMiddleCoordinate, tribonacciLargeCoordinate] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_middle_lt_large

theorem tribonacci_threshold_scale :
    t * tribonacciThreshold = tribonacciMiddleCoordinate := by
  simpa only [tribonacciThreshold, tribonacciMiddleCoordinate, zpow_neg, zpow_one] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_low_to_middle

theorem tribonacci_middle_scale :
    t * tribonacciMiddleCoordinate = tribonacciLargeCoordinate := by
  simpa only [tribonacciMiddleCoordinate, tribonacciLargeCoordinate] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_middle_to_large

theorem tribonacci_large_branch :
    t * tribonacciLargeCoordinate - 1 = tribonacciMiddleCoordinate := by
  simpa only [tribonacciLargeCoordinate, tribonacciMiddleCoordinate] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_large_branch

theorem tribonacci_large_complement :
    1 - tribonacciLargeCoordinate = tribonacciThreshold := by
  simpa only [tribonacciLargeCoordinate, tribonacciThreshold, zpow_neg, zpow_one] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_large_complement

theorem tribonacci_threshold_scale_two :
    t ^ 2 * tribonacciThreshold = tribonacciLargeCoordinate := by
  calc
    t ^ 2 * tribonacciThreshold = t * (t * tribonacciThreshold) := by ring
    _ = t * tribonacciMiddleCoordinate := by rw [tribonacci_threshold_scale]
    _ = tribonacciLargeCoordinate := tribonacci_middle_scale

theorem tribonacci_nine_fifths_lt : (9 : Real) / 5 < t := by
  have h :=
    D5.S0.Tower.DBonacciGeneral.ChampionValue.dbonacci_three_root_numeric_bounds.1
  rw [D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
    at h
  norm_num at h ⊢
  linarith

theorem tribonacci_lt_forty_six_fifths : t < (46 : Real) / 25 := by
  have h :=
    D5.S0.Tower.DBonacciGeneral.ChampionValue.dbonacci_three_root_numeric_bounds.2
  rw [D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
    at h
  norm_num at h ⊢
  linarith

theorem tribonacci_middle_le_inverse : tribonacciMiddleCoordinate ≤ t⁻¹ := by
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial]
  have hfactor :
      0 < (t - (9 : Real) / 5) * (2 * (t + (9 : Real) / 5) - 3) :=
    mul_pos (sub_pos.mpr tribonacci_nine_fifths_lt) (by
      nlinarith [D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant])
  simp only [tribonacciMiddleCoordinate]
  nlinarith

theorem tribonacci_inverse_lt_large : t⁻¹ < tribonacciLargeCoordinate := by
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial]
  have hfactor : 0 < (2 - t) * (t + 1) :=
    mul_pos
      (sub_pos.mpr D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two)
      (by nlinarith [D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant])
  simp only [tribonacciLargeCoordinate]
  nlinarith

theorem tribonacci_combined_right_upper_lt_threshold :
    t * (t - 1 - tribonacciThreshold) - 1 < tribonacciThreshold := by
  rw [tribonacciThreshold,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial]
  have hfactor :
      0 < ((46 : Real) / 25 - t) *
        (3 * ((46 : Real) / 25 + t) - 4) :=
    mul_pos (sub_pos.mpr tribonacci_lt_forty_six_fifths) (by
      nlinarith [D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant])
  nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]

theorem tribonacci_pair_contraction_pos : 0 < tribonacciPairContraction := by
  rw [tribonacciPairContraction]
  exact inv_pos.mpr
    (sq_pos_of_pos D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos)

theorem tribonacci_pair_contraction_lt_one : tribonacciPairContraction < 1 := by
  rw [tribonacciPairContraction]
  apply inv_lt_one_of_one_lt₀
  nlinarith [D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant]

theorem tribonacci_pair_contraction_identity (u : Real) :
    tribonacciLargeCoordinate - u =
      tribonacciPairContraction *
        (tribonacciLargeCoordinate - (t ^ 2 * u - t)) := by
  rw [tribonacciPairContraction, tribonacciLargeCoordinate]
  field_simp [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero]
  nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]

theorem tribonacci_strict_permanent_mem (state : State)
    (hstate : state ∈ tribonacciStrictPermanentSet) :
    state ∈ tribonacciStrictSurvivorSet := by
  exact hstate 0

theorem tribonacci_strict_permanent_transition (state : State)
    (hstate : state ∈ tribonacciStrictPermanentSet) :
    transition state ∈ tribonacciStrictPermanentSet := by
  intro n
  have hnext := hstate (n + 1)
  rw [tribonacci_backward_survivor_succ] at hnext
  exact hnext.2

/-- A strict permanent large state on the right branch returns after two
steps to a right-branch large state. -/
theorem tribonacci_alternating_large_step (u : Real)
    (hpermanent : (⟨.large, u⟩ : State) ∈ tribonacciStrictPermanentSet)
    (hright : t⁻¹ < u) :
    (⟨.large, t ^ 2 * u - t⟩ : State) ∈ tribonacciStrictPermanentSet ∧
      t⁻¹ < t ^ 2 * u - t := by
  have hcombined := tribonacci_strict_permanent_transition _ hpermanent
  simp only [
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
    if_neg (not_le.mpr hright)] at hcombined
  have hcombinedStrict := tribonacci_strict_permanent_mem _ hcombined
  have hcombinedBounds := tribonacci_strict_mem_iff _ |>.mp hcombinedStrict
  change tribonacciThreshold < t * u - 1 ∧
    t * u - 1 < t - 1 - tribonacciThreshold at hcombinedBounds
  have hcombinedLeft : t * u - 1 ≤ t⁻¹ := by
    by_contra hnot
    have hsmall := tribonacci_strict_permanent_transition _ hcombined
    simp only [
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
      if_neg hnot] at hsmall
    have hsmallBounds :=
      tribonacci_strict_mem_iff _ |>.mp (tribonacci_strict_permanent_mem _ hsmall)
    change tribonacciThreshold < t * (t * u - 1) - 1 ∧ _ at hsmallBounds
    have hupper := mul_lt_mul_of_pos_left hcombinedBounds.2
      D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
    linarith [tribonacci_combined_right_upper_lt_threshold]
  have hlarge := tribonacci_strict_permanent_transition _ hcombined
  simp only [
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
    if_pos hcombinedLeft] at hlarge
  have hcoordinate : t ^ 2 * u - t = t * (t * u - 1) := by ring
  have hrightNext : t⁻¹ < t ^ 2 * u - t := by
    rw [hcoordinate]
    by_contra hnot
    have hlargeNext := tribonacci_strict_permanent_transition _ hlarge
    simp only [
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
      if_pos (le_of_not_gt hnot)] at hlargeNext
    have hlargeNextBounds :=
      tribonacci_strict_mem_iff _ |>.mp
        (tribonacci_strict_permanent_mem _ hlargeNext)
    change tribonacciThreshold < t * (t * (t * u - 1)) ∧
      t * (t * (t * u - 1)) < 1 - tribonacciThreshold at hlargeNextBounds
    have hlower := mul_lt_mul_of_pos_left hcombinedBounds.1
      (sq_pos_of_pos D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos)
    rw [tribonacci_threshold_scale_two] at hlower
    nlinarith [tribonacci_large_complement]
  constructor
  · simpa only [hcoordinate] using hlarge
  · exact hrightNext

theorem tribonacci_alternating_large_distance_bound (n : Nat) (u : Real)
    (hpermanent : (⟨.large, u⟩ : State) ∈ tribonacciStrictPermanentSet)
    (hright : t⁻¹ < u) :
    tribonacciLargeCoordinate - u ≤
      tribonacciPairContraction ^ n *
        (tribonacciLargeCoordinate - tribonacciThreshold) := by
  induction n generalizing u with
  | zero =>
      simp only [pow_zero, one_mul]
      have hu := tribonacci_strict_mem_iff _ |>.mp
        (tribonacci_strict_permanent_mem _ hpermanent)
      linarith
  | succ n ih =>
      obtain ⟨hnext, hrightNext⟩ :=
        tribonacci_alternating_large_step u hpermanent hright
      calc
        tribonacciLargeCoordinate - u =
            tribonacciPairContraction *
              (tribonacciLargeCoordinate - (t ^ 2 * u - t)) :=
          tribonacci_pair_contraction_identity u
        _ ≤ tribonacciPairContraction *
            (tribonacciPairContraction ^ n *
              (tribonacciLargeCoordinate - tribonacciThreshold)) :=
          mul_le_mul_of_nonneg_left (ih _ hnext hrightNext)
            tribonacci_pair_contraction_pos.le
        _ = tribonacciPairContraction ^ (n + 1) *
            (tribonacciLargeCoordinate - tribonacciThreshold) := by
          rw [pow_succ]
          ring

theorem tribonacci_no_alternating_large_permanent (u : Real)
    (hpermanent : (⟨.large, u⟩ : State) ∈ tribonacciStrictPermanentSet)
    (hright : t⁻¹ < u) : False := by
  have hu := tribonacci_strict_mem_iff _ |>.mp
    (tribonacci_strict_permanent_mem _ hpermanent)
  change tribonacciThreshold < u ∧ u < 1 - tribonacciThreshold at hu
  have huLarge : u < tribonacciLargeCoordinate := by
    nlinarith [tribonacci_large_complement]
  have hdistance : 0 < tribonacciLargeCoordinate - u := sub_pos.mpr huLarge
  have hdiameter : 0 < tribonacciLargeCoordinate - tribonacciThreshold := by
    linarith [tribonacci_threshold_lt_middle, tribonacci_middle_lt_large]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hdistance hdiameter) tribonacci_pair_contraction_lt_one
  have hbound :=
    tribonacci_alternating_large_distance_bound n u hpermanent hright
  have hlt :
      tribonacciPairContraction ^ n *
          (tribonacciLargeCoordinate - tribonacciThreshold) <
        tribonacciLargeCoordinate - u := by
    calc
      tribonacciPairContraction ^ n *
          (tribonacciLargeCoordinate - tribonacciThreshold) <
          ((tribonacciLargeCoordinate - u) /
            (tribonacciLargeCoordinate - tribonacciThreshold)) *
              (tribonacciLargeCoordinate - tribonacciThreshold) :=
        mul_lt_mul_of_pos_right hn hdiameter
      _ = tribonacciLargeCoordinate - u := by
        field_simp
  exact (not_lt_of_ge hbound) hlt

theorem tribonacci_no_large_strict_permanent (u : Real)
    (hpermanent : (⟨.large, u⟩ : State) ∈ tribonacciStrictPermanentSet) : False := by
  by_cases hright : t⁻¹ < u
  · exact tribonacci_no_alternating_large_permanent u hpermanent hright
  · have hleft : u ≤ t⁻¹ := le_of_not_gt hright
    have hlarge := tribonacci_strict_permanent_transition _ hpermanent
    simp only [
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
      if_pos hleft] at hlarge
    have hrightNext : t⁻¹ < t * u := by
      by_contra hnot
      have hlargeNext := tribonacci_strict_permanent_transition _ hlarge
      simp only [
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
        if_pos (le_of_not_gt hnot)] at hlargeNext
      have hu := tribonacci_strict_mem_iff _ |>.mp
        (tribonacci_strict_permanent_mem _ hpermanent)
      have hnext := tribonacci_strict_mem_iff _ |>.mp
        (tribonacci_strict_permanent_mem _ hlargeNext)
      change tribonacciThreshold < u ∧ _ at hu
      change tribonacciThreshold < t * (t * u) ∧
        t * (t * u) < 1 - tribonacciThreshold at hnext
      have hlower := mul_lt_mul_of_pos_left hu.1
        (sq_pos_of_pos D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos)
      rw [tribonacci_threshold_scale_two] at hlower
      nlinarith [tribonacci_large_complement]
    exact tribonacci_no_alternating_large_permanent (t * u) hlarge hrightNext

/-- Pointwise form of strict permanent emptiness. -/
theorem tribonacci_no_strict_permanent_survivor (state : State) :
    state ∉ tribonacciStrictPermanentSet := by
  intro hpermanent
  rcases state with ⟨kind, u⟩
  cases kind with
  | large => exact tribonacci_no_large_strict_permanent u hpermanent
  | small =>
      have hlarge := tribonacci_strict_permanent_transition _ hpermanent
      simp only [
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition]
        at hlarge
      exact tribonacci_no_large_strict_permanent (t * u) hlarge
  | combined =>
      by_cases hleft : u ≤ t⁻¹
      · have hlarge := tribonacci_strict_permanent_transition _ hpermanent
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
          if_pos hleft] at hlarge
        exact tribonacci_no_large_strict_permanent (t * u) hlarge
      · have hsmall := tribonacci_strict_permanent_transition _ hpermanent
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
          if_neg hleft] at hsmall
        have hlarge := tribonacci_strict_permanent_transition _ hsmall
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition]
          at hlarge
        exact tribonacci_no_large_strict_permanent (t * (t * u - 1)) hlarge

/-- The strict Tribonacci threshold has no permanently surviving state. -/
theorem tribonacci_strict_permanent_set_eq_empty :
    tribonacciStrictPermanentSet = ∅ := by
  ext state
  simp only [Set.mem_empty_iff_false, iff_false]
  exact tribonacci_no_strict_permanent_survivor state

def IsTribonacciClosedChampionState (state : State) : Prop :=
  state = tribonacciChampionLargeState ∨ state = tribonacciChampionCombinedState

theorem tribonacci_champion_combined_mem_strict :
    tribonacciChampionCombinedState ∈ tribonacciStrictSurvivorSet := by
  rw [tribonacci_strict_mem_iff]
  change tribonacciThreshold < tribonacciMiddleCoordinate ∧
    tribonacciMiddleCoordinate < t - 1 - tribonacciThreshold
  have hmidpoint :
      t - 1 - tribonacciMiddleCoordinate = tribonacciMiddleCoordinate := by
    rw [tribonacciMiddleCoordinate]
    ring
  have hthreshold := tribonacci_threshold_lt_middle
  constructor
  · exact hthreshold
  · linarith

/-- The one-step strict domain is nonempty, so permanent emptiness is not
vacuous at depth zero. -/
theorem tribonacci_strict_survivor_set_nonempty :
    tribonacciStrictSurvivorSet.Nonempty :=
  ⟨tribonacciChampionCombinedState, tribonacci_champion_combined_mem_strict⟩

theorem tribonacci_champion_large_mem_closed :
    tribonacciChampionLargeState ∈ tribonacciClosedSurvivorSet := by
  rw [tribonacci_closed_mem_iff]
  change tribonacciThreshold ≤ tribonacciLargeCoordinate ∧
    tribonacciLargeCoordinate ≤ 1 - tribonacciThreshold
  constructor
  · exact (tribonacci_threshold_lt_middle.trans tribonacci_middle_lt_large).le
  · nlinarith [tribonacci_large_complement]

theorem tribonacci_champion_combined_mem_closed :
    tribonacciChampionCombinedState ∈ tribonacciClosedSurvivorSet := by
  rw [tribonacci_closed_mem_iff]
  change tribonacciThreshold ≤ tribonacciMiddleCoordinate ∧
    tribonacciMiddleCoordinate ≤ t - 1 - tribonacciThreshold
  have hmidpoint :
      t - 1 - tribonacciMiddleCoordinate = tribonacciMiddleCoordinate := by
    rw [tribonacciMiddleCoordinate]
    ring
  have hthreshold := tribonacci_threshold_lt_middle
  constructor
  · exact hthreshold.le
  · linarith

theorem tribonacci_champion_large_transition :
    transition tribonacciChampionLargeState = tribonacciChampionCombinedState := by
  have hbranch : ¬ (tribonacciChampionLargeState.coordinate ≤ t⁻¹) := by
    change ¬ (tribonacciLargeCoordinate ≤ t⁻¹)
    exact not_le.mpr tribonacci_inverse_lt_large
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
    show tribonacciChampionLargeState.kind = .large by rfl]
  simp only [if_neg hbranch]
  simp only [
    tribonacciChampionLargeState]
  congr 1
  exact tribonacci_large_branch

theorem tribonacci_champion_combined_transition :
    transition tribonacciChampionCombinedState = tribonacciChampionLargeState := by
  have hbranch : tribonacciChampionCombinedState.coordinate ≤ t⁻¹ := by
    change tribonacciMiddleCoordinate ≤ t⁻¹
    exact tribonacci_middle_le_inverse
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
    show tribonacciChampionCombinedState.kind = .combined by rfl]
  simp only [if_pos hbranch]
  simp only [
    tribonacciChampionCombinedState]
  congr 1
  exact tribonacci_middle_scale

theorem tribonacci_closed_champion_mem (state : State)
    (hstate : IsTribonacciClosedChampionState state) :
    state ∈ tribonacciClosedSurvivorSet := by
  rcases hstate with rfl | rfl
  · exact tribonacci_champion_large_mem_closed
  · exact tribonacci_champion_combined_mem_closed

theorem tribonacci_closed_champion_forward (state : State)
    (hstate : IsTribonacciClosedChampionState state) :
    IsTribonacciClosedChampionState (transition state) := by
  rcases hstate with rfl | rfl
  · right
    exact tribonacci_champion_large_transition
  · left
    exact tribonacci_champion_combined_transition

theorem tribonacci_closed_champion_survives (n : Nat) (state : State)
    (hstate : IsTribonacciClosedChampionState state) :
    state ∈ tribonacciBackwardSurvivor tribonacciClosedSurvivorSet n := by
  induction n generalizing state with
  | zero => exact tribonacci_closed_champion_mem state hstate
  | succ n ih =>
      rw [tribonacci_backward_survivor_succ]
      exact ⟨tribonacci_closed_champion_mem state hstate,
        ih (transition state) (tribonacci_closed_champion_forward state hstate)⟩

/-- The known closed period-two carrier is a lower bound, not a classification
of the full closed permanent set. -/
theorem tribonacci_closed_champion_carrier_subset :
    {state | IsTribonacciClosedChampionState state} ⊆
      tribonacciClosedPermanentSet := by
  intro state hstate n
  exact tribonacci_closed_champion_survives n state hstate

/-- Unlike the strict permanent set, the closed permanent set is nonempty. -/
theorem tribonacci_closed_permanent_set_nonempty :
    tribonacciClosedPermanentSet.Nonempty := by
  refine ⟨tribonacciChampionLargeState, ?_⟩
  exact tribonacci_closed_champion_carrier_subset (Or.inl rfl)

end D5.S0.Tower.TribonacciSurvivors.TribonacciPermanentSurvivors

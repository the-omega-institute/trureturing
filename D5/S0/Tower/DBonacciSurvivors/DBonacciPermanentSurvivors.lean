/- GID: D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict d=4,5 permanent survival is empty; closed survival is nonempty. -/

import D5.S0.Tower.DBonacci.OrbitAlgebra
import D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit

/- Library-search audit trail (2026-08-17):
   * Repository search found the uniform typed d-bonacci gap substitution,
     base gap, champion value, and the order-four and order-five closed
     period-two orbits, but no strict permanent-survivor theorem.
   * The Tribonacci proof supplied the backward-set and contraction pattern;
     its three-constructor case split was not reused for the four- and
     five-letter alphabets.
   * Pinned Mathlib supplies `exists_pow_lt_of_lt_one` for the geometric
     contraction. No external d-bonacci permanent-survivor theorem was found. -/

namespace D5.S0.Tower.DBonacciSurvivors.DBonacciPermanentSurvivors

abbrev Gap (d : Nat) := Fin d

structure State (d : Nat) where
  kind : Gap d
  coordinate : Real

@[ext]
theorem state_ext {d : Nat} {left right : State d}
    (hkind : left.kind = right.kind)
    (hcoordinate : left.coordinate = right.coordinate) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def beta (d : Nat) : Real :=
  D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d

noncomputable def threshold (d : Nat) : Real :=
  D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue (beta d)

noncomputable def normalizedGapLength (d : Nat) (kind : Gap d) : Real :=
  D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound d kind.1

def top (d : Nat) (hd : 0 < d) : Gap d :=
  D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d hd

noncomputable def transition (d : Nat) (hd : 0 < d) (state : State d) : State d :=
  if hzero : state.kind.1 = 0 then
    ⟨top d hd, beta d * state.coordinate⟩
  else if state.coordinate ≤ (beta d)⁻¹ then
    ⟨top d hd, beta d * state.coordinate⟩
  else
    ⟨⟨state.kind.1 - 1, by omega⟩, beta d * state.coordinate - 1⟩

theorem transition_zero (d : Nat) (hd : 0 < d) (state : State d)
    (hzero : state.kind.1 = 0) :
    transition d hd state = ⟨top d hd, beta d * state.coordinate⟩ := by
  simp [transition, hzero]

theorem transition_left (d : Nat) (hd : 0 < d) (state : State d)
    (hzero : state.kind.1 ≠ 0) (hleft : state.coordinate ≤ (beta d)⁻¹) :
    transition d hd state = ⟨top d hd, beta d * state.coordinate⟩ := by
  simp [transition, hzero, hleft]

theorem transition_right (d : Nat) (hd : 0 < d) (state : State d)
    (hzero : state.kind.1 ≠ 0) (hright : ¬state.coordinate ≤ (beta d)⁻¹) :
    transition d hd state =
      ⟨⟨state.kind.1 - 1, by omega⟩, beta d * state.coordinate - 1⟩ := by
  simp [transition, hzero, hright]

def strictSet (d : Nat) : Set (State d) :=
  {state | threshold d < min state.coordinate
    (normalizedGapLength d state.kind - state.coordinate)}

def closedSet (d : Nat) : Set (State d) :=
  {state | threshold d ≤ min state.coordinate
    (normalizedGapLength d state.kind - state.coordinate)}

noncomputable def backward (d : Nat) (hd : 0 < d) (F : Set (State d)) :
    Nat → Set (State d)
  | 0 => F
  | n + 1 => F ∩ transition d hd ⁻¹' backward d hd F n

def strictPermanent (d : Nat) (hd : 0 < d) : Set (State d) :=
  {state | ∀ n, state ∈ backward d hd (strictSet d) n}

def closedPermanent (d : Nat) (hd : 0 < d) : Set (State d) :=
  {state | ∀ n, state ∈ backward d hd (closedSet d) n}

theorem backward_succ (d : Nat) (hd : 0 < d) (F : Set (State d)) (n : Nat) :
    backward d hd F (n + 1) = F ∩ transition d hd ⁻¹' backward d hd F n := by
  simp [backward]

theorem strict_mem_iff (d : Nat) (state : State d) :
    state ∈ strictSet d ↔
      threshold d < state.coordinate ∧
        state.coordinate < normalizedGapLength d state.kind - threshold d := by
  change threshold d < min state.coordinate
      (normalizedGapLength d state.kind - state.coordinate) ↔ _
  rw [lt_min_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

theorem closed_mem_iff (d : Nat) (state : State d) :
    state ∈ closedSet d ↔
      threshold d ≤ state.coordinate ∧
        state.coordinate ≤ normalizedGapLength d state.kind - threshold d := by
  change threshold d ≤ min state.coordinate
      (normalizedGapLength d state.kind - state.coordinate) ↔ _
  rw [le_min_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

theorem permanent_mem (d : Nat) (hd : 0 < d) (state : State d)
    (hstate : state ∈ strictPermanent d hd) : state ∈ strictSet d :=
  hstate 0

theorem permanent_transition (d : Nat) (hd : 0 < d) (state : State d)
    (hstate : state ∈ strictPermanent d hd) :
    transition d hd state ∈ strictPermanent d hd := by
  intro n
  have hnext := hstate (n + 1)
  rw [backward_succ] at hnext
  exact hnext.2

theorem normalized_top_length (d : Nat) (hd : 2 ≤ d) :
    normalizedGapLength d (top d (by omega)) = 1 := by
  simp [normalizedGapLength, top,
    D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter,
    D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound_full d hd]

theorem normalized_predecessor_length (d : Nat) (hd : 3 ≤ d) :
    normalizedGapLength d ⟨d - 2, by omega⟩ = beta d - 1 := by
  have hrec := D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound_succ d (d - 2)
  have htop := D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound_full d (by omega)
  rw [show d - 2 + 1 = d - 1 by omega, htop] at hrec
  have hbpos : 0 < beta d := by
    exact lt_trans zero_lt_one
      (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega))
  simp only [normalizedGapLength, beta]
  have hscaled := congrArg (fun x : Real => beta d * x) hrec
  field_simp [ne_of_gt hbpos] at hscaled
  rw [eq_div_iff] at hscaled
  · linarith
  · simpa [beta] using ne_of_gt hbpos

theorem beta_one_lt (d : Nat) (hd : 2 ≤ d) : 1 < beta d := by
  simpa [beta] using
    D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d hd

theorem denominator_pos (d : Nat) (hd : 2 ≤ d) : 0 < beta d ^ 2 - 1 := by
  have hproduct : 0 < (beta d - 1) * (beta d + 1) :=
    mul_pos (sub_pos.mpr (beta_one_lt d hd)) (by linarith [beta_one_lt d hd])
  nlinarith

theorem one_sub_threshold (d : Nat) (hd : 2 ≤ d) :
    1 - threshold d = beta d / (beta d ^ 2 - 1) := by
  have hden : beta d ^ 2 - 1 ≠ 0 := ne_of_gt (denominator_pos d hd)
  rw [threshold, D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue]
  field_simp [hden]
  ring

noncomputable def contraction (d : Nat) : Real := (beta d ^ 2)⁻¹

theorem contraction_pos (d : Nat) (hd : 2 ≤ d) : 0 < contraction d := by
  exact inv_pos.mpr (sq_pos_of_pos (lt_trans zero_lt_one
    (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d hd)))

theorem contraction_lt_one (d : Nat) (hd : 2 ≤ d) : contraction d < 1 := by
  apply inv_lt_one_of_one_lt₀
  linarith [denominator_pos d hd]

theorem contraction_identity (d : Nat) (hd : 2 ≤ d) (u : Real) :
    (1 - threshold d) - u = contraction d *
      ((1 - threshold d) - (beta d ^ 2 * u - beta d)) := by
  rw [one_sub_threshold d hd]
  have hbpos : 0 < beta d := lt_trans zero_lt_one
    (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d hd)
  have hden : beta d ^ 2 - 1 ≠ 0 := ne_of_gt (denominator_pos d hd)
  rw [contraction]
  field_simp [ne_of_gt hbpos, hden]
  ring

theorem non_top_forced_left (d : Nat) (hd : 3 ≤ d)
    (hscale : (beta d)⁻¹ < beta d * threshold d)
    (hbarrier : beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 < threshold d)
    (state : State d) (hkind : state.kind.1 < d - 1)
    (hpermanent : state ∈ strictPermanent d (by omega)) :
    transition d (by omega) state =
        ⟨top d (by omega), beta d * state.coordinate⟩ ∧
      (beta d)⁻¹ < beta d * state.coordinate := by
  have hbpos : 0 < beta d := lt_trans zero_lt_one
    (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega))
  have hbounds := (strict_mem_iff d state).mp
    (permanent_mem d (by omega) state hpermanent)
  have hhigh : (beta d)⁻¹ < beta d * state.coordinate :=
    hscale.trans (mul_lt_mul_of_pos_left hbounds.1 hbpos)
  constructor
  · by_cases hzero : state.kind.1 = 0
    · exact transition_zero d (by omega) state hzero
    · by_cases hleft : state.coordinate ≤ (beta d)⁻¹
      · exact transition_left d (by omega) state hzero hleft
      · have hnext := permanent_transition d (by omega) state hpermanent
        rw [transition_right d (by omega) state hzero hleft] at hnext
        have hnextBounds := (strict_mem_iff d _).mp
          (permanent_mem d (by omega) _ hnext)
        have hkindle : state.kind.1 ≤ d - 2 := by omega
        have hlengthle : normalizedGapLength d state.kind ≤
            normalizedGapLength d ⟨d - 2, by omega⟩ := by
          exact (D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound_strictMono d
            (by omega)).monotone hkindle
        have hu := mul_lt_mul_of_pos_left hbounds.2 hbpos
        have hlen := mul_le_mul_of_nonneg_left hlengthle hbpos.le
        change threshold d < beta d * state.coordinate - 1 ∧ _ at hnextBounds
        linarith
  · exact hhigh

theorem high_top_step (d : Nat) (hd : 3 ≤ d)
    (hscale : (beta d)⁻¹ < beta d * threshold d)
    (hbarrier : beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 < threshold d)
    (u : Real)
    (hpermanent : (⟨top d (by omega), u⟩ : State d) ∈ strictPermanent d (by omega))
    (hhigh : (beta d)⁻¹ < u) :
    (⟨top d (by omega), beta d ^ 2 * u - beta d⟩ : State d) ∈
        strictPermanent d (by omega) ∧
      (beta d)⁻¹ < beta d ^ 2 * u - beta d := by
  have hpred := permanent_transition d (by omega) _ hpermanent
  have htopzero : (top d (by omega)).1 ≠ 0 := by
    change d - 1 ≠ 0
    omega
  rw [transition_right d (by omega) _ htopzero (not_le.mpr hhigh)] at hpred
  have hk : ((⟨(top d (by omega)).1 - 1, by omega⟩ : Gap d)).1 < d - 1 := by
    change (d - 1) - 1 < d - 1
    omega
  obtain ⟨heq, hnextHigh⟩ := non_top_forced_left d hd hscale hbarrier _ hk hpred
  have hnext := permanent_transition d (by omega) _ hpred
  rw [heq] at hnext
  have hcoordinate : beta d * (beta d * u - 1) = beta d ^ 2 * u - beta d := by
    ring
  constructor
  · simpa only [hcoordinate] using hnext
  · simpa only [hcoordinate] using hnextHigh

theorem high_top_distance_bound (d : Nat) (hd : 3 ≤ d)
    (hscale : (beta d)⁻¹ < beta d * threshold d)
    (hbarrier : beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 < threshold d)
    (n : Nat) (u : Real)
    (hpermanent : (⟨top d (by omega), u⟩ : State d) ∈ strictPermanent d (by omega))
    (hhigh : (beta d)⁻¹ < u) :
    (1 - threshold d) - u ≤ contraction d ^ n *
      ((1 - threshold d) - threshold d) := by
  induction n generalizing u with
  | zero =>
      simp only [pow_zero, one_mul]
      have hu := (strict_mem_iff d _).mp
        (permanent_mem d (by omega) _ hpermanent)
      linarith
  | succ n ih =>
      obtain ⟨hnext, hnextHigh⟩ := high_top_step d hd hscale hbarrier u hpermanent hhigh
      calc
        (1 - threshold d) - u = contraction d *
            ((1 - threshold d) - (beta d ^ 2 * u - beta d)) :=
          contraction_identity d (by omega) u
        _ ≤ contraction d * (contraction d ^ n *
              ((1 - threshold d) - threshold d)) :=
          mul_le_mul_of_nonneg_left (ih _ hnext hnextHigh)
            (contraction_pos d (by omega)).le
        _ = contraction d ^ (n + 1) *
            ((1 - threshold d) - threshold d) := by rw [pow_succ]; ring

theorem no_high_top_permanent (d : Nat) (hd : 3 ≤ d)
    (hscale : (beta d)⁻¹ < beta d * threshold d)
    (hbarrier : beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 < threshold d)
    (u : Real)
    (hpermanent : (⟨top d (by omega), u⟩ : State d) ∈ strictPermanent d (by omega))
    (hhigh : (beta d)⁻¹ < u) : False := by
  have hu := (strict_mem_iff d _).mp
    (permanent_mem d (by omega) _ hpermanent)
  rw [normalized_top_length d (by omega)] at hu
  have hdistance : 0 < (1 - threshold d) - u := by linarith
  have hdiameter : 0 < (1 - threshold d) - threshold d := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hdistance hdiameter) (contraction_lt_one d (by omega))
  have hbound := high_top_distance_bound d hd hscale hbarrier n u hpermanent hhigh
  have hlt : contraction d ^ n * ((1 - threshold d) - threshold d) <
      (1 - threshold d) - u := by
    calc
      contraction d ^ n * ((1 - threshold d) - threshold d) <
          (((1 - threshold d) - u) /
            ((1 - threshold d) - threshold d)) *
              ((1 - threshold d) - threshold d) :=
        mul_lt_mul_of_pos_right hn hdiameter
      _ = (1 - threshold d) - u := by field_simp
  exact (not_lt_of_ge hbound) hlt

theorem no_strict_permanent (d : Nat) (hd : 3 ≤ d)
    (hscale : (beta d)⁻¹ < beta d * threshold d)
    (hbarrier : beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 < threshold d)
    (state : State d) : state ∉ strictPermanent d (by omega) := by
  intro hpermanent
  rcases state with ⟨kind, u⟩
  by_cases htop : kind = top d (by omega)
  · subst kind
    by_cases hhigh : (beta d)⁻¹ < u
    · exact no_high_top_permanent d hd hscale hbarrier u hpermanent hhigh
    · have hlow : u ≤ (beta d)⁻¹ := le_of_not_gt hhigh
      have hnext := permanent_transition d (by omega) _ hpermanent
      have htopzero : (top d (by omega)).1 ≠ 0 := by
        change d - 1 ≠ 0
        omega
      rw [transition_left d (by omega) _ htopzero hlow] at hnext
      have hbounds := (strict_mem_iff d _).mp
        (permanent_mem d (by omega) _ hpermanent)
      have hbpos : 0 < beta d := lt_trans zero_lt_one
        (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega))
      have hnextHigh : (beta d)⁻¹ < beta d * u :=
        hscale.trans (mul_lt_mul_of_pos_left hbounds.1 hbpos)
      exact no_high_top_permanent d hd hscale hbarrier (beta d * u) hnext hnextHigh
  · have hkind : kind.1 < d - 1 := by
      have hle : kind.1 ≤ d - 1 := by omega
      apply lt_of_le_of_ne hle
      intro heq
      apply htop
      apply Fin.ext
      change kind.1 = d - 1
      exact heq
    obtain ⟨heq, hhigh⟩ :=
      non_top_forced_left d hd hscale hbarrier (⟨kind, u⟩ : State d) hkind hpermanent
    have hnext := permanent_transition d (by omega) _ hpermanent
    rw [heq] at hnext
    exact no_high_top_permanent d hd hscale hbarrier (beta d * u) hnext hhigh

theorem strict_permanent_eq_empty_of_barriers (d : Nat) (hd : 3 ≤ d)
    (hscale : (beta d)⁻¹ < beta d * threshold d)
    (hbarrier : beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 < threshold d) :
    strictPermanent d (by omega) = ∅ := by
  ext state
  simp only [Set.mem_empty_iff_false, iff_false]
  exact no_strict_permanent d hd hscale hbarrier state

local notation "b4" => beta 4
local notation "b5" => beta 5

theorem four_scale_barrier : b4⁻¹ < b4 * threshold 4 := by
  have hb := D5.S0.Tower.DBonacci.ChampionOrbit.four_root_bounds
  have hc := D5.S0.Tower.DBonacci.ChampionOrbit.four_root_characteristic
  have hden : 0 < b4 ^ 2 - 1 := by simpa [beta] using
    D5.S0.Tower.DBonacci.ChampionOrbit.four_denominator_pos
  have hproduct : 0 < (2 - b4) * (b4 + 1) :=
    mul_pos (sub_pos.mpr (by simpa [beta] using hb.2)) (by
      simpa [beta] using (show 0 <
        D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 + 1 by linarith [hb.1]))
  have hnumerator : 0 < b4 ^ 4 - b4 ^ 3 - 2 * b4 ^ 2 + 1 := by
    simp only [beta] at hc hproduct ⊢
    nlinarith
  have hbpos : 0 < b4 := by simpa [beta] using (lt_trans zero_lt_one hb.1)
  have hidentity :
      b4 * threshold 4 - b4⁻¹ =
        (b4 ^ 4 - b4 ^ 3 - 2 * b4 ^ 2 + 1) /
          (b4 * (b4 ^ 2 - 1)) := by
    rw [threshold, D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue]
    field_simp [ne_of_gt hbpos, ne_of_gt hden]
    ring
  have hdiff : 0 < b4 * threshold 4 - b4⁻¹ := by
    rw [hidentity]
    exact div_pos hnumerator (mul_pos hbpos hden)
  linarith

theorem five_root_characteristic :
    b5 ^ 5 = b5 ^ 4 + b5 ^ 3 + b5 ^ 2 + b5 + 1 := by
  have h := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_characteristic
    5 (by norm_num)
  norm_num [Finset.sum_range_succ, beta] at h ⊢
  nlinarith

theorem five_scale_barrier : b5⁻¹ < b5 * threshold 5 := by
  have hb := D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_root_bounds
  have hc := five_root_characteristic
  have hden : 0 < b5 ^ 2 - 1 := by simpa [beta] using
    D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_denominator_pos
  have hproduct : 0 < (2 - b5) * (b5 + 1) := by
    apply mul_pos
    · simpa [beta] using (sub_pos.mpr hb.2)
    · simp only [beta]
      linarith [hb.1]
  have hpositive : 0 < b5 * ((2 - b5) * (b5 + 1)) := by
    exact mul_pos (by simpa [beta] using (lt_trans zero_lt_one hb.1)) hproduct
  have hnumerator : 0 < b5 ^ 4 - b5 ^ 3 - 2 * b5 ^ 2 + 1 := by
    simp only [beta] at hc hpositive ⊢
    nlinarith
  have hbpos : 0 < b5 := by simpa [beta] using (lt_trans zero_lt_one hb.1)
  have hidentity :
      b5 * threshold 5 - b5⁻¹ =
        (b5 ^ 4 - b5 ^ 3 - 2 * b5 ^ 2 + 1) /
          (b5 * (b5 ^ 2 - 1)) := by
    rw [threshold, D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue]
    field_simp [ne_of_gt hbpos, ne_of_gt hden]
    ring
  have hdiff : 0 < b5 * threshold 5 - b5⁻¹ := by
    rw [hidentity]
    exact div_pos hnumerator (mul_pos hbpos hden)
  linarith

theorem cubic_barrier_pos (d : Nat)
    (hlower : (9 : Real) / 5 < beta d)
    (hupper : beta d < 2) : 0 < beta d ^ 3 - 2 * beta d - 1 := by
  have hbpos : 0 < beta d := lt_trans (by norm_num) hlower
  have hsum : 0 < beta d ^ 2 + ((9 : Real) / 5) * beta d + (81 : Real) / 25 := by
    positivity
  have hcube : 0 < (beta d - (9 : Real) / 5) *
      (beta d ^ 2 + ((9 : Real) / 5) * beta d + (81 : Real) / 25) :=
    mul_pos (sub_pos.mpr hlower) hsum
  nlinarith

theorem barrier_of_root_bounds (d : Nat) (hd : 3 ≤ d)
    (hlower : (9 : Real) / 5 < beta d)
    (hupper : beta d < 2) :
    beta d *
      (normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d) - 1 <
        threshold d := by
  rw [normalized_predecessor_length d hd]
  have hbpos : 0 < beta d := lt_trans (by norm_num) hlower
  have hden : 0 < beta d ^ 2 - 1 := by nlinarith
  have hcubic := cubic_barrier_pos d hlower hupper
  have hidentity :
      beta d * (beta d - 1 - threshold d) - 1 - threshold d =
        ((beta d - 2) * (beta d ^ 3 - 2 * beta d - 1)) /
          (beta d ^ 2 - 1) := by
    rw [threshold, D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue]
    field_simp [ne_of_gt hden]
    ring
  have hnegative :
      beta d * (beta d - 1 - threshold d) - 1 - threshold d < 0 := by
    rw [hidentity]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (sub_neg.mpr hupper) hcubic) hden
  linarith

theorem four_predecessor_barrier :
    b4 * (normalizedGapLength 4 ⟨2, by norm_num⟩ - threshold 4) - 1 <
      threshold 4 := by
  apply barrier_of_root_bounds 4 (by norm_num)
  · have h := D5.S0.Tower.DBonacciGeneral.ChampionValue.dbonacci_four_root_numeric_bounds.1
    norm_num [beta] at h ⊢
    linarith
  · simpa [beta] using D5.S0.Tower.DBonacci.ChampionOrbit.four_root_bounds.2

theorem five_predecessor_barrier :
    b5 * (normalizedGapLength 5 ⟨3, by norm_num⟩ - threshold 5) - 1 <
      threshold 5 := by
  apply barrier_of_root_bounds 5 (by norm_num)
  · have h := D5.S0.Tower.DBonacciGeneral.ChampionValue.dbonacci_five_root_numeric_bounds.1
    norm_num [beta] at h ⊢
    linarith
  · simpa [beta] using D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_root_bounds.2

def dbonacciFourStrictPermanentSet : Set (State 4) := strictPermanent 4 (by norm_num)

def dbonacciFiveStrictPermanentSet : Set (State 5) := strictPermanent 5 (by norm_num)

/-- No state survives every finite strict backward depth at order four. -/
theorem dbonacci_four_strict_permanent_set_eq_empty :
    dbonacciFourStrictPermanentSet = ∅ := by
  exact strict_permanent_eq_empty_of_barriers 4 (by norm_num)
    four_scale_barrier four_predecessor_barrier

/-- No state survives every finite strict backward depth at order five. -/
theorem dbonacci_five_strict_permanent_set_eq_empty :
    dbonacciFiveStrictPermanentSet = ∅ := by
  exact strict_permanent_eq_empty_of_barriers 5 (by norm_num)
    five_scale_barrier five_predecessor_barrier

noncomputable def largeCoordinate (d : Nat) : Real :=
  beta d / (beta d ^ 2 - 1)

noncomputable def middleCoordinate (d : Nat) : Real :=
  1 / (beta d ^ 2 - 1)

noncomputable def largeState (d : Nat) (hd : 0 < d) : State d :=
  ⟨top d hd, largeCoordinate d⟩

noncomputable def middleState (d : Nat) (hd : 2 ≤ d) : State d :=
  ⟨⟨d - 2, by omega⟩, middleCoordinate d⟩

def IsClosedChampionState (d : Nat) (hd : 2 ≤ d) (state : State d) : Prop :=
  state = largeState d (by omega) ∨ state = middleState d hd

theorem threshold_eq_low_arm (d : Nat) :
    threshold d = (beta d ^ 2 - beta d - 1) / (beta d ^ 2 - 1) := rfl

theorem large_coordinate_eq_one_sub_threshold (d : Nat) (hd : 2 ≤ d) :
    largeCoordinate d = 1 - threshold d := by
  rw [largeCoordinate, one_sub_threshold d hd]

theorem middle_lt_large (d : Nat) (hd : 2 ≤ d) :
    middleCoordinate d < largeCoordinate d := by
  rw [middleCoordinate, largeCoordinate, div_lt_div_iff_of_pos_right (denominator_pos d hd)]
  exact beta_one_lt d hd

theorem predecessor_right_arm (d : Nat) (hd : 3 ≤ d) :
    normalizedGapLength d ⟨d - 2, by omega⟩ - middleCoordinate d =
      beta d * threshold d := by
  rw [normalized_predecessor_length d hd, middleCoordinate, threshold_eq_low_arm]
  field_simp [ne_of_gt (denominator_pos d (by omega))]
  ring

theorem large_branch_coordinate (d : Nat) (hd : 2 ≤ d) :
    beta d * largeCoordinate d - 1 = middleCoordinate d := by
  rw [largeCoordinate, middleCoordinate]
  field_simp [ne_of_gt (denominator_pos d hd)]
  ring

theorem middle_branch_coordinate (d : Nat) :
    beta d * middleCoordinate d = largeCoordinate d := by
  rw [middleCoordinate, largeCoordinate]
  ring

theorem large_coordinate_high (d : Nat) (hd : 2 ≤ d) :
    (beta d)⁻¹ < largeCoordinate d := by
  have hbpos : 0 < beta d := lt_trans zero_lt_one (beta_one_lt d hd)
  have hidentity :
      largeCoordinate d - (beta d)⁻¹ =
        1 / (beta d * (beta d ^ 2 - 1)) := by
    rw [largeCoordinate]
    field_simp [ne_of_gt hbpos, ne_of_gt (denominator_pos d hd)]
    ring
  have hdiff : 0 < largeCoordinate d - (beta d)⁻¹ := by
    rw [hidentity]
    exact one_div_pos.mpr (mul_pos hbpos (denominator_pos d hd))
  linarith

theorem middle_coordinate_le_inverse (d : Nat) (hd : 2 ≤ d)
    (hthreshold : 0 < threshold d) :
    middleCoordinate d ≤ (beta d)⁻¹ := by
  have hbpos : 0 < beta d := lt_trans zero_lt_one (beta_one_lt d hd)
  have hden := denominator_pos d hd
  have hnum : 0 < beta d ^ 2 - beta d - 1 := by
    rw [threshold_eq_low_arm] at hthreshold
    rcases (div_pos_iff.mp hthreshold) with hsame | hsame
    · exact hsame.1
    · linarith
  rw [middleCoordinate]
  rw [div_le_iff₀ hden]
  calc
    1 = (beta d)⁻¹ * beta d := by field_simp [ne_of_gt hbpos]
    _ ≤ (beta d)⁻¹ * (beta d ^ 2 - 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (inv_nonneg.mpr hbpos.le)

theorem closed_large_mem (d : Nat) (hd : 3 ≤ d)
    (hthresholdMiddle : threshold d < middleCoordinate d) :
    largeState d (by omega) ∈ closedSet d := by
  rw [closed_mem_iff]
  change threshold d ≤ largeCoordinate d ∧
    largeCoordinate d ≤ normalizedGapLength d (top d (by omega)) - threshold d
  rw [normalized_top_length d (by omega)]
  constructor
  · exact (hthresholdMiddle.trans (middle_lt_large d (by omega))).le
  · rw [large_coordinate_eq_one_sub_threshold d (by omega)]

theorem closed_middle_mem (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (hthresholdMiddle : threshold d < middleCoordinate d) :
    middleState d (by omega) ∈ closedSet d := by
  rw [closed_mem_iff]
  change threshold d ≤ middleCoordinate d ∧
    middleCoordinate d ≤ normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d
  have hright := predecessor_right_arm d hd
  constructor
  · exact hthresholdMiddle.le
  · have hbeta := beta_one_lt d (by omega)
    nlinarith [mul_pos (lt_trans zero_lt_one hbeta) hthreshold]

theorem large_transition (d : Nat) (hd : 3 ≤ d) :
    transition d (by omega) (largeState d (by omega)) =
      middleState d (by omega) := by
  have hzero : (largeState d (by omega)).kind.1 ≠ 0 := by
    change d - 1 ≠ 0
    omega
  rw [transition_right d (by omega) _ hzero
    (not_le.mpr (large_coordinate_high d (by omega)))]
  apply state_ext
  · apply Fin.ext
    change (d - 1) - 1 = d - 2
    omega
  · exact large_branch_coordinate d (by omega)

theorem middle_transition (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d) :
    transition d (by omega) (middleState d (by omega)) =
      largeState d (by omega) := by
  have hzero : (middleState d (by omega)).kind.1 ≠ 0 := by
    change d - 2 ≠ 0
    omega
  rw [transition_left d (by omega) _ hzero
    (middle_coordinate_le_inverse d (by omega) hthreshold)]
  apply state_ext
  · rfl
  · exact middle_branch_coordinate d

theorem closed_champion_mem (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (hthresholdMiddle : threshold d < middleCoordinate d)
    (state : State d) (hstate : IsClosedChampionState d (by omega) state) :
    state ∈ closedSet d := by
  rcases hstate with rfl | rfl
  · exact closed_large_mem d hd hthresholdMiddle
  · exact closed_middle_mem d hd hthreshold hthresholdMiddle

theorem closed_champion_forward (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (state : State d) (hstate : IsClosedChampionState d (by omega) state) :
    IsClosedChampionState d (by omega) (transition d (by omega) state) := by
  rcases hstate with rfl | rfl
  · right
    exact large_transition d hd
  · left
    exact middle_transition d hd hthreshold

theorem closed_champion_survives (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (hthresholdMiddle : threshold d < middleCoordinate d)
    (n : Nat) (state : State d) (hstate : IsClosedChampionState d (by omega) state) :
    state ∈ backward d (by omega) (closedSet d) n := by
  induction n generalizing state with
  | zero => exact closed_champion_mem d hd hthreshold hthresholdMiddle state hstate
  | succ n ih =>
      rw [backward_succ]
      exact ⟨closed_champion_mem d hd hthreshold hthresholdMiddle state hstate,
        ih (transition d (by omega) state)
          (closed_champion_forward d hd hthreshold state hstate)⟩

theorem closed_champion_carrier_subset (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (hthresholdMiddle : threshold d < middleCoordinate d) :
    {state | IsClosedChampionState d (by omega) state} ⊆
      closedPermanent d (by omega) := by
  intro state hstate n
  exact closed_champion_survives d hd hthreshold hthresholdMiddle n state hstate

theorem closed_permanent_nonempty_of_champion (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (hthresholdMiddle : threshold d < middleCoordinate d) :
    (closedPermanent d (by omega)).Nonempty := by
  refine ⟨largeState d (by omega), ?_⟩
  exact closed_champion_carrier_subset d hd hthreshold hthresholdMiddle (Or.inl rfl)

def dbonacciFourClosedPermanentSet : Set (State 4) := closedPermanent 4 (by norm_num)

def dbonacciFiveClosedPermanentSet : Set (State 5) := closedPermanent 5 (by norm_num)

theorem four_threshold_pos : 0 < threshold 4 := by
  simpa [threshold, beta,
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue] using
      D5.S0.Tower.DBonacci.ChampionOrbit.four_lowArm_pos

theorem five_threshold_pos : 0 < threshold 5 := by
  simpa [threshold, beta,
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue] using
    D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_lowArm_pos

theorem four_threshold_lt_middle : threshold 4 < middleCoordinate 4 := by
  simpa [threshold, beta, middleCoordinate,
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue] using
    D5.S0.Tower.DBonacci.ChampionOrbit.four_lowArm_lt_middleLeft

theorem five_threshold_lt_middle : threshold 5 < middleCoordinate 5 := by
  simpa [threshold, beta, middleCoordinate,
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue] using
    D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_lowArm_lt_middleLeft

theorem strict_middle_mem (d : Nat) (hd : 3 ≤ d)
    (hthreshold : 0 < threshold d)
    (hthresholdMiddle : threshold d < middleCoordinate d) :
    middleState d (by omega) ∈ strictSet d := by
  rw [strict_mem_iff]
  change threshold d < middleCoordinate d ∧
    middleCoordinate d < normalizedGapLength d ⟨d - 2, by omega⟩ - threshold d
  have hright := predecessor_right_arm d hd
  constructor
  · exact hthresholdMiddle
  · have hbeta := beta_one_lt d (by omega)
    nlinarith [mul_pos (sub_pos.mpr hbeta) hthreshold]

theorem dbonacci_four_strict_survivor_set_nonempty : (strictSet 4).Nonempty :=
  ⟨middleState 4 (by norm_num),
    strict_middle_mem 4 (by norm_num) four_threshold_pos four_threshold_lt_middle⟩

theorem dbonacci_five_strict_survivor_set_nonempty : (strictSet 5).Nonempty :=
  ⟨middleState 5 (by norm_num),
    strict_middle_mem 5 (by norm_num) five_threshold_pos five_threshold_lt_middle⟩

/-- The closed order-four champion two-cycle survives every backward depth. -/
theorem dbonacci_four_closed_permanent_set_nonempty :
    dbonacciFourClosedPermanentSet.Nonempty := by
  exact closed_permanent_nonempty_of_champion 4 (by norm_num)
    four_threshold_pos four_threshold_lt_middle

/-- The closed order-five champion two-cycle survives every backward depth. -/
theorem dbonacci_five_closed_permanent_set_nonempty :
    dbonacciFiveClosedPermanentSet.Nonempty := by
  exact closed_permanent_nonempty_of_champion 5 (by norm_num)
    five_threshold_pos five_threshold_lt_middle

end D5.S0.Tower.DBonacciSurvivors.DBonacciPermanentSurvivors

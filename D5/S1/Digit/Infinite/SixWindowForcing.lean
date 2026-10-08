/- GID: D5/S1/Digit/Infinite/SixWindowForcing
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SixWindowForcing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local separation and arbitrary-length six-window forcing for actual paired sources. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace D5.S1.Digit.Infinite.SixWindowForcing

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.CriticalPrefixSeparation (residual)

/-- The finite-delay critical budget. -/
noncomputable def rho : ℝ := (239 * g - 44) / 380

/-- The three-color bounds for the two third-color choices of separation type three. -/
noncomputable def K31 : ℝ := (47 * g - 11) / 50
noncomputable def K32 : ℝ := (5 - 21 * g) / 20
/-- The three-color bound for separation type four. -/
noncomputable def K4 : ℝ := (9 * g - 2) / 25
/-- The four-color return bound for separation type two. -/
noncomputable def J : ℝ := 2 * g ^ 4 / (5 * (1 + g ^ 3))

/-- The alternating six-window source words. -/
def blockA : List Label := [threeLabel, threeLabel, fiveLabel, nullLabel, threeLabel, nullLabel]
def blockB : List Label := [nullLabel, threeLabel, nullLabel, threeLabel, threeLabel, fiveLabel]

set_option quotPrecheck false
local notation "X" => (fun (x : LegalDigits) (j : ℕ) => kappa (bitShift x (3 * j)))
local notation "L" => (fun i : Fin 6 => if i.val ≤ 1 then threeLabel else
  if i.val = 2 then nullLabel else if i.val = 3 then fiveLabel else twoLabel)
local notation "H" => (fun i : Fin 6 => if i.val ≤ 1 then nullLabel else
  if i.val = 2 then fiveLabel else if i.val = 3 then twoLabel else twoFiveLabel)
local notation "N" => (fun i : Fin 6 => if i.val ≤ 1 then (0 : Fin 6) else
  if i.val ≤ 3 then 1 else 2)
local notation "C" => (fun i : Fin 6 => if i.val ≤ 1 then threeLabel else
  if i.val ≤ 3 then nullLabel else fiveLabel)

private theorem algebra : g ^ 2 + 4 * g = 1 ∧ (4 / 17 : ℝ) < g ∧
    g < 17 / 72 ∧ t = (1 + g) / 2 ∧ t ^ 2 = (1 - g) / 2 := by
  obtain ⟨ht, ht1, ht2, hg, hh⟩ :=
    D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations
  have hq : g ^ 2 + 4 * g = 1 := by rw [hg]; nlinarith
  have hp : 0 < g := pow_pos ht 3
  refine ⟨hq, ?_, ?_, by linarith, by linarith⟩
  · by_contra hn
    have hn := le_of_not_gt hn
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hn)]
  · by_contra hn
    have hn := le_of_not_gt hn
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hn)]

private theorem root (x : LegalDigits) (j : ℕ) :
    X x j ∈ Set.Icc
      (if (window x j).val 1 then -1 else if (window x j).val 0 then
        (if (window x j).val 2 then 2 * t else t) else
        (if (window x j).val 2 then g else t - 1))
      (if (window x j).val 1 then t - 1 else if (window x j).val 0 then
        (if (window x j).val 2 then 1 + t else 2 * t) else
        (if (window x j).val 2 then t else g)) := by
  obtain ⟨_, hrange, hrec, _, _, _, _, _, hroot⟩ := closed_observation_graph_realization
  have hw : window (bitShift x (3 * j)) 0 = window x j := by
    simp [window, D5.S1.Digit.Infinite.OddColorThreeSource.shift_add]
  rw [← hw, ← hroot]
  dsimp only
  rw [(hrec (bitShift x (3 * j))).1]
  exact ⟨_, (hrange _).subset ⟨_, (hrec _).2.1, rfl⟩, rfl⟩

private theorem observation_bounds (ν : ℝ) (i : Fin 6) (z : ℝ)
    (hz : z ∈ observation ν i) :
    cellLower i - ν ≤ z ∧ z ≤ cellUpper i + ν :=
  ⟨(le_max_right _ _).trans hz.1, hz.2.trans (min_le_right _ _)⟩

private theorem allow (ν : ℝ) (hν : ν < lambda) (x : LegalDigits)
    (j : ℕ) (i : Fin 6) (hx : X x j ∈ observation ν i) :
    window x j = L i ∨ window x j = H i := by
  classical
  obtain ⟨hg2, hglo, hghi, ht, ht2⟩ := algebra
  have hr := root x j
  obtain ⟨hlo, hhi⟩ := observation_bounds ν i _ hx
  generalize window x j = l at hr ⊢
  letI : Fintype Label := by
    unfold Label D5.S1.Digit.Infinite.WindowSuccessorGraph.X
    infer_instance
  fin_cases l <;> fin_cases i
  all_goals norm_num [nullLabel, threeLabel, twoLabel, fiveLabel, twoFiveLabel] at *
  all_goals try (first | exact Or.inl rfl | exact Or.inr rfl)
  all_goals
    exfalso
    norm_num [cellLower, cellUpper, cuts, lambda, ht, ht2] at hlo hhi hν
    norm_num [ht, ht2] at hr
    nlinarith only [hg2, hglo, hghi, hlo, hhi, hν, hr.1, hr.2]


/-- Both coordinates of one pair of actual sources share the indicated finite color word. -/
def SharedAt (ν : ℝ) (r : ℕ → Fin 6) (x y : LegalDigits) (j n : ℕ) : Prop :=
  ∀ k < n, X x (j + k) ∈ observation ν (r (j + k)) ∧
    X y (j + k) ∈ observation ν (r (j + k))

private theorem end_labels (ν : ℝ) (hν : ν < lambda) (x : LegalDigits)
    (j : ℕ) :
    (X x j ∈ observation ν 0 → window x j = threeLabel) ∧
    (X x j ∈ observation ν 5 → window x j = twoFiveLabel) := by
  obtain ⟨_, hglo, hghi, ht, ht2⟩ := algebra
  have hr := root x j
  constructor
  · intro hx
    rcases allow ν hν x j 0 hx with h | h
    · exact h
    · norm_num at h
      rw [h] at hr
      obtain ⟨hlo, hhi⟩ := observation_bounds ν 0 _ hx
      norm_num [nullLabel, cellUpper, cellLower, cuts, lambda, ht, ht2] at hr hhi hν
      linarith [hr.1]
  · intro hx
    rcases allow ν hν x j 5 hx with h | h
    · norm_num at h
      rw [h] at hr
      obtain ⟨hlo, hhi⟩ := observation_bounds ν 5 _ hx
      norm_num [twoLabel, cellUpper, cellLower, cuts, lambda, ht, ht2] at hr hlo hν
      linarith [hr.2]
    · exact h

private theorem split_bounds (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i : Fin 6) (hi : 1 ≤ i.val ∧ i.val ≤ 4)
    (hx : X x j ∈ observation ν i) (hy : X y j ∈ observation ν i)
    (hl : window x j = L i) (hh : window y j = H i) :
    lambda - ν ≤ g * ((-1 + i.val * (1 + t) / 5) - X x (j + 1)) ∧
    lambda - ν ≤ g * (X y (j + 1) - (-1 + i.val * (1 + t) / 5)) := by
  obtain ⟨hg2, hglo, hghi, ht, ht2⟩ := algebra
  obtain ⟨hxl, hxu⟩ := observation_bounds ν i _ hx
  obtain ⟨hyl, hyu⟩ := observation_bounds ν i _ hy
  have ha := residual x j
  have hb := residual y j
  rw [hl] at ha
  rw [hh] at hb
  fin_cases i <;> norm_num at hi
  all_goals norm_num [cellLower, cellUpper, cuts, lambda, offset, nullLabel,
    threeLabel, twoLabel, fiveLabel, twoFiveLabel, ht, ht2] at ha hb hxl hxu hyl hyu ⊢
  all_goals constructor <;> nlinarith only [ha, hb, hxl, hxu, hyl, hyu, hg2]

private theorem next_color (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i c : Fin 6) (hi : 1 ≤ i.val ∧ i.val ≤ 4)
    (hx : X x j ∈ observation ν i) (hy : X y j ∈ observation ν i)
    (hl : window x j = L i) (hh : window y j = H i)
    (hx' : X x (j + 1) ∈ observation ν c) (hy' : X y (j + 1) ∈ observation ν c) :
    c = N i := by
  obtain ⟨hg2, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < g := by linarith
  obtain ⟨ha, hb⟩ := split_bounds ν hν x y j i hi hx hy hl hh
  have hδ : 0 < lambda - ν := sub_pos.mpr hν
  have hsx : X x (j + 1) < -1 + i.val * (1 + t) / 5 := by nlinarith
  have hsy : -1 + i.val * (1 + t) / 5 < X y (j + 1) := by nlinarith
  obtain ⟨hxl, hxu⟩ := observation_bounds ν c _ hx'
  obtain ⟨hyl, hyu⟩ := observation_bounds ν c _ hy'
  fin_cases i <;> fin_cases c <;> norm_num at hi ⊢
  all_goals norm_num [cellLower, cellUpper, cuts, lambda, ht, ht2] at hxl hxu hyl hyu hν hsx hsy
  all_goals nlinarith only [hg2, hxl, hxu, hyl, hyu, hν, hsx, hsy, hglo, hghi]

private theorem common_next (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i : Fin 6) (hi : 1 ≤ i.val ∧ i.val ≤ 4)
    (hx : X x j ∈ observation ν i) (hy : X y j ∈ observation ν i)
    (hl : window x j = L i) (hh : window y j = H i)
    (hx' : X x (j + 1) ∈ observation ν (N i))
    (hy' : X y (j + 1) ∈ observation ν (N i))
    (he : window x (j + 1) = window y (j + 1)) :
    window x (j + 1) = C i := by
  obtain ⟨hg2, hglo, hghi, ht, ht2⟩ := algebra
  obtain ⟨ha, hb⟩ := split_bounds ν hν x y j i hi hx hy hl hh
  have hp : 0 < g := by linarith
  have hsx : -1 + i.val * (1 + t) / 5 < X y (j + 1) := by
    have hδ := sub_pos.mpr hν
    nlinarith
  have hr := root y (j + 1)
  rw [← he] at hr
  have ha' := allow ν hν x (j + 1) (N i) hx'
  fin_cases i <;> norm_num at hi ha' hx' hy' ⊢
  · exact (end_labels ν hν x (j + 1)).1 hx'
  all_goals rcases ha' with h | h
  all_goals try exact h
  all_goals rw [h] at hr
  all_goals norm_num [nullLabel, threeLabel, fiveLabel, twoLabel,
    twoFiveLabel, ht, ht2] at hr hsx
  all_goals exfalso; linarith only [hr.2, hsx, hglo, hghi]


local notation "Z" => (fun i : Fin 6 => if i.val ≤ 1 then 2 * t / 5 else
  if i.val = 2 then 1 + 4 * t / 5 else if i.val = 3 then t / 5 else 3 * t / 5)

private theorem second_bounds (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i : Fin 6) (hi : 1 ≤ i.val ∧ i.val ≤ 4)
    (hx : X x j ∈ observation ν i) (hy : X y j ∈ observation ν i)
    (hl : window x j = L i) (hh : window y j = H i)
    (hc : window x (j + 1) = C i) (hd : window y (j + 1) = C i) :
    lambda - ν ≤ g ^ 2 * (X x (j + 2) - Z i) ∧
    lambda - ν ≤ g ^ 2 * (Z i - X y (j + 2)) := by
  obtain ⟨hg2, hglo, hghi, ht, ht2⟩ := algebra
  obtain ⟨ha, hb⟩ := split_bounds ν hν x y j i hi hx hy hl hh
  have hcenter : g * Z i = offset (C i) - (-1 + i.val * (1 + t) / 5) := by
    fin_cases i <;> norm_num at hi
    all_goals norm_num [offset, threeLabel, nullLabel, fiveLabel, ht, ht2]
    all_goals nlinarith only [hg2]
  have hra := congrArg (fun z : ℝ => g * z) (residual x (j + 1))
  have hrb := congrArg (fun z : ℝ => g * z) (residual y (j + 1))
  rw [hc] at hra
  rw [hd] at hrb
  simp only [show j + 1 + 1 = j + 2 by omega] at hra hrb
  constructor <;> nlinarith only [ha, hb, hra, hrb, hcenter]

private theorem third_color (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i c : Fin 6) (hi : 1 ≤ i.val ∧ i.val ≤ 4)
    (ha : lambda - ν ≤ g ^ 2 * (X x (j + 2) - Z i))
    (hb : lambda - ν ≤ g ^ 2 * (Z i - X y (j + 2)))
    (hx : X x (j + 2) ∈ observation ν c) (hy : X y (j + 2) ∈ observation ν c) :
    (i.val = 3 → c = 1 ∨ c = 2) ∧
    (i.val ≠ 3 → c = if i.val = 2 then 5 else 2) := by
  obtain ⟨hg2, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < g ^ 2 := sq_pos_of_pos (by linarith)
  have hδ : 0 < lambda - ν := sub_pos.mpr hν
  have hsx : Z i < X x (j + 2) := by nlinarith
  have hsy : X y (j + 2) < Z i := by nlinarith
  obtain ⟨hxl, hxu⟩ := observation_bounds ν c _ hx
  obtain ⟨hyl, hyu⟩ := observation_bounds ν c _ hy
  fin_cases i <;> fin_cases c <;> norm_num at hi ⊢
  all_goals norm_num [cellLower, cellUpper, cuts, lambda, ht, ht2] at hxl hxu hyl hyu hν hsx hsy
  all_goals nlinarith only [hg2, hxl, hxu, hyl, hyu, hν, hsx, hsy, hglo, hghi]


private theorem clearance_constants :
    g ^ 2 * (g - 1 / 5) = K31 * (1 + g ^ 2) ∧
    g ^ 2 * (t / 5 - g + 2 * t ^ 2 / 5) = K32 * (1 + g ^ 2) ∧
    2 * g ^ 3 / 5 = K4 * (1 + g ^ 2) := by
  obtain ⟨hq, _, _, ht, ht2⟩ := algebra
  refine ⟨?_, ?_, ?_⟩
  · unfold K31
    linear_combination ((3 * g - 11) / 50) * hq
  · rw [ht2, ht]
    unfold K32
    linear_combination ((5 - g) / 20) * hq
  · unfold K4
    linear_combination ((g - 2) / 25) * hq

private theorem three_bound (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (r : ℕ → Fin 6) (hs : SharedAt ν r x y j 3)
    (i : Fin 6) (hi : i = 3 ∨ i = 4) (hc : r j = i)
    (hl : window x j = L i) (hh : window y j = H i)
    (he : window x (j + 1) = window y (j + 1)) :
    (i = 3 → lambda - ν ≤ max K31 K32) ∧
    (i = 4 → lambda - ν ≤ K4) := by
  obtain ⟨h0x, h0y⟩ := hs 0 (by omega)
  simp only [Nat.add_zero, hc] at h0x h0y
  obtain ⟨h1x, h1y⟩ := hs 1 (by omega)
  have hin : 1 ≤ i.val ∧ i.val ≤ 4 := by rcases hi with rfl | rfl <;> decide
  have hn := next_color ν hν x y j i (r (j + 1)) hin h0x h0y hl hh h1x h1y
  rw [hn] at h1x h1y
  have hcommon := common_next ν hν x y j i hin h0x h0y hl hh h1x h1y he
  obtain ⟨ha, hb⟩ := second_bounds ν hν x y j i hin h0x h0y hl hh hcommon (he ▸ hcommon)
  obtain ⟨h2x, h2y⟩ := hs 2 (by omega)
  have hthird := third_color ν hν x y j i (r (j + 2)) hin ha hb h2x h2y
  obtain ⟨hq, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < 1 + g ^ 2 := by positivity
  have hg0 : 0 ≤ g ^ 2 := sq_nonneg g
  obtain ⟨hk31, hk32, hk4⟩ := clearance_constants
  rcases hi with rfl | rfl
  · refine ⟨?_, by norm_num⟩
    intro _
    rcases hthird.1 rfl with h | h
    · rw [h] at h2x
      have hu := (observation_bounds ν 1 _ h2x).2
      have hm := mul_le_mul_of_nonneg_left hu hg0
      norm_num [cellUpper, cuts, lambda] at hm ha
      have heq : g ^ 2 * (g - t ^ 2 / 5 - t / 5) = K31 * (1 + g ^ 2) := by
        rw [ht2]
        convert hk31 using 1 <;> ring
      have hclear : (lambda - ν) * (1 + g ^ 2) ≤ K31 * (1 + g ^ 2) := by
        unfold lambda
        nlinarith only [ha, hm, heq]
      exact ((mul_le_mul_right hp).mp hclear).trans (le_max_left _ _)
    · rw [h] at h2y
      have hu := (observation_bounds ν 2 _ h2y).1
      have hm := mul_le_mul_of_nonneg_left hu hg0
      norm_num [cellLower, cuts, lambda] at hm hb
      have hclear : (lambda - ν) * (1 + g ^ 2) ≤ K32 * (1 + g ^ 2) := by
        unfold lambda
        nlinarith only [hb, hm, hk32]
      exact ((mul_le_mul_right hp).mp hclear).trans (le_max_right _ _)
  · refine ⟨by norm_num, ?_⟩
    intro _
    have h := hthird.2 (by decide)
    norm_num at h
    rw [h] at h2x
    have hu := (observation_bounds ν 2 _ h2x).2
    have hm := mul_le_mul_of_nonneg_left hu hg0
    norm_num [cellUpper, cuts, lambda] at hm ha
    have heq : g ^ 2 * (t - 2 * t ^ 2 / 5 - 3 * t / 5) = K4 * (1 + g ^ 2) := by
      rw [ht2, ht]
      convert hk4 using 1 <;> ring
    have hclear : (lambda - ν) * (1 + g ^ 2) ≤ K4 * (1 + g ^ 2) := by
      unfold lambda
      nlinarith only [ha, hm, heq]
    exact (mul_le_mul_right hp).mp hclear

end D5.S1.Digit.Infinite.SixWindowForcing

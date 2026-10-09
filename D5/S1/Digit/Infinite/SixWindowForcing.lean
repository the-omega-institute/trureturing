/- GID: D5/S1/Digit/Infinite/SixWindowForcing
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SixWindowForcing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local separation and arbitrary-length six-window forcing for actual paired sources. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import D5.S1.Digit.Infinite.OddColorThreeSource
import Mathlib.Tactic.FinCases

set_option autoImplicit false

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

/-- The actual coordinate after deleting j three-bit windows. -/
@[simp] noncomputable def sample (x : LegalDigits) (j : ℕ) : ℝ := kappa (bitShift x (3 * j))

/-- The common next color associated to each ordered separation type. -/
@[simp] def nextColor (i : Fin 6) : Fin 6 :=
  if i.val ≤ 1 then 0 else if i.val ≤ 3 then 1 else 2

/-- The only possible common next label for each ordered separation type. -/
@[simp] def commonNextLabel (i : Fin 6) : Label :=
  if i.val ≤ 1 then threeLabel else if i.val ≤ 3 then nullLabel else fiveLabel

local notation "X" => sample
local notation "L" => D5.S1.Digit.Infinite.OddColorThreeSource.lowLabel
local notation "H" => D5.S1.Digit.Infinite.OddColorThreeSource.highLabel
local notation "N" => nextColor
local notation "C" => commonNextLabel

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
  have hw := D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.window_shift x j
  have hb := D5.S1.Digit.Infinite.OddColorThreeSource.root_bounds (bitShift x (3 * j))
  rw [hw] at hb
  exact hb

private theorem observation_bounds (ν : ℝ) (i : Fin 6) (z : ℝ)
    (hz : z ∈ observation ν i) :
    cellLower i - ν ≤ z ∧ z ≤ cellUpper i + ν :=
  ⟨(le_max_right _ _).trans hz.1, hz.2.trans (min_le_right _ _)⟩

private theorem allow (ν : ℝ) (hν : ν < lambda) (x : LegalDigits)
    (j : ℕ) (i : Fin 6) (hx : X x j ∈ observation ν i) :
    window x j = L i ∨ window x j = H i := by
  simpa only [D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.window_shift] using
    D5.S1.Digit.Infinite.OddColorThreeSource.color_labels ν hν i
      (bitShift x (3 * j)) hx


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
      simp [nullLabel, cellUpper, cellLower, cuts, lambda, ht, ht2] at hr hhi hν
      linarith [hr.1]
  · intro hx
    rcases allow ν hν x j 5 hx with h | h
    · norm_num at h
      rw [h] at hr
      obtain ⟨hlo, hhi⟩ := observation_bounds ν 5 _ hx
      simp [twoLabel, cellUpper, cellLower, cuts, lambda, ht, ht2] at hr hlo hν
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
  all_goals simp [cellLower, cellUpper, cuts, lambda, offset, nullLabel,
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
  fin_cases i <;> fin_cases c <;> simp at hi
  all_goals try simp [Fin.ext_iff]
  all_goals simp [cellLower, cellUpper, cuts, lambda, ht, ht2] at hxl hxu hyl hyu hν hsx hsy
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
  fin_cases i <;> simp at hi
  all_goals simp at ha' hx' hy' ⊢
  · exact (end_labels ν hν x (j + 1)).1 hx'
  all_goals rcases ha' with h | h
  all_goals try exact h
  all_goals rw [h] at hr
  all_goals simp [nullLabel, threeLabel, fiveLabel, twoLabel,
    twoFiveLabel, ht, ht2] at hr hsx
  all_goals exfalso; linarith only [hr.2, hsx, hglo, hghi]


/-- The two-step center associated to an ordered separation type. -/
@[simp] noncomputable def secondCenter (i : Fin 6) : ℝ :=
  if i.val ≤ 1 then 2 * t / 5 else if i.val = 2 then 1 + 4 * t / 5 else
    if i.val = 3 then t / 5 else 3 * t / 5

local notation "Z" => secondCenter

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
    all_goals simp [offset, threeLabel, nullLabel, fiveLabel, ht, ht2]
    all_goals nlinarith only [hg2]
  have hcenter2 := congrArg (fun z : ℝ => g * z) hcenter
  have hra := congrArg (fun z : ℝ => g * z) (residual x (j + 1))
  have hrb := congrArg (fun z : ℝ => g * z) (residual y (j + 1))
  rw [hc] at hra
  rw [hd] at hrb
  simp only [show j + 1 + 1 = j + 2 by omega] at hra hrb
  simp only [sample] at ha hb ⊢
  constructor <;> nlinarith only [ha, hb, hra, hrb, hcenter2]

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
  fin_cases i <;> fin_cases c <;> simp at hi
  all_goals try simp [Fin.ext_iff]
  all_goals simp [cellLower, cellUpper, cuts, lambda, ht, ht2] at hxl hxu hyl hyu hν hsx hsy
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
  · refine ⟨?_, by intro h; have h := congrArg Fin.val h; norm_num at h⟩
    intro _
    rcases hthird.1 rfl with h | h
    · rw [h] at h2x
      have hu := (observation_bounds ν 1 _ h2x).2
      have hm := mul_le_mul_of_nonneg_left hu hg0
      simp [cellUpper, cuts, lambda] at hm ha
      have heq : g ^ 2 * (g - t ^ 2 / 5 - t / 5) = K31 * (1 + g ^ 2) := by
        rw [ht2, ht]
        convert hk31 using 1 <;> ring
      have hclear : (lambda - ν) * (1 + g ^ 2) ≤ K31 * (1 + g ^ 2) := by
        unfold lambda
        nlinarith only [ha, hm, heq]
      exact ((mul_le_mul_iff_of_pos_right hp).mp hclear).trans (le_max_left _ _)
    · rw [h] at h2y
      have hu := (observation_bounds ν 2 _ h2y).1
      have hm := mul_le_mul_of_nonneg_left hu hg0
      simp [cellLower, cuts, lambda] at hm hb
      have hclear : (lambda - ν) * (1 + g ^ 2) ≤ K32 * (1 + g ^ 2) := by
        unfold lambda
        nlinarith only [hb, hm, hk32]
      exact ((mul_le_mul_iff_of_pos_right hp).mp hclear).trans (le_max_right _ _)
  · refine ⟨by intro h; have h := congrArg Fin.val h; norm_num at h, ?_⟩
    intro _
    have h := hthird.2 (by decide)
    norm_num at h
    rw [h] at h2x
    have hu := (observation_bounds ν 2 _ h2x).2
    have hm := mul_le_mul_of_nonneg_left hu hg0
    simp [cellUpper, cuts, lambda] at hm ha
    have heq : g ^ 2 * (t - 2 * t ^ 2 / 5 - 3 * t / 5) = K4 * (1 + g ^ 2) := by
      rw [ht2, ht]
      convert hk4 using 1 <;> ring
    have hclear : (lambda - ν) * (1 + g ^ 2) ≤ K4 * (1 + g ^ 2) := by
      unfold lambda
      nlinarith only [ha, hm, heq]
    exact (mul_le_mul_iff_of_pos_right hp).mp hclear


private theorem four_bound (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (r : ℕ → Fin 6) (hs : SharedAt ν r x y j 4)
    (hc : r j = 2) (hl : window x j = nullLabel) (hh : window y j = fiveLabel)
    (he : window x (j + 1) = window y (j + 1)) : lambda - ν ≤ J := by
  obtain ⟨h0x, h0y⟩ := hs 0 (by omega)
  simp only [Nat.add_zero, hc] at h0x h0y
  obtain ⟨h1x, h1y⟩ := hs 1 (by omega)
  have hn := next_color ν hν x y j 2 (r (j + 1)) (by decide) h0x h0y hl hh h1x h1y
  rw [hn] at h1x h1y
  have hc1 := common_next ν hν x y j 2 (by decide) h0x h0y hl hh h1x h1y he
  obtain ⟨ha, hb⟩ := second_bounds ν hν x y j 2 (by decide) h0x h0y hl hh hc1 (he ▸ hc1)
  obtain ⟨h2x, h2y⟩ := hs 2 (by omega)
  have hn2 := (third_color ν hν x y j 2 (r (j + 2)) (by decide) ha hb h2x h2y).2 (by decide)
  norm_num at hn2
  rw [hn2] at h2x h2y
  have hx2 := (end_labels ν hν x (j + 2)).2 h2x
  have hy2 := (end_labels ν hν y (j + 2)).2 h2y
  obtain ⟨hq, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < g := by linarith
  let w : ℝ := (g - 5) / 10
  have hw : g * w = offset twoFiveLabel - (1 + 4 * t / 5) := by
    simp [w, offset, twoFiveLabel, ht, ht2]
    nlinarith only [hq]
  have hra := congrArg (fun z : ℝ => g ^ 2 * z) (residual x (j + 2))
  have hrb := congrArg (fun z : ℝ => g ^ 2 * z) (residual y (j + 2))
  rw [hx2] at hra
  rw [hy2] at hrb
  norm_num at ha hb
  have hw2 := congrArg (fun z : ℝ => g ^ 2 * z) hw
  have ha3 : lambda - ν ≤ g ^ 3 * (w - X x (j + 3)) := by
    simp only [show j + 2 + 1 = j + 3 by omega] at hra
    simp only [sample]
    nlinarith only [ha, hra, hw2]
  have hb3 : lambda - ν ≤ g ^ 3 * (X y (j + 3) - w) := by
    simp only [show j + 2 + 1 = j + 3 by omega] at hrb
    simp only [sample]
    nlinarith only [hb, hrb, hw2]
  have hp3 : 0 < g ^ 3 := pow_pos hp _
  have hδ : 0 < lambda - ν := sub_pos.mpr hν
  have hsx : X x (j + 3) < w := by nlinarith
  have hsy : w < X y (j + 3) := by nlinarith
  obtain ⟨h3x, h3y⟩ := hs 3 (by omega)
  have hc3 : r (j + 3) = 0 := by
    obtain ⟨hxl, hxu⟩ := observation_bounds ν (r (j + 3)) _ h3x
    obtain ⟨hyl, hyu⟩ := observation_bounds ν (r (j + 3)) _ h3y
    generalize r (j + 3) = c at hxl hxu hyl hyu ⊢
    fin_cases c <;> norm_num
    all_goals simp [w, cellLower, cellUpper, cuts, lambda, ht, ht2] at hxl hxu hyl hyu hν hsx hsy
    all_goals nlinarith only [hq, hxl, hxu, hyl, hyu, hν, hsx, hsy, hglo, hghi]
  rw [hc3] at h3y
  have hu := (observation_bounds ν 0 _ h3y).2
  have hm := mul_le_mul_of_nonneg_left hu hp3.le
  simp [cellUpper, cuts, lambda] at hm
  have hwclear : -t ^ 2 - w = 2 * g / 5 := by rw [ht2]; dsimp [w]; ring
  have hwclear3 := congrArg (fun z : ℝ => g ^ 3 * z) hwclear
  have hJ : J * (1 + g ^ 3) = 2 * g ^ 4 / 5 := by
    unfold J
    field_simp [show 1 + g ^ 3 ≠ 0 by positivity]
  have hclear : (lambda - ν) * (1 + g ^ 3) ≤ J * (1 + g ^ 3) := by
    simp only [sample] at hb3
    unfold lambda at hb3 ⊢
    nlinarith only [hb3, hm, hwclear3, hJ]
  exact (mul_le_mul_iff_of_pos_right (by positivity : 0 < 1 + g ^ 3)).mp hclear

private theorem budget_clearance (ν : ℝ) (hν : ν ≤ rho) :
    max K31 K32 < K4 ∧ J < K4 ∧ g ^ 4 / 5 < K4 ∧ K4 < lambda - ν := by
  obtain ⟨hq, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < g := by linarith
  have hg3 : g ^ 3 = 17 * g - 4 := by
    linear_combination (g - 4) * hq
  have hg4 : g ^ 4 = 17 - 72 * g := by
    linear_combination (g ^ 2 - 4 * g + 17) * hq
  have hK := clearance_constants.2.2
  refine ⟨max_lt ?_ ?_, ?_, ?_, ?_⟩
  · unfold K31 K4
    linarith only [hghi]
  · unfold K32 K4
    linarith only [hglo]
  · unfold J
    apply (div_lt_iff₀ (by positivity : 0 < 5 * (1 + g ^ 3))).2
    unfold K4
    rw [hg3, hg4]
    nlinarith only [hq, hglo]
  · apply (mul_lt_mul_iff_of_pos_right (by positivity : 0 < 1 + g ^ 2)).mp
    calc
      g ^ 4 / 5 * (1 + g ^ 2) = g ^ 3 / 5 * (g * (1 + g ^ 2)) := by ring
      _ < g ^ 3 / 5 * 2 := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        nlinarith only [hq, hglo, hghi]
      _ = K4 * (1 + g ^ 2) := by linarith only [hK]
  · unfold K4 lambda rho at *
    rw [ht2]
    linarith only [hν, hghi]


private theorem ordered_pairs (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i : Fin 6) (hx : X x j ∈ observation ν i)
    (hy : X y j ∈ observation ν i) (hne : window x j ≠ window y j) :
    (1 ≤ i.val ∧ i.val ≤ 4) ∧
      ((window x j = L i ∧ window y j = H i) ∨
        (window x j = H i ∧ window y j = L i)) := by
  have hi0 : i.val ≠ 0 := by
    intro hi
    have he : i = 0 := Fin.ext hi
    subst i
    exact hne ((end_labels ν hν x j).1 hx |>.trans ((end_labels ν hν y j).1 hy).symm)
  have hi5 : i.val ≠ 5 := by
    intro hi
    have he : i = 5 := Fin.ext hi
    subst i
    exact hne ((end_labels ν hν x j).2 hx |>.trans ((end_labels ν hν y j).2 hy).symm)
  refine ⟨by have := i.isLt; omega, ?_⟩
  rcases allow ν hν x j i hx with ha | ha <;>
    rcases allow ν hν y j i hy with hb | hb
  · exact False.elim (hne (ha.trans hb.symm))
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact False.elim (hne (ha.trans hb.symm))

private theorem pair_color (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i c : Fin 6) (hi : 1 ≤ i.val ∧ i.val ≤ 4)
    (hx : X x j ∈ observation ν c) (hy : X y j ∈ observation ν c)
    (hl : window x j = L i) (hh : window y j = H i) : c = i := by
  have hc0 : c.val ≠ 0 := by
    intro he
    have hec : c = 0 := Fin.ext he
    have he := (end_labels ν hν y j).1 (hec ▸ hy)
    rw [hh] at he
    have he1 := congrArg (fun l : Label => l.val 1) he
    have he2 := congrArg (fun l : Label => l.val 2) he
    fin_cases i <;> simp at hi
    all_goals simp [nullLabel, threeLabel, fiveLabel, twoLabel, twoFiveLabel] at he1 he2
  have hc5 : c.val ≠ 5 := by
    intro he
    have hec : c = 5 := Fin.ext he
    have he := (end_labels ν hν x j).2 (hec ▸ hx)
    rw [hl] at he
    have he0 := congrArg (fun l : Label => l.val 0) he
    have he2 := congrArg (fun l : Label => l.val 2) he
    fin_cases i <;> simp at hi
    all_goals simp [nullLabel, threeLabel, fiveLabel, twoLabel, twoFiveLabel] at he0 he2
  have ha := allow ν hν x j c hx
  have hb := allow ν hν y j c hy
  rw [hl] at ha
  rw [hh] at hb
  fin_cases i <;> fin_cases c <;> simp at hi hc0 hc5
  all_goals try simp [Fin.ext_iff]
  all_goals rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals
    have ha0 := congrArg (fun l : Label => l.val 0) ha
    have ha1 := congrArg (fun l : Label => l.val 1) ha
    have ha2 := congrArg (fun l : Label => l.val 2) ha
    have hb0 := congrArg (fun l : Label => l.val 0) hb
    have hb1 := congrArg (fun l : Label => l.val 1) hb
    have hb2 := congrArg (fun l : Label => l.val 2) hb
    simp [nullLabel, threeLabel, fiveLabel, twoLabel, twoFiveLabel]
      at ha0 ha1 ha2 hb0 hb1 hb2

private theorem high_next (ν : ℝ) (hν : ν < lambda) (x y : LegalDigits)
    (j : ℕ) (i : Fin 6) (hi : 2 ≤ i.val ∧ i.val ≤ 4)
    (hx : X x j ∈ observation ν i) (hy : X y j ∈ observation ν i)
    (hl : window x j = L i) (hh : window y j = H i)
    (hy' : X y (j + 1) ∈ observation ν (N i)) :
    window y (j + 1) = H (N i) := by
  obtain ⟨hq, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < g := by linarith
  obtain ⟨_, hb⟩ := split_bounds ν hν x y j i (by omega) hx hy hl hh
  have hδ := sub_pos.mpr hν
  have hs : -1 + i.val * (1 + t) / 5 < X y (j + 1) := by nlinarith
  have hr := root y (j + 1)
  have hc := allow ν hν y (j + 1) (N i) hy'
  fin_cases i <;> simp at hi
  all_goals simp at hc ⊢
  all_goals rcases hc with h | h
  all_goals try exact h
  all_goals rw [h] at hr
  all_goals simp [nullLabel, threeLabel, fiveLabel, twoLabel,
    twoFiveLabel, ht, ht2] at hr hs
  all_goals exfalso; nlinarith only [hq, hr.2, hs, hglo, hghi]

private theorem forced_next (ν : ℝ) (hν : ν < lambda)
    (x y : LegalDigits) (j : ℕ) (i : Fin 6) (hi : 2 ≤ i.val ∧ i.val ≤ 4)
    (hb : (if i.val = 2 then J else if i.val = 3 then max K31 K32 else K4) < lambda - ν)
    (r : ℕ → Fin 6) (hs : SharedAt ν r x y j (if i.val = 2 then 4 else 3))
    (hl : window x j = L i) (hh : window y j = H i) :
    r (j + 1) = N i ∧ window x (j + 1) = L (N i) ∧
      window y (j + 1) = H (N i) := by
  have hlen : 2 ≤ if i.val = 2 then 4 else 3 := by split <;> omega
  obtain ⟨h0x, h0y⟩ := hs 0 (by omega)
  simp only [Nat.add_zero] at h0x h0y
  have hc := pair_color ν hν x y j i (r j) (by omega) h0x h0y hl hh
  rw [hc] at h0x h0y
  obtain ⟨h1x, h1y⟩ := hs 1 (by omega)
  have hn := next_color ν hν x y j i (r (j + 1)) (by omega) h0x h0y hl hh h1x h1y
  rw [hn] at h1x h1y
  have hhy := high_next ν hν x y j i hi h0x h0y hl hh h1y
  have hne : window x (j + 1) ≠ window y (j + 1) := by
    intro he
    fin_cases i <;> simp at hi
    all_goals simp at hs hl hh hb
    · exact (not_le_of_gt hb)
        (four_bound ν hν x y j r hs hc hl hh he)
    · exact (not_le_of_gt (max_lt hb.1 hb.2))
        ((three_bound ν hν x y j r hs 3 (Or.inl rfl) hc hl hh he).1 rfl)
    · exact (not_le_of_gt hb)
        ((three_bound ν hν x y j r hs 4 (Or.inr rfl) hc hl hh he).2 rfl)
  refine ⟨hn, ?_, hhy⟩
  rcases allow ν hν x (j + 1) (N i) h1x with h | h
  · exact h
  · exact False.elim (hne (h.trans hhy.symm))

private theorem three_forcing (ν : ℝ) (hν : ν < lambda)
    (hδ4 : g ^ 4 / 5 < lambda - ν)
    (x y : LegalDigits) (j : ℕ) (r : ℕ → Fin 6) (hs : SharedAt ν r x y j 3)
    (hl : window x j = threeLabel) (hh : window y j = nullLabel) :
    r j = 1 ∧ r (j + 1) = 0 ∧ r (j + 2) = 2 ∧
    window x (j + 1) = threeLabel ∧ window y (j + 1) = threeLabel ∧
    window x (j + 2) = fiveLabel ∧ window y (j + 2) = nullLabel := by
  obtain ⟨h0x, h0y⟩ := hs 0 (by omega)
  simp only [Nat.add_zero] at h0x h0y
  have hc := pair_color ν hν x y j 1 (r j) (by decide) h0x h0y hl hh
  rw [hc] at h0x h0y
  obtain ⟨h1x, h1y⟩ := hs 1 (by omega)
  have hn := next_color ν hν x y j 1 (r (j + 1)) (by decide) h0x h0y hl hh h1x h1y
  norm_num at hn
  rw [hn] at h1x h1y
  have hx1 := (end_labels ν hν x (j + 1)).1 h1x
  have hy1 := (end_labels ν hν y (j + 1)).1 h1y
  obtain ⟨ha, hb⟩ := second_bounds ν hν x y j 1 (by decide) h0x h0y hl hh hx1 hy1
  obtain ⟨h2x, h2y⟩ := hs 2 (by omega)
  have hn2 := (third_color ν hν x y j 1 (r (j + 2)) (by decide) ha hb h2x h2y).2 (by decide)
  norm_num at hn2
  rw [hn2] at h2x h2y
  obtain ⟨hq, hglo, hghi, ht, ht2⟩ := algebra
  have hp : 0 < g ^ 2 := sq_pos_of_pos (by linarith)
  have hδ := sub_pos.mpr hν
  have hz : 2 * t / 5 - g = g ^ 2 / 5 := by rw [ht]; nlinarith only [hq]
  have hz2 := congrArg (fun z : ℝ => g ^ 2 * z) hz
  have hxg : g < X x (j + 2) := by
    change lambda - ν ≤ g ^ 2 * (X x (j + 2) - 2 * t / 5) at ha
    have hs := (mul_pos_iff_of_pos_left hp).mp (lt_of_lt_of_le hδ ha)
    linarith only [hs, hz, hp]
  have hyg : X y (j + 2) < g := by
    change lambda - ν ≤ g ^ 2 * (2 * t / 5 - X y (j + 2)) at hb
    have hs : 0 < g ^ 2 * (g - X y (j + 2)) := by
      nlinarith only [hb, hz2, hδ4]
    have hh := (mul_pos_iff_of_pos_left hp).mp hs
    linarith only [hh]
  have hxl : window x (j + 2) = fiveLabel := by
    rcases allow ν hν x (j + 2) 2 h2x with h | h
    · have hr := root x (j + 2)
      norm_num at h
      rw [h] at hr
      simp [nullLabel] at hr
      exact False.elim (not_le_of_gt hxg hr.2)
    · exact h
  have hyl : window y (j + 2) = nullLabel := by
    rcases allow ν hν y (j + 2) 2 h2y with h | h
    · exact h
    · have hr := root y (j + 2)
      norm_num at h
      rw [h] at hr
      simp [fiveLabel] at hr
      exact False.elim (not_le_of_gt hyg hr.1)
  exact ⟨hc, hn, hn2, hx1, hy1, hxl, hyl⟩

private theorem six_forcing (ν : ℝ) (hν : ν < lambda) (hJ : J < lambda - ν)
    (hδ4 : g ^ 4 / 5 < lambda - ν)
    (start m : ℕ) (hm : 1 ≤ m) (x y : LegalDigits) (r : ℕ → Fin 6)
    (hs : SharedAt ν r x y start (6 * m))
    (hl : window x start = threeLabel) (hh : window y start = nullLabel) :
    ∀ j < 6 * m,
      window x (start + j) = (blockA[j % 6]?).getD nullLabel ∧
      window y (start + j) = (blockB[j % 6]?).getD nullLabel := by
  have hsub (a n : ℕ) (han : a + n ≤ 6 * m) : SharedAt ν r x y (start + a) n := by
    intro k hk
    simpa only [Nat.add_assoc] using hs (a + k) (by omega)
  have hswap (a : ℕ) (ha : a + 6 ≤ 6 * m)
      (hax : window x (start + a) = threeLabel) (hay : window y (start + a) = nullLabel) :
      window x (start + a + 3) = nullLabel ∧ window y (start + a + 3) = threeLabel := by
    have ht := three_forcing ν hν hδ4 x y (start + a) r (hsub a 3 (by omega)) hax hay
    have hrev : SharedAt ν r y x (start + a + 2) 4 := by
      intro k hk
      simpa only [Nat.add_assoc] using ((hsub (a + 2) 4 (by omega)) k hk).symm
    have hf := forced_next ν hν y x (start + a + 2) 2 (by decide) (by simpa using hJ) r hrev ht.2.2.2.2.2.2
      ht.2.2.2.2.2.1
    simpa [Nat.add_assoc] using And.intro hf.2.2 hf.2.1
  have hstart : ∀ b, b < m →
      window x (start + 6 * b) = threeLabel ∧ window y (start + 6 * b) = nullLabel := by
    intro b
    induction b with
    | zero => intro _; simpa using And.intro hl hh
    | succ b ih =>
      intro hb
      obtain ⟨hax, hay⟩ := ih (by omega)
      obtain ⟨hx3, hy3⟩ := hswap (6 * b) (by omega) hax hay
      have hrev : SharedAt ν r y x (start + 6 * b + 3) 3 := by
        intro k hk
        simpa only [Nat.add_assoc] using ((hsub (6 * b + 3) 3 (by omega)) k hk).symm
      have ht := three_forcing ν hν hδ4 y x (start + 6 * b + 3) r hrev hy3 hx3
      have hf := forced_next ν hν x y (start + 6 * b + 5) 2 (by decide) (by simpa using hJ) r
        (by simpa [Nat.add_assoc] using hsub (6 * b + 5) 4 (by omega))
        (by simpa [Nat.add_assoc] using ht.2.2.2.2.2.2)
        (by simpa [Nat.add_assoc] using ht.2.2.2.2.2.1)
      simpa [Nat.mul_succ, Nat.add_assoc] using And.intro hf.2.1 hf.2.2
  intro j hj
  let b := j / 6
  have hb : b < m := by dsimp [b]; omega
  have he : j = 6 * b + j % 6 := by
    dsimp only [b]
    exact (Nat.mod_add_div j 6).symm.trans (Nat.add_comm _ _)
  obtain ⟨hax, hay⟩ := hstart b hb
  have ht := three_forcing ν hν hδ4 x y (start + 6 * b) r (hsub (6 * b) 3 (by omega)) hax hay
  obtain ⟨hx3, hy3⟩ := hswap (6 * b) (by omega) hax hay
  have hrev : SharedAt ν r y x (start + 6 * b + 3) 3 := by
    intro k hk
    simpa only [Nat.add_assoc] using ((hsub (6 * b + 3) 3 (by omega)) k hk).symm
  have ht' := three_forcing ν hν hδ4 y x (start + 6 * b + 3) r hrev hy3 hx3
  have hr : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨
      j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals simp only [hr]; rw [he, hr]; simp [blockA, blockB]
  · exact ⟨hax, hay⟩
  · exact ⟨ht.2.2.2.1, ht.2.2.2.2.1⟩
  · exact ⟨ht.2.2.2.2.2.1, ht.2.2.2.2.2.2⟩
  · exact ⟨hx3, hy3⟩
  · simpa [Nat.add_assoc] using And.intro ht'.2.2.2.2.1 ht'.2.2.2.1
  · simpa [Nat.add_assoc] using And.intro ht'.2.2.2.2.2.2 ht'.2.2.2.2.2.1


/-- Lower endpoints of the six critical closed expansions. -/
@[simp] noncomputable def closedLower : Fin 6 → ℝ :=
  ![-1, -6 * t ^ 2 / 5, g - 2 * t ^ 2 / 5, t - 3 * t ^ 2 / 5,
    2 * t - 4 * t ^ 2 / 5, 2 * t]
/-- Upper endpoints of the six critical closed expansions. -/
@[simp] noncomputable def closedUpper : Fin 6 → ℝ :=
  ![-t ^ 2, g - t ^ 2 / 5, t - 2 * t ^ 2 / 5, 2 * t - 3 * t ^ 2 / 5,
    2 * t + t ^ 2 / 5, 1 + t]

local notation "B" => closedLower
local notation "U" => closedUpper

private theorem intervals (ν : ℝ) (h0 : 0 ≤ ν) (hν : ν ≤ lambda) (i : Fin 6) :
    observation ν i = Set.Icc
      (if i = 0 then -1 else B i + (lambda - ν))
      (if i = 5 then 1 + t else U i - (lambda - ν)) := by
  obtain ⟨hq, hglo, hghi, ht, ht2⟩ := algebra
  have hlo : max (-1) (cellLower i - ν) =
      if i = 0 then -1 else B i + (lambda - ν) := by
    fin_cases i <;> simp [cellLower, cuts, lambda]
    all_goals try exact h0
    all_goals first
      | rw [max_eq_left (by linarith only [h0])]
      | rw [max_eq_right (by dsimp [lambda] at hν; nlinarith only [hν, hq, ht, ht2, hglo, hghi])]
    all_goals ring
  have hhi : min (1 + t) (cellUpper i + ν) =
      if i = 5 then 1 + t else U i - (lambda - ν) := by
    fin_cases i <;> simp [cellUpper, cuts, lambda]
    all_goals try exact h0
    all_goals first
      | rw [min_eq_left (by linarith only [h0])]
      | rw [min_eq_right (by dsimp [lambda] at hν; nlinarith only [hν, hq, ht, ht2, hglo, hghi])]
    all_goals ring
  exact congrArg₂ Set.Icc hlo hhi

/-- Closed expansions, ordered local separation, budget-dependent local forcing,
and six-window forcing at any starting position and any positive length. -/
theorem result (ν : ℝ) (h0 : 0 ≤ ν) (hν : ν < lambda) :
    (∀ i : Fin 6, observation lambda i = Set.Icc (B i) (U i)) ∧
    (∀ i : Fin 6, observation ν i = Set.Icc
      (if i = 0 then -1 else B i + (lambda - ν))
      (if i = 5 then 1 + t else U i - (lambda - ν))) ∧
    (∀ (x : LegalDigits) j,
      (X x j ∈ observation ν 0 → window x j = threeLabel) ∧
      (X x j ∈ observation ν 5 → window x j = twoFiveLabel)) ∧
    (∀ (x y : LegalDigits) j (i : Fin 6),
      X x j ∈ observation ν i → X y j ∈ observation ν i →
      window x j ≠ window y j → (1 ≤ i.val ∧ i.val ≤ 4) ∧
        ((window x j = L i ∧ window y j = H i) ∨
          (window x j = H i ∧ window y j = L i))) ∧
    (∀ (x y : LegalDigits) j (i : Fin 6),
      1 ≤ i.val → i.val ≤ 4 →
      X x j ∈ observation ν i → X y j ∈ observation ν i →
      window x j = L i → window y j = H i →
      X x (j + 1) ≤ (-1 + i.val * (1 + t) / 5) - (lambda - ν) / g ∧
      (-1 + i.val * (1 + t) / 5) + (lambda - ν) / g ≤ X y (j + 1)) ∧
    (∀ (x y : LegalDigits) j (r : ℕ → Fin 6) (i : Fin 6),
      1 ≤ i.val → i.val ≤ 4 → SharedAt ν r x y j 2 →
      window x j = L i → window y j = H i →
      r j = i ∧ r (j + 1) = N i ∧
      (window x (j + 1) = window y (j + 1) → window x (j + 1) = C i)) ∧
    (∀ (x y : LegalDigits) j (r : ℕ → Fin 6), SharedAt ν r x y j 3 →
      r j = 3 → window x j = fiveLabel → window y j = twoLabel →
      window x (j + 1) = window y (j + 1) → lambda - ν ≤ max K31 K32) ∧
    (∀ (x y : LegalDigits) j (r : ℕ → Fin 6), SharedAt ν r x y j 3 →
      r j = 4 → window x j = twoLabel → window y j = twoFiveLabel →
      window x (j + 1) = window y (j + 1) → lambda - ν ≤ K4) ∧
    (∀ (x y : LegalDigits) j (r : ℕ → Fin 6), SharedAt ν r x y j 4 →
      r j = 2 → window x j = nullLabel → window y j = fiveLabel →
      window x (j + 1) = window y (j + 1) → lambda - ν ≤ J) ∧
    (∀ (x y : LegalDigits) j (i : Fin 6) (r : ℕ → Fin 6),
      2 ≤ i.val → i.val ≤ 4 →
      (if i.val = 2 then J else if i.val = 3 then max K31 K32 else K4) < lambda - ν →
      SharedAt ν r x y j (if i.val = 2 then 4 else 3) →
      window x j = L i → window y j = H i →
      r (j + 1) = N i ∧ window x (j + 1) = L (N i) ∧
        window y (j + 1) = H (N i)) ∧
    (g ^ 4 / 5 < lambda - ν → ∀ (x y : LegalDigits) j (r : ℕ → Fin 6),
      SharedAt ν r x y j 3 → window x j = threeLabel → window y j = nullLabel →
      r j = 1 ∧ r (j + 1) = 0 ∧ r (j + 2) = 2 ∧
      window x (j + 1) = threeLabel ∧ window y (j + 1) = threeLabel ∧
      window x (j + 2) = fiveLabel ∧ window y (j + 2) = nullLabel) ∧
    (J < lambda - ν → g ^ 4 / 5 < lambda - ν →
      ∀ start m : ℕ, 1 ≤ m → ∀ (x y : LegalDigits) (r : ℕ → Fin 6),
      SharedAt ν r x y start (6 * m) →
      window x start = threeLabel → window y start = nullLabel →
      ∀ j < 6 * m, window x (start + j) = (blockA[j % 6]?).getD nullLabel ∧
        window y (start + j) = (blockB[j % 6]?).getD nullLabel) ∧
    (ν ≤ rho → max K31 K32 < lambda - ν ∧ J < lambda - ν ∧
      g ^ 4 / 5 < lambda - ν ∧ K4 < lambda - ν) ∧
    K4 = 2 * g ^ 3 / (5 * (1 + g ^ 2)) := by
  obtain ⟨_, hglo, _, _, _⟩ := algebra
  have hp : 0 < g := by linarith
  refine ⟨?_, intervals ν h0 hν.le, end_labels ν hν, ordered_pairs ν hν, ?_, ?_, ?_, ?_,
    four_bound ν hν, ?_, three_forcing ν hν, six_forcing ν hν, ?_, ?_⟩
  · intro i
    have h := intervals lambda (by dsimp [lambda]; positivity) le_rfl i
    fin_cases i <;> simpa using h
  · intro x y j i hi hi' hx hy hl hh
    obtain ⟨ha, hb⟩ := split_bounds ν hν x y j i ⟨hi, hi'⟩ hx hy hl hh
    constructor
    · have h := (div_le_iff₀' hp).2 ha
      linarith only [h]
    · have h := (div_le_iff₀' hp).2 hb
      linarith only [h]
  · intro x y j r i hi hi' hs hl hh
    obtain ⟨h0x, h0y⟩ := hs 0 (by omega)
    simp only [Nat.add_zero] at h0x h0y
    have hc := pair_color ν hν x y j i (r j) ⟨hi, hi'⟩ h0x h0y hl hh
    rw [hc] at h0x h0y
    obtain ⟨h1x, h1y⟩ := hs 1 (by omega)
    have hn := next_color ν hν x y j i (r (j + 1)) ⟨hi, hi'⟩ h0x h0y hl hh h1x h1y
    rw [hn] at h1x h1y
    exact ⟨hc, hn, common_next ν hν x y j i ⟨hi, hi'⟩ h0x h0y hl hh h1x h1y⟩
  · intro x y j r hs hc hl hh he
    exact (three_bound ν hν x y j r hs 3 (Or.inl rfl) hc hl hh he).1 rfl
  · intro x y j r hs hc hl hh he
    exact (three_bound ν hν x y j r hs 4 (Or.inr rfl) hc hl hh he).2 rfl
  · intro x y j i r hi hi' hb hs hl hh
    exact forced_next ν hν x y j i ⟨hi, hi'⟩ hb r hs hl hh
  · intro hρ
    obtain ⟨ha, hb, hc, hd⟩ := budget_clearance ν hρ
    exact ⟨ha.trans hd, hb.trans hd, hc.trans hd, hd⟩
  · apply (eq_div_iff (by positivity : 5 * (1 + g ^ 2) ≠ 0)).2
    nlinarith only [clearance_constants.2.2]

end D5.S1.Digit.Infinite.SixWindowForcing

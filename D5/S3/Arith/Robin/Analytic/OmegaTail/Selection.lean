/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Selection
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Selection
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Prime capacities and exact cardinalities for finite density selections. -/

import D5.S3.Arith.Robin.Analytic.OmegaTailUpper

/-! Finite logarithmic prime capacities, rounding adjustment, and product budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper

private lemma prime_capacity_aux {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => primeCount (c * t) / (t / log t)) atTop (𝓝 c) := by
  have hct : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hlog : Tendsto (fun t : ℝ => log (c * t) / log t) atTop (𝓝 1) := by
    have h := (tendsto_log_atTop.const_div_atTop (log c)).add
      (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [log_mul hc.ne' (by linarith : t ≠ 0), add_div,
      div_self (log_pos ht).ne']
  have h := ((pi_normalized.comp hct).div hlog (by norm_num : (1 : ℝ) ≠ 0)).mul_const c
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (max 1 (1 / c))] with t ht
  have ht0 : 0 < t := lt_trans (by positivity : (0 : ℝ) < max 1 (1 / c)) ht
  have hct1 : 1 < c * t := by
    have := lt_of_le_of_lt (le_max_right (1 : ℝ) (1 / c)) ht
    apply (div_lt_iff₀ hc).mp at this
    simpa only [one_mul, mul_comm] using this
  field_simp [ht0.ne', hc.ne', (log_pos hct1).ne',
    (log_pos (lt_of_le_of_lt (le_max_left (1 : ℝ) (1 / c)) ht)).ne']

/-- The prime number theorem on the exact logarithmic scale used for the tail count. -/
private lemma prime_capacity {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => primeCount (c * log x) / scale x) atTop (𝓝 c) := by
  simpa only [scale, Function.comp_def] using
    (prime_capacity_aux hc).comp tendsto_log_atTop

/-- Each fixed logarithmic window has capacity equal to its length on the counting scale. -/
private lemma prime_window_capacity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ =>
      (primeCount (b * log x) - primeCount (a * log x)) / scale x)
      atTop (𝓝 (b - a)) := by
  simpa only [sub_div] using (prime_capacity hb).sub (prime_capacity ha)

lemma primeInterval_card {a b : ℝ} (hab : a ≤ b) :
    ((primeInterval a b).card : ℝ) = primeCount b - primeCount a := by
  have he : primeInterval a b = Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ := by
    ext p
    simp only [primeInterval, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun h => (Nat.not_le_of_lt hlo) h.1⟩
    · rintro ⟨⟨hhi, hp⟩, hlo⟩
      exact ⟨⟨lt_of_not_ge (fun h => hlo ⟨h, hp⟩), hhi⟩, hp⟩
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.floor_mono hab),
        (Nat.mem_primesLE.mp hp).2⟩
  rw [he, Finset.card_sdiff_of_subset hsub,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting,
    Nat.cast_sub (Nat.monotone_primeCounting (Nat.floor_mono hab))]
  rfl

/-- Capacities count actual primes in the disjoint real-endpoint windows. -/
lemma primeInterval_capacity {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ => ((primeInterval (a * log x) (b * log x)).card : ℝ) / scale x)
      atTop (𝓝 (b - a)) := by
  apply (prime_window_capacity ha (ha.trans hab)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [primeInterval_card (mul_le_mul_of_nonneg_right hab.le (log_pos hx).le)]

/-- The exact integer count strictly above the second-order threshold. -/
def selectedCount (lambda x : ℝ) : ℕ := ⌊threshold lambda x⌋₊ + 1

private lemma threshold_ratio (lambda : ℝ) :
    Tendsto (fun x : ℝ => threshold lambda x / scale x) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add
    ((tendsto_log_atTop.comp tendsto_log_atTop).const_div_atTop lambda)
  simp only [add_zero, Function.comp_def] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (exp 1)] with x hx
  dsimp only [threshold]
  field_simp [(scale_pos hx).ne']

private lemma threshold_atTop (lambda : ℝ) :
    Tendsto (threshold lambda) atTop atTop := by
  apply (scale_tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1)
    (threshold_ratio lambda)).congr'
  filter_upwards [eventually_gt_atTop (exp 1)] with x hx
  exact mul_div_cancel₀ _ (scale_pos hx).ne'

private lemma selected_error (lambda : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ (selectedCount lambda x : ℝ) - threshold lambda x ∧
      (selectedCount lambda x : ℝ) - threshold lambda x ≤ 1 := by
  filter_upwards [(threshold_atTop lambda).eventually_ge_atTop 0] with x hx
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one (threshold lambda x)
  simp only [selectedCount, Nat.cast_add, Nat.cast_one]
  exact ⟨by linarith, by linarith⟩

/-- The logarithmic rounding error is negligible on the counting scale. -/
lemma loglog_div_scale :
    Tendsto (fun x : ℝ => log (log x) / scale x) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop 2
    (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp tendsto_log_atTop
  simp only [rpow_two, rpow_one, Function.comp_def] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (exp 1)] with x hx
  have hL : 0 < log x := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx)
  dsimp only [scale]
  field_simp
  <;> ring

/-- Rounding preserves the leading number of selected primes. -/
private lemma selectedCount_ratio (lambda : ℝ) :
    Tendsto (fun x : ℝ => (selectedCount lambda x : ℝ) / scale x)
      atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ =>
      ((selectedCount lambda x : ℝ) - threshold lambda x) / scale x)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (scale_tendsto.const_div_atTop 1)
    · filter_upwards [selected_error lambda, eventually_gt_atTop (exp 1)] with x he hx
      exact div_nonneg he.1 (scale_pos hx).le
    · filter_upwards [selected_error lambda, eventually_gt_atTop (exp 1)] with x he hx
      exact div_le_div_of_nonneg_right he.2 (scale_pos hx).le
  have h := (threshold_ratio lambda).add he
  simp only [add_zero] at h
  convert h using 1
  ext x
  ring

/-- The precise second-order cancellation needed to keep every selected product below x. -/
private lemma selectedCount_log_cancellation (lambda : ℝ) :
    Tendsto (fun x : ℝ =>
      ((selectedCount lambda x : ℝ) * log (log x) - log x) / scale x)
      atTop (𝓝 lambda) := by
  have he : Tendsto (fun x : ℝ =>
      ((selectedCount lambda x : ℝ) - threshold lambda x) *
        log (log x) / scale x) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ loglog_div_scale
    · filter_upwards [selected_error lambda, eventually_gt_atTop (exp 1)] with x he hx
      have hell : 0 < log (log x) :=
        log_pos ((lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx)
      exact div_nonneg (mul_nonneg he.1 hell.le) (scale_pos hx).le
    · filter_upwards [selected_error lambda, eventually_gt_atTop (exp 1)] with x he hx
      have hell : 0 < log (log x) :=
        log_pos ((lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx)
      exact div_le_div_of_nonneg_right
        (by nlinarith [he.2] :
          ((selectedCount lambda x : ℝ) - threshold lambda x) *
            log (log x) ≤ log (log x)) (scale_pos hx).le
  have h := he.add_const lambda
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (exp 1)] with x hx
  have hL : 0 < log x := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx)
  have hell : 0 < log (log x) :=
    log_pos ((lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx)
  dsimp only [threshold, scale]
  field_simp
  <;> ring

private lemma floor_scaled {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ => (⌊r * scale x⌋₊ : ℝ) / scale x) atTop (𝓝 r) :=
  (tendsto_nat_floor_mul_div_atTop hr).comp scale_tendsto

/-- A distinguished box absorbs all integer rounding errors and the second-order shift. -/
def adjustedSelection {J : Type*} [Fintype J] [DecidableEq J]
    (j0 : J) (r : J → ℝ) (lambda : ℝ) (j : J) (x : ℝ) : ℕ :=
  if j = j0 then
    selectedCount lambda x - ∑ i ∈ Finset.univ.erase j0, ⌊r i * scale x⌋₊
  else ⌊r j * scale x⌋₊

/-- Exact total size and all relative box occupancies survive the rounding adjustment. -/
lemma adjustedSelection_spec {J : Type*} [Fintype J] [DecidableEq J]
    (j0 : J) (r : J → ℝ) (lambda : ℝ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1) :
    (∀ᶠ x : ℝ in atTop, ∑ j, adjustedSelection j0 r lambda j x = selectedCount lambda x) ∧
    ∀ j, Tendsto (fun x : ℝ => (adjustedSelection j0 r lambda j x : ℝ) / scale x)
      atTop (𝓝 (r j)) := by
  let B (x : ℝ) : ℕ := ∑ i ∈ Finset.univ.erase j0, ⌊r i * scale x⌋₊
  have hB : Tendsto (fun x : ℝ => (B x : ℝ) / scale x)
      atTop (𝓝 (1 - r j0)) := by
    have h := tendsto_finset_sum (Finset.univ.erase j0)
      (fun i _ => floor_scaled (hr i))
    have hid : ∑ i ∈ Finset.univ.erase j0, r i = 1 - r j0 := by
      have := Finset.sum_erase_add Finset.univ r (Finset.mem_univ j0)
      rw [hsum] at this
      linarith
    rw [hid] at h
    simpa only [B, Nat.cast_sum, Finset.sum_div] using h
  have hgap : Tendsto (fun x : ℝ =>
      ((selectedCount lambda x : ℝ) - (B x : ℝ)) / scale x)
      atTop (𝓝 (r j0)) := by
    convert (selectedCount_ratio lambda).sub hB using 1 <;> simp [sub_div]
  have hlegal : ∀ᶠ x : ℝ in atTop, B x ≤ selectedCount lambda x := by
    filter_upwards [hgap.eventually_const_lt hr0, eventually_gt_atTop (exp 1)]
      with x hx hxlarge
    have : (B x : ℝ) < (selectedCount lambda x : ℝ) :=
      sub_pos.mp ((div_pos_iff_of_pos_right (scale_pos hxlarge)).mp hx)
    exact_mod_cast this.le
  constructor
  · filter_upwards [hlegal] with x hx
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => adjustedSelection j0 r lambda j x) (Finset.mem_univ j0)]
    have he : ∑ j ∈ Finset.univ.erase j0, adjustedSelection j0 r lambda j x = B x := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [adjustedSelection, if_neg (Finset.ne_of_mem_erase hj)]
    rw [he]
    simp only [adjustedSelection, if_pos rfl]
    exact Nat.add_sub_of_le hx
  · intro j
    by_cases hj : j = j0
    · subst j
      apply hgap.congr'
      filter_upwards [hlegal] with x hx
      simp only [adjustedSelection, if_pos rfl, if_true]
      change ((selectedCount lambda x : ℝ) - (B x : ℝ)) / scale x =
        ((selectedCount lambda x - B x : ℕ) : ℝ) / scale x
      rw [Nat.cast_sub hx]
    · simpa only [adjustedSelection, if_neg hj] using floor_scaled (hr j)

/-- Interior limiting occupancies fit every actual prime capacity eventually. -/
lemma adjustedSelection_fits {J : Type*} [Fintype J] [DecidableEq J]
    (j0 : J) (r d : J → ℝ) (lambda : ℝ) (P : J → ℝ → ℕ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1)
    (hroom : ∀ j, r j < d j)
    (hP : ∀ j, Tendsto (fun x : ℝ => (P j x : ℝ) / scale x) atTop (𝓝 (d j))) :
    ∀ᶠ x : ℝ in atTop, ∀ j, adjustedSelection j0 r lambda j x ≤ P j x := by
  rw [Filter.eventually_all]
  intro j
  have hk := (adjustedSelection_spec j0 r lambda hr hr0 hsum).2 j
  filter_upwards [hk.eventually_lt (hP j) (hroom j), eventually_gt_atTop (exp 1)]
    with x hx hxlarge
  have : (adjustedSelection j0 r lambda j x : ℝ) < P j x :=
    (div_lt_div_iff_of_pos_right (scale_pos hxlarge)).mp hx
  exact_mod_cast this.le

/-- The adjusted selection retains the exact logarithmic cost at second order. -/
private lemma adjustedSelection_cost {J : Type*} [Fintype J] [DecidableEq J]
    (j0 : J) (r b : J → ℝ) (lambda : ℝ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1)
    (hb : ∀ j, 0 < b j) :
    Tendsto (fun x : ℝ =>
      ((∑ j, (adjustedSelection j0 r lambda j x : ℝ) * log (b j * log x)) - log x) /
        scale x) atTop (𝓝 (lambda + ∑ j, r j * log (b j))) := by
  have hk := adjustedSelection_spec j0 r lambda hr hr0 hsum
  have hsumlim := tendsto_finset_sum Finset.univ
    (fun j _ => (hk.2 j).mul_const (log (b j)))
  have h := (selectedCount_log_cancellation lambda).add hsumlim
  apply h.congr'
  filter_upwards [hk.1, eventually_gt_atTop (exp 1)] with x hx hxlarge
  have hL : 0 < log x := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((lt_log_iff_exp_lt (lt_trans (exp_pos _) hxlarge)).mpr hxlarge)
  have hcost : (∑ j, (adjustedSelection j0 r lambda j x : ℝ) * log (b j * log x)) =
      (selectedCount lambda x : ℝ) * log (log x) +
        ∑ j, (adjustedSelection j0 r lambda j x : ℝ) * log (b j) := by
    simp_rw [log_mul (hb _).ne' hL.ne', mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum, hx]
    ring
  rw [hcost]
  simp only [← Finset.sum_div, div_mul_eq_mul_div]
  ring

/-- Strict logarithmic slack makes every adjusted prime product fit below the original cutoff. -/
lemma adjustedSelection_budget {J : Type*} [Fintype J] [DecidableEq J]
    (j0 : J) (r b : J → ℝ) (lambda : ℝ)
    (hr : ∀ j, 0 ≤ r j) (hr0 : 0 < r j0) (hsum : ∑ j, r j = 1)
    (hb : ∀ j, 0 < b j) (hslack : lambda + ∑ j, r j * log (b j) < 0) :
    ∀ᶠ x : ℝ in atTop,
      ∑ j, (adjustedSelection j0 r lambda j x : ℝ) * log (b j * log x) < log x := by
  filter_upwards [(adjustedSelection_cost j0 r b lambda hr hr0 hsum hb).eventually_lt_const
    hslack, eventually_gt_atTop (exp 1)] with x hx hxlarge
  have : (∑ j, (adjustedSelection j0 r lambda j x : ℝ) * log (b j * log x)) - log x < 0 :=
    by simpa using (div_lt_iff₀ (scale_pos hxlarge)).mp hx
  exact sub_neg.mp this

end D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

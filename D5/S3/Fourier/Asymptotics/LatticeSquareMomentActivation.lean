/- GID: D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/LatticeSquareMomentActivation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact support thresholds for the integer-lattice squared-mass minimizer. -/

import D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-! Exact support activation for minimum squared mass under a second-moment budget on ℤ. -/

open Finset

noncomputable section

namespace D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

set_option autoImplicit false

def latticeInterval (n : ℕ) : Finset ℤ :=
  Icc (-(n : ℤ)) (n : ℤ)

private theorem sum_latticeInterval_even (n : ℕ) (f : ℤ → ℝ)
    (hzero : f 0 = 0) (heven : ∀ k, f (-k) = f k) :
    (∑ k ∈ latticeInterval n, f k) = 2 * ∑ j ∈ range (n + 1), f (j : ℤ) := by
  unfold latticeInterval
  rw [Finset.sum_Icc_of_even_eq_range heven, hzero, sub_zero, two_nsmul, two_mul]

theorem card_latticeInterval (n : ℕ) :
    ((latticeInterval n).card : ℝ) = 2 * (n : ℝ) + 1 := by
  have h := Int.card_Icc_of_le (a := -(n : ℤ)) (b := (n : ℤ)) (by omega)
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h'
  unfold latticeInterval
  linarith [h']

private theorem sum_fourth_rat (n : ℕ) :
    (∑ j ∈ range (n + 1), (j : ℚ) ^ 4) =
      (n : ℚ) * (n + 1) * (2 * n + 1) * (3 * (n : ℚ) ^ 2 + 3 * n - 1) / 30 := by
  have h3 : bernoulli 3 = 0 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_three]
  have h4 : bernoulli 4 = -(1 / 30 : ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
    norm_num
  have hc : (5 : ℕ).choose 2 = 10 := by decide
  rw [sum_range_pow]
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two, h3, h4, hc]
  ring

theorem sum_lattice_square (n : ℕ) :
    (∑ k ∈ latticeInterval n, (k : ℝ) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 3 := by
  rw [sum_latticeInterval_even n _ (by simp) (by intro k; push_cast; ring)]
  push_cast
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment.sum_square_rank]
  ring

theorem sum_lattice_fourth (n : ℕ) :
    (∑ k ∈ latticeInterval n, (k : ℝ) ^ 4) =
      (n : ℝ) * (n + 1) * (2 * n + 1) * (3 * (n : ℝ) ^ 2 + 3 * n - 1) / 15 := by
  rw [sum_latticeInterval_even n _ (by simp) (by intro k; push_cast; ring)]
  push_cast
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_fourth_rat n)
  push_cast at h
  rw [h]
  ring

private def normalizer (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ latticeInterval n, (t - (k : ℝ) ^ 2)

private def momentNumerator (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ latticeInterval n, (k : ℝ) ^ 2 * (t - (k : ℝ) ^ 2)

private theorem normalizer_formula (n : ℕ) (t : ℝ) :
    normalizer n t = (2 * (n : ℝ) + 1) * t - (n : ℝ) * (n + 1) * (2 * n + 1) / 3 := by
  rw [normalizer, sum_sub_distrib, sum_const, nsmul_eq_mul, card_latticeInterval,
    sum_lattice_square]

private theorem momentNumerator_formula (n : ℕ) (t : ℝ) :
    momentNumerator n t =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 3 * t -
      (n : ℝ) * (n + 1) * (2 * n + 1) * (3 * (n : ℝ) ^ 2 + 3 * n - 1) / 15 := by
  unfold momentNumerator
  simp_rw [mul_sub, ← pow_add]
  rw [sum_sub_distrib, ← sum_mul, sum_lattice_square, sum_lattice_fourth]
  ring

private theorem lower_moment_difference (n : ℕ) (t : ℝ) :
    momentNumerator n t - (((n : ℝ) ^ 2 - 1) / 5) * normalizer n t =
      (2 * (n : ℝ) + 1) * (n + 1) * (2 * n + 3) / 15 * (t - (n : ℝ) ^ 2) := by
  rw [normalizer_formula, momentNumerator_formula]
  ring

private theorem upper_moment_difference (n : ℕ) (t : ℝ) :
    momentNumerator n t - ((n : ℝ) * (n + 2) / 5) * normalizer n t =
      (2 * (n : ℝ) + 1) * n * (2 * (n : ℝ) - 1) / 15 * (t - ((n : ℝ) + 1) ^ 2) := by
  rw [normalizer_formula, momentNumerator_formula]
  ring

theorem sq_le_iff_mem (k : ℤ) (n : ℕ) :
    (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 ↔ k ∈ latticeInterval n := by
  rw [← sq_abs (k : ℝ), sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _), abs_le,
    latticeInterval, mem_Icc]
  norm_cast

private theorem sq_lt_succ_iff_mem (k : ℤ) (n : ℕ) :
    (k : ℝ) ^ 2 < ((n : ℝ) + 1) ^ 2 ↔ k ∈ latticeInterval n := by
  rw [← sq_abs (k : ℝ), sq_lt_sq₀ (abs_nonneg _) (by positivity), abs_lt,
    latticeInterval, mem_Icc]
  have hl : -((n : ℝ) + 1) < (k : ℝ) ↔ -((n : ℤ) + 1) < k := by exact_mod_cast Iff.rfl
  have hr : (k : ℝ) < (n : ℝ) + 1 ↔ k < (n : ℤ) + 1 := by exact_mod_cast Iff.rfl
  rw [hl, hr]
  omega

private theorem normalizer_pos (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : (n : ℝ) ^ 2 ≤ t) :
    0 < normalizer n t := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hzero : (0 : ℤ) ∈ latticeInterval n := by simp [latticeInterval]
  have hle := single_le_sum
    (s := latticeInterval n) (f := fun k : ℤ => t - (k : ℝ) ^ 2)
    (fun k hk => sub_nonneg.mpr (((sq_le_iff_mem k n).mpr hk).trans ht)) hzero
  have ht' : 0 < t := (pow_pos hn' 2).trans_le ht
  exact ht'.trans_le (show t ≤ normalizer n t from by simpa [normalizer] using hle)

private def weight (t Z : ℝ) (k : ℤ) : ℝ :=
  max 0 (t - (k : ℝ) ^ 2) / Z

private theorem weight_nonneg {t Z : ℝ} (hZ : 0 < Z) (k : ℤ) :
    0 ≤ weight t Z k :=
  div_nonneg (le_max_left _ _) hZ.le

private theorem weight_ne_zero_iff {t Z : ℝ} (hZ : 0 < Z) (k : ℤ) :
    weight t Z k ≠ 0 ↔ (k : ℝ) ^ 2 < t := by
  rw [← (weight_nonneg (t := t) hZ k).lt_iff_ne']
  rw [weight, div_pos_iff_of_pos_right hZ, lt_max_iff]
  simp

private theorem support_weight (n : ℕ) (hn : 0 < n) {t Z : ℝ} (hZ : 0 < Z)
    (ht : (n : ℝ) ^ 2 ≤ t) (ht' : t ≤ ((n : ℝ) + 1) ^ 2) :
    Function.support (weight t Z) =
      if t = (n : ℝ) ^ 2 then (latticeInterval (n - 1) : Set ℤ) else latticeInterval n := by
  ext k
  rw [Function.mem_support, weight_ne_zero_iff hZ]
  split_ifs with he
  · have hpred : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, sub_add_cancel]
    rw [he, ← hpred, sq_lt_succ_iff_mem, Finset.mem_coe]
  · rw [Finset.mem_coe]
    exact ⟨fun hk => (sq_lt_succ_iff_mem k n).mp (hk.trans_le ht'), fun hk =>
      ((sq_le_iff_mem k n).mpr hk).trans_lt (lt_of_le_of_ne ht (Ne.symm he))⟩

private theorem hasSum_weight (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) ^ 2 ≤ t) (ht' : t ≤ ((n : ℝ) + 1) ^ 2)
    (hZ : 0 < normalizer n t) :
    HasSum (weight t (normalizer n t)) 1 ∧
    HasSum (fun k : ℤ => (k : ℝ) ^ 2 * weight t (normalizer n t) k)
      (momentNumerator n t / normalizer n t) := by
  have hzero (k : ℤ) (hk : k ∉ latticeInterval n) : weight t (normalizer n t) k = 0 := by
    by_contra h
    exact hk ((sq_lt_succ_iff_mem k n).mp (((weight_ne_zero_iff hZ k).mp h).trans_le ht'))
  have hinside (k : ℤ) (hk : k ∈ latticeInterval n) :
      weight t (normalizer n t) k = (t - (k : ℝ) ^ 2) / normalizer n t := by
    rw [weight, max_eq_right (sub_nonneg.mpr (((sq_le_iff_mem k n).mpr hk).trans ht))]
  constructor
  · have hs : HasSum (weight t (normalizer n t))
        (∑ k ∈ latticeInterval n, weight t (normalizer n t) k) :=
      hasSum_sum_of_ne_finset_zero hzero
    have he : (∑ k ∈ latticeInterval n, weight t (normalizer n t) k) = 1 := by
      rw [sum_congr rfl hinside, ← sum_div]
      exact div_self hZ.ne'
    rwa [he] at hs
  · have hs : HasSum (fun k : ℤ => (k : ℝ) ^ 2 * weight t (normalizer n t) k)
        (∑ k ∈ latticeInterval n, (k : ℝ) ^ 2 * weight t (normalizer n t) k) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by rw [hzero k hk, mul_zero])
    have he : (∑ k ∈ latticeInterval n, (k : ℝ) ^ 2 * weight t (normalizer n t) k) =
        momentNumerator n t / normalizer n t := by
      rw [momentNumerator, sum_div]
      apply sum_congr rfl
      intro k hk
      rw [hinside k hk, mul_div_assoc]
    rwa [he] at hs

private theorem summable_sq_of_hasSum_one {w : ℤ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hmass : HasSum w 1) : Summable (fun k => w k ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ hmass.summable
  intro k
  have hle : w k ≤ 1 := by
    rw [← hmass.tsum_eq]
    exact hmass.summable.le_tsum k (fun j _ => hw j)
  simpa [pow_two] using mul_le_mul_of_nonneg_left hle (hw k)

private theorem compare_weight {m t Z : ℝ} (hZ : 0 < Z)
    (hvmass : HasSum (weight t Z) 1)
    (hvmoment : HasSum (fun k : ℤ => (k : ℝ) ^ 2 * weight t Z k) m)
    (w : ℤ → ℝ) (q : ℝ) (hw : ∀ k, 0 ≤ w k) (hwmass : HasSum w 1)
    (hwmoment : HasSum (fun k : ℤ => (k : ℝ) ^ 2 * w k) q) :
    Summable (fun k => w k ^ 2) ∧
    Summable (fun k : ℤ => (max 0 ((k : ℝ) ^ 2 - t) / Z) * w k) ∧
    ((∑' k, w k ^ 2) - (∑' k, (weight t Z k) ^ 2) =
      (∑' k, (w k - weight t Z k) ^ 2) + 2 * ((m - q) / Z) +
        2 * (∑' k : ℤ, (max 0 ((k : ℝ) ^ 2 - t) / Z) * w k)) ∧
    (q ≤ m → w ≠ weight t Z → (∑' k, (weight t Z k) ^ 2) < ∑' k, w k ^ 2) := by
  let v := weight t Z
  let a (k : ℤ) := (t - (k : ℝ) ^ 2) / Z
  have hv := weight_nonneg (t := t) hZ
  have hwsq := summable_sq_of_hasSum_one hw hwmass
  have hvsq := summable_sq_of_hasSum_one hv hvmass
  have hdist : Summable (fun k => (w k - v k) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ (hwsq.add hvsq)
    intro k
    nlinarith [mul_nonneg (hw k) (hv k)]
  -- The two moment series make the affine readout summable even off the active support.
  have hdot : HasSum (fun k => a k * (w k - v k)) ((m - q) / Z) := by
    have hmass := (hwmass.sub hvmass).mul_left t
    have hmoment := hwmoment.sub hvmoment
    convert (hmass.sub hmoment).mul_right Z⁻¹ using 1
    · ext k
      dsimp [a, v]
      rw [div_eq_mul_inv]
      ring
    · rw [div_eq_mul_inv]
      ring
  let gap : ℝ := (∑' k, w k ^ 2) - ∑' k, v k ^ 2
  let distance : ℝ := ∑' k, (w k - v k) ^ 2
  let tail (k : ℤ) := (max 0 ((k : ℝ) ^ 2 - t) / Z) * w k
  have htail : HasSum tail ((gap - distance) / 2 - (m - q) / Z) := by
    convert (((hwsq.hasSum.sub hvsq.hasSum).sub hdist.hasSum).div_const 2).sub hdot using 1
    ext k
    change tail k = ((w k ^ 2 - v k ^ 2) - (w k - v k) ^ 2) / 2 - a k * (w k - v k)
    by_cases hk : 0 ≤ t - (k : ℝ) ^ 2
    · have he : v k = a k := by simp [v, a, weight, max_eq_right hk]
      have hneg : (k : ℝ) ^ 2 - t ≤ 0 := by linarith
      simp only [tail, max_eq_left hneg, zero_div, zero_mul, he]
      ring
    · have hk' := le_of_not_ge hk
      have he : v k = 0 := by simp [v, weight, max_eq_left hk']
      have hpos : 0 ≤ (k : ℝ) ^ 2 - t := by linarith
      simp only [tail, a, max_eq_right hpos, he, zero_pow (by decide : 2 ≠ 0), sub_zero]
      ring
  have hgap : gap = distance + 2 * ((m - q) / Z) + 2 * (∑' k, tail k) := by
    rw [htail.tsum_eq]
    ring
  refine ⟨hwsq, htail.summable, hgap, ?_⟩
  intro hq hne
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ v k := Function.ne_iff.mp hne
  have hpos : 0 < ∑' k, (w k - v k) ^ 2 :=
    hdist.tsum_pos (fun j => sq_nonneg _) k (sq_pos_of_ne_zero (sub_ne_zero.mpr hk))
  have hmoment : 0 ≤ (m - q) / Z := div_nonneg (sub_nonneg.mpr hq) hZ.le
  have htail_nonneg : 0 ≤ ∑' k, tail k := tsum_nonneg (fun k =>
    mul_nonneg (div_nonneg (le_max_left ..) hZ.le) (hw k))
  apply sub_pos.mp
  change 0 < gap
  rw [hgap]
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hpos (by positivity)) (by positivity)

private theorem moment_thresholds (n : ℕ) (hn : 0 < n) {t m : ℝ}
    (ht : (n : ℝ) ^ 2 ≤ t) (ht' : t ≤ ((n : ℝ) + 1) ^ 2)
    (hm : momentNumerator n t / normalizer n t = m) :
    ((n : ℝ) ^ 2 - 1) / 5 ≤ m ∧ m ≤ (n : ℝ) * (n + 2) / 5 ∧
    (m = ((n : ℝ) ^ 2 - 1) / 5 ↔ t = (n : ℝ) ^ 2) ∧
    (m = (n : ℝ) * (n + 2) / 5 ↔ t = ((n : ℝ) + 1) ^ 2) := by
  have hZ := normalizer_pos n hn ht
  have hnum := (div_eq_iff hZ.ne').mp hm
  have hlo := lower_moment_difference n t
  have hhi := upper_moment_difference n t
  rw [hnum, ← sub_mul] at hlo hhi
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (2 * (n : ℝ) + 1) * (n + 1) * (2 * n + 3) / 15 := by positivity
  have hb : 0 < (2 * (n : ℝ) + 1) * n * (2 * (n : ℝ) - 1) / 15 := by
    have hb' : 0 < 2 * (n : ℝ) - 1 := by linarith
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sub_nonneg.mp
    apply (mul_nonneg_iff_of_pos_right hZ).mp
    rw [hlo]
    exact mul_nonneg ha.le (sub_nonneg.mpr ht)
  · apply sub_nonpos.mp
    rw [← mul_le_mul_iff_of_pos_right hZ, zero_mul, hhi]
    exact mul_nonpos_of_nonneg_of_nonpos hb.le (sub_nonpos.mpr ht')
  · simpa [mul_eq_zero, hZ.ne', ha.ne', sub_eq_zero] using
      Iff.of_eq (congrArg (fun x : ℝ => x = 0) hlo)
  · simpa [mul_eq_zero, hZ.ne', hb.ne', sub_eq_zero] using
      Iff.of_eq (congrArg (fun x : ℝ => x = 0) hhi)

private theorem exists_radius (n : ℕ) (hn : 0 < n) {m : ℝ}
    (hmlo : ((n : ℝ) ^ 2 - 1) / 5 ≤ m) (hmhi : m ≤ (n : ℝ) * (n + 2) / 5) :
    ∃ t : ℝ, (n : ℝ) ^ 2 ≤ t ∧ t ≤ ((n : ℝ) + 1) ^ 2 ∧
      momentNumerator n t / normalizer n t = m := by
  let lo : ℝ := (n : ℝ) ^ 2
  let hi : ℝ := ((n : ℝ) + 1) ^ 2
  let moment (t : ℝ) := momentNumerator n t / normalizer n t
  have hab : lo ≤ hi := by
    dsimp [lo, hi]
    gcongr
    linarith
  have hcont : ContinuousOn moment (Set.Icc lo hi) := by
    have hnum : Continuous (momentNumerator n) := by
      simp only [funext (momentNumerator_formula n)]
      fun_prop
    have hden : Continuous (normalizer n) := by
      simp only [funext (normalizer_formula n)]
      fun_prop
    exact hnum.continuousOn.div hden.continuousOn
      (fun _ ht => (normalizer_pos n hn ht.1).ne')
  have hlo : moment lo = ((n : ℝ) ^ 2 - 1) / 5 :=
    (moment_thresholds n hn le_rfl hab rfl).2.2.1.mpr rfl
  have hhi : moment hi = (n : ℝ) * (n + 2) / 5 :=
    (moment_thresholds n hn hab le_rfl rfl).2.2.2.mpr rfl
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hcont
    (show m ∈ Set.Icc (moment lo) (moment hi) from ⟨hlo.trans_le hmlo, hmhi.trans_eq hhi.symm⟩)
  exact ⟨t, ht.1, ht.2, he⟩

private theorem weight_eq_single_of_zero (n : ℕ) (hn : 0 < n) {t : ℝ}
    (ht : (n : ℝ) ^ 2 ≤ t) (ht' : t ≤ ((n : ℝ) + 1) ^ 2)
    (hm : momentNumerator n t / normalizer n t = 0)
    (hmass : HasSum (weight t (normalizer n t)) 1) :
    weight t (normalizer n t) = Pi.single 0 1 := by
  obtain ⟨hlo, _, he, _⟩ := moment_thresholds n hn ht ht' hm
  have hle : (n : ℝ) ≤ (1 : ℝ) :=
    (sq_le_sq₀ (Nat.cast_nonneg _) zero_le_one).mp (by linarith)
  have hle' : n ≤ 1 := by exact_mod_cast hle
  have hn1 : n = 1 := by omega
  have ht1 : t = 1 := by simpa [hn1] using he.mp (by norm_num [hn1])
  have hsupp : Function.support (weight t (normalizer n t)) = {0} := by
    simpa [hn1, ht1, latticeInterval] using support_weight n hn (normalizer_pos n hn ht) ht ht'
  have hzero (k : ℤ) (hk : k ≠ 0) : weight t (normalizer n t) k = 0 := by
    by_contra h
    have hmem := Function.mem_support.mpr h
    exact hk (by simpa [hsupp] using hmem)
  have hcenter : weight t (normalizer n t) 0 = 1 :=
    (tsum_eq_single 0 hzero).symm.trans hmass.tsum_eq
  funext k
  by_cases hk : k = 0
  · subst k
    simpa using hcenter
  · simp [Pi.single_eq_of_ne hk, hzero k hk]

/-- The normalized positive-part law on the radius interval indexed by a positive integer.
The support has radius `n - 1` at its lower endpoint and radius `n` throughout the
rest of the interval, including the upper endpoint. -/
structure Activation (m : ℝ) (n : ℕ) (t Z : ℝ) (w : ℤ → ℝ) : Prop where
  radius_lower : (n : ℝ) ^ 2 ≤ t
  radius_upper : t ≤ ((n : ℝ) + 1) ^ 2
  normalizer_pos : 0 < Z
  normalizer_eq : Z = ∑ k ∈ Icc (-(n : ℤ)) (n : ℤ), (t - (k : ℝ) ^ 2)
  law : ∀ k : ℤ, w k = max 0 (t - (k : ℝ) ^ 2) / Z
  nonneg : ∀ k : ℤ, 0 ≤ w k
  mass : HasSum w 1
  second_moment : HasSum (fun k : ℤ => (k : ℝ) ^ 2 * w k) m
  lower_endpoint : m = ((n : ℝ) ^ 2 - 1) / 5 ↔ t = (n : ℝ) ^ 2
  upper_endpoint : m = (n : ℝ) * (n + 2) / 5 ↔ t = ((n : ℝ) + 1) ^ 2
  support : Function.support w =
    if t = (n : ℝ) ^ 2 then (Icc (-((n - 1 : ℕ) : ℤ)) ((n - 1 : ℕ) : ℤ) : Set ℤ)
    else (Icc (-(n : ℤ)) (n : ℤ) : Set ℤ)
  finite_support : (Function.support w).Finite
  at_zero : m = 0 → w = Pi.single 0 1
  comparison : ∀ (v : ℤ → ℝ) (q : ℝ), (∀ k, 0 ≤ v k) → HasSum v 1 →
    HasSum (fun k : ℤ => (k : ℝ) ^ 2 * v k) q →
    Summable (fun k => v k ^ 2) ∧
    Summable (fun k : ℤ => (max 0 ((k : ℝ) ^ 2 - t) / Z) * v k) ∧
    ((∑' k, v k ^ 2) - (∑' k, w k ^ 2) =
      (∑' k, (v k - w k) ^ 2) + 2 * ((m - q) / Z) +
        2 * (∑' k : ℤ, (max 0 ((k : ℝ) ^ 2 - t) / Z) * v k)) ∧
    (q ≤ m → v ≠ w → (∑' k, w k ^ 2) < ∑' k, v k ^ 2)

private theorem activation_parameters_unique {m t Z t' Z' : ℝ} {n n' : ℕ} {w w' : ℤ → ℝ}
    (hn : 0 < n) (hn' : 0 < n')
    (h : Activation m n t Z w) (h' : Activation m n' t' Z' w') :
    (t, Z, w) = (t', Z', w') := by
  have hw : w = w' := by
    by_contra hne
    have hlt := (h.comparison w' m h'.nonneg h'.mass h'.second_moment).2.2.2
      le_rfl (fun he => hne he.symm)
    have hlt' := (h'.comparison w m h.nonneg h.mass h.second_moment).2.2.2 le_rfl hne
    exact lt_asymm hlt hlt'
  subst w'
  have one_le_radius {n : ℕ} {t : ℝ} (hn : 0 < n) (ht : (n : ℝ) ^ 2 ≤ t) :
      1 ≤ t := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [ht, hnR, sq_nonneg ((n : ℝ) - 1)]
  have ht := one_le_radius hn h.radius_lower
  have ht' := one_le_radius hn' h'.radius_lower
  have hzero : t / Z = t' / Z' := by
    have e := (h.law 0).symm.trans (h'.law 0)
    simpa [max_eq_right (zero_le_one.trans ht), max_eq_right (zero_le_one.trans ht')] using e
  have hone : (t - 1) / Z = (t' - 1) / Z' := by
    have e := (h.law 1).symm.trans (h'.law 1)
    simpa [max_eq_right (sub_nonneg.mpr ht), max_eq_right (sub_nonneg.mpr ht')] using e
  have hZ : Z = Z' := by
    have e : Z⁻¹ = Z'⁻¹ := by
      rw [← one_div, ← one_div]
      linarith only [hzero, hone, sub_div t 1 Z, sub_div t' 1 Z']
    simpa using congrArg Inv.inv e
  subst Z'
  have htr : t = t' := (div_left_inj' h.normalizer_pos.ne').mp hzero
  simp [htr]

/-- For every positive index, the attainable budgets on its radius interval are exactly
the closed interval between the two activation thresholds, with unique activation data. -/
theorem exists_lattice_square_moment_minimizer_on_interval (n : ℕ) (hn : 0 < n) (m : ℝ) :
    let lowerBound := fun n : ℕ => ((n : ℝ) ^ 2 - 1) / 5
    (lowerBound n ≤ m ∧ m ≤ (n : ℝ) * (n + 2) / 5) ↔
      ∃! a : ℝ × ℝ × (ℤ → ℝ), Activation m n a.1 a.2.1 a.2.2 := by
  constructor
  · rintro ⟨hmlo, hmhi⟩
    obtain ⟨t, ht, ht', hm⟩ := exists_radius n hn hmlo hmhi
    have hZ := normalizer_pos n hn ht
    obtain ⟨hmass, hmoment⟩ := hasSum_weight n ht ht' hZ
    rw [hm] at hmoment
    obtain ⟨_, _, hlow, hupp⟩ := moment_thresholds n hn ht ht' hm
    have hsupp := support_weight n hn hZ ht ht'
    have hfinite : (Function.support (weight t (normalizer n t))).Finite := by
      rw [hsupp]
      split_ifs <;> exact Finset.finite_toSet _
    have h : Activation m n t (normalizer n t) (weight t (normalizer n t)) := by
      refine ⟨ht, ht', hZ, rfl, fun _ => rfl, weight_nonneg hZ, hmass, hmoment,
        hlow, hupp, hsupp, hfinite, ?_, compare_weight hZ hmass hmoment⟩
      rintro rfl
      exact weight_eq_single_of_zero n hn ht ht' hm hmass
    exact ⟨⟨t, normalizer n t, weight t (normalizer n t)⟩, h,
      fun a ha => activation_parameters_unique hn hn ha h⟩
  · rintro ⟨⟨t, Z, w⟩, h, _⟩
    have hZ : Z = normalizer n t := h.normalizer_eq
    subst Z
    have hw : w = weight t (normalizer n t) := funext h.law
    subst w
    have hs := (hasSum_weight n h.radius_lower h.radius_upper h.normalizer_pos).2
    obtain ⟨hlo, hhi, _, _⟩ :=
      moment_thresholds n hn h.radius_lower h.radius_upper (hs.unique h.second_moment)
    exact ⟨hlo, hhi⟩

/-- Every nonnegative second-moment budget on the integer lattice has unique activation
data on the half-open budget interval, including its index. -/
theorem exists_lattice_square_moment_minimizer (m : ℝ) :
    let lowerBound := fun n : ℕ => ((n : ℝ) ^ 2 - 1) / 5
    0 ≤ m ↔ ∃! a : ℕ × ℝ × ℝ × (ℤ → ℝ), 0 < a.1 ∧
      (lowerBound a.1 ≤ m ∧ m < (a.1 : ℝ) * (a.1 + 2) / 5) ∧
      Activation m a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  refine ⟨?_, ?_⟩
  swap
  · rintro ⟨⟨n, t, Z, w⟩, ⟨_, _, h⟩, _⟩
    rw [← h.second_moment.tsum_eq]
    exact tsum_nonneg (fun k => mul_nonneg (sq_nonneg _) (h.nonneg k))
  intro hm
  let r := Real.sqrt (5 * m + 1)
  let n := ⌊r⌋₊
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 5 * m + 1 := Real.sq_sqrt (by linarith)
  have hle : (n : ℝ) ≤ r := Nat.floor_le hr
  have hlt : r < (n : ℝ) + 1 := Nat.lt_floor_add_one r
  have hn : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    rw [hn0, Nat.cast_zero, zero_add] at hlt
    have hsq := (sq_lt_sq₀ hr zero_le_one).mpr hlt
    linarith
  have hlo := (sq_le_sq₀ (Nat.cast_nonneg n) hr).mpr hle
  have hhi := (sq_lt_sq₀ hr (by positivity)).mpr hlt
  have hmlo : ((n : ℝ) ^ 2 - 1) / 5 ≤ m := by linarith
  have hmhi : m < (n : ℝ) * (n + 2) / 5 := by nlinarith only [hhi, hrsq]
  obtain ⟨⟨t, Z, w⟩, h, _⟩ := (exists_lattice_square_moment_minimizer_on_interval n hn m).mp
    ⟨hmlo, hmhi.le⟩
  refine ⟨⟨n, t, Z, w⟩, ⟨hn, ⟨hmlo, hmhi⟩, h⟩, ?_⟩
  rintro ⟨n', t', Z', w'⟩ ⟨hn', ⟨hmlo', hmhi'⟩, h'⟩
  have interval_order {i j : ℕ} (hij : i < j) :
      (i : ℝ) * (i + 2) / 5 ≤ ((j : ℝ) ^ 2 - 1) / 5 := by
    have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (i : ℝ) + 1) (Nat.cast_nonneg j)).mpr hle
    nlinarith only [hs]
  have heq : n' = n := by
    apply le_antisymm
    · by_contra! hlt'
      exact (hmhi.trans_le ((interval_order hlt').trans hmlo')).false
    · by_contra! hlt'
      exact (hmhi'.trans_le ((interval_order hlt').trans hmlo)).false
  subst n'
  exact congrArg (Prod.mk n) (activation_parameters_unique hn hn h' h)

end D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

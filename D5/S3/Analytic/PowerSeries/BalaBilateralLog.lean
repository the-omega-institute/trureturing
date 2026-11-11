/- GID: D5/S3/Analytic/PowerSeries/BalaBilateralLog
   generality: G
   mirror-B: D5/B/S3/Analytic/PowerSeries/BalaBilateralLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute convergence on the separate unit disks for the bilateral logarithm problem. -/

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! The regular tails and their jointly summable binomial correction. -/

noncomputable section
open Filter Finset
open scoped Topology

namespace D5.S3.Analytic.PowerSeries.BalaBilateralLog

/-- The regular positive tail, indexed from zero. -/
def positive (x a : ℂ) (k : ℕ) : ℂ :=
  (x - a ^ (k + 1)) ^ (k + 1) / (k + 1)

/-- The regular negative tail, including its separately defined value at zero. -/
def negative (x a : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ (k + 2) * a ^ ((k + 1) * (k + 1)) /
    ((k + 1) * (1 - x * a ^ (k + 1)) ^ (k + 1))

/-- Defined from the two source tails, independently of the proposed logarithm value. -/
def regularSum (x a : ℂ) : ℂ := (∑' k, positive x a k) + ∑' k, negative x a k

/-- The raw expression has no parameter at zero and no zero integer index. -/
def raw (x : ℂ) (a : {a : ℂ // a ≠ 0}) (n : {n : ℤ // n ≠ 0}) : ℂ :=
  (x - (a : ℂ) ^ (n : ℤ)) ^ (n : ℤ) / (n : ℤ)

/-- The real source family, also restricted to its ordinary domain. -/
def realRaw (x : ℝ) (a : {a : ℝ // a ≠ 0}) (n : {n : ℤ // n ≠ 0}) : ℝ :=
  (x - (a : ℝ) ^ (n : ℤ)) ^ (n : ℤ) / (n : ℤ)

private theorem disk_product (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1)
    (n : ℕ) : ‖x * a ^ n‖ < 1 := by
  rw [norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg x)
    (pow_le_one₀ (norm_nonneg a) ha.le)) hx

private theorem denominator_ne (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1)
    (n : ℕ) : 1 - x * a ^ n ≠ 0 := by
  intro h
  have he : x * a ^ n = 1 := by linear_combination -h
  have := disk_product x a hx ha n
  simp [he] at this

private theorem envelope_summable (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => (‖x‖ + ‖a‖ ^ n) ^ n) := by
  let r : ℝ := (1 + ‖x‖) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have he : ∀ᶠ n : ℕ in atTop, ‖a‖ ^ n < r - ‖x‖ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg a) ha).eventually
      (eventually_lt_nhds (show (0 : ℝ) < r - ‖x‖ by dsimp [r]; linarith))
  apply (summable_geometric_of_lt_one hr0 hr1).of_norm_bounded_eventually_nat
  filter_upwards [he] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (by linarith) n

private theorem positive_norm_summable (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun k => ‖positive x a k‖) := by
  have he := (summable_nat_add_iff 1).2 (envelope_summable x a hx ha)
  apply he.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  have hk : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)
  simp only [positive, norm_div, norm_pow, hk]
  calc
    ‖x - a ^ (k + 1)‖ ^ (k + 1) / (k + 1) ≤
        ‖x - a ^ (k + 1)‖ ^ (k + 1) :=
      div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    _ ≤ (‖x‖ + ‖a‖ ^ (k + 1)) ^ (k + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) (by simpa using norm_sub_le x (a ^ (k + 1))) _

/-- The triangular coefficients are zero outside their ordinary finite binomial row. -/
private def coefficient (x a : ℂ) (n m : ℕ) : ℂ :=
  if m = 0 then 0 else (-a ^ n) ^ m * x ^ (n - m) * n.choose m / n

private theorem coefficient_support (x a : ℂ) (n m : ℕ) (h : n < m) :
    coefficient x a n m = 0 := by
  simp [coefficient, Nat.choose_eq_zero_of_lt h]

private theorem coefficient_row_norm (x a : ℂ) (n : ℕ) :
    ∑ m ∈ range (n + 1), ‖coefficient x a n m‖ ≤ (‖a‖ ^ n + ‖x‖) ^ n := by
  rw [add_pow]
  apply sum_le_sum
  intro m hm
  by_cases hn : n = 0
  · subst n
    have : m = 0 := by simpa using hm
    subst m
    simp [coefficient]
  by_cases hm0 : m = 0
  · simp [coefficient, hm0]
  simp only [coefficient, if_neg hm0, norm_div, norm_mul, norm_pow, norm_neg,
    Complex.norm_natCast]
  exact div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- Joint absolute summability precedes any interchange of the triangular array. -/
private theorem coefficient_absolute (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun t : ℕ × ℕ => ‖coefficient x a t.1 t.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  have hrow : ∀ n, Summable (fun m => ‖coefficient x a n m‖) := by
    intro n
    apply summable_of_ne_finset_zero (s := range (n + 1))
    intro m hm
    rw [coefficient_support x a n m (by simpa using hm), norm_zero]
  refine ⟨hrow, ?_⟩
  apply (envelope_summable x a hx ha).of_nonneg_of_le
    (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
  intro n
  rw [tsum_eq_sum (s := range (n + 1)) (fun m hm => by
    rw [coefficient_support x a n m (by simpa using hm), norm_zero])]
  simpa [add_comm] using coefficient_row_norm x a n

private theorem coefficient_column_term (x a : ℂ) (j k : ℕ) :
    coefficient x a (j + (k + 1)) (k + 1) =
      -((-1 : ℂ) ^ (k + 2) * a ^ ((k + 1) * (k + 1)) / (k + 1)) *
        ((j + k).choose k * (x * a ^ (k + 1)) ^ j) := by
  have hc : ((j + (k + 1) : ℕ) : ℂ) * ((j + k).choose k : ℂ) =
      ((j + (k + 1)).choose (k + 1) : ℂ) * (k + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq (j + k) k
  have hn : ((j + (k + 1) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : j + (k + 1) ≠ 0)
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  simp only [coefficient, if_neg (by omega : k + 1 ≠ 0), Nat.add_sub_cancel]
  rw [neg_pow, ← pow_mul, mul_pow]
  rw [show (j + (k + 1)) * (k + 1) = (k + 1) * (k + 1) + (k + 1) * j by ring,
    pow_add, pow_add (-1 : ℂ) (k + 1) 1]
  simp only [pow_one, mul_neg_one, neg_neg]
  field_simp [hn, hk]
  linear_combination -(-1 : ℂ) ^ (k + 1) * a ^ ((k + 1) * (k + 1)) *
    x ^ j * a ^ ((k + 1) * j) * hc

private theorem coefficient_column (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1)
    (k : ℕ) : HasSum (fun n => coefficient x a n (k + 1)) (-negative x a k) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k
    (disk_product x a hx ha (k + 1))).mul_left
      (-((-1 : ℂ) ^ (k + 2) * a ^ ((k + 1) * (k + 1)) / (k + 1)))
  have hs : HasSum (fun j => coefficient x a (j + (k + 1)) (k + 1))
      (-negative x a k) := by
    convert h using 1
    · ext j
      exact coefficient_column_term x a j k
    · simp only [negative, div_mul_eq_div_mul_one_div, neg_div, neg_mul]
  have hz : ∑ n ∈ range (k + 1), coefficient x a n (k + 1) = 0 :=
    sum_eq_zero (fun n hn => coefficient_support x a n (k + 1) (by simpa using hn))
  have he := (hasSum_nat_add_iff (k + 1) (f := fun n => coefficient x a n (k + 1))).1 hs
  simpa [hz] using he

private theorem coefficient_row (x a : ℂ) (n : ℕ) :
    ∑' m, coefficient x a n m = (x - a ^ n) ^ n / n - x ^ n / n := by
  rw [tsum_eq_sum (s := range (n + 1)) (fun m hm =>
    coefficient_support x a n m (by simpa using hm))]
  let f : ℕ → ℂ := fun m => (-a ^ n) ^ m * x ^ (n - m) * n.choose m / n
  have hzero : 0 ∈ range (n + 1) := by simp
  have hc : ∑ m ∈ range (n + 1), coefficient x a n m =
      ∑ m ∈ (range (n + 1)).erase 0, f m := by
    rw [← sum_erase_add _ _ hzero]
    simp only [coefficient, ite_true, add_zero]
    apply sum_congr rfl
    intro m hm
    simp only [coefficient, if_neg (ne_of_mem_erase hm)]
    rfl
  have hp : (x - a ^ n) ^ n / n = ∑ m ∈ range (n + 1), f m := by
    rw [show x - a ^ n = -a ^ n + x by ring, add_pow, sum_div]
  rw [hc, hp, ← sum_erase_add _ _ hzero]
  simp [f]

set_option maxHeartbeats 600000 in
private theorem regular_identity (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
    Summable (fun k => ‖positive x a k‖) ∧
    Summable (fun k => ‖negative x a k‖) ∧ regularSum x a = -Complex.log (1 - x) := by
  have hc := (coefficient_absolute x a hx ha).of_norm
  have hcn := coefficient_absolute x a hx ha
  have hneg : Summable (fun k => ‖negative x a k‖) := by
    have hr := hcn.prod_symm
    have hs := hr.prod
    have ht : Summable (fun m => ‖∑' n, coefficient x a n m‖) :=
      hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m =>
        norm_tsum_le_tsum_norm (hr.prod_factor m))
    have ht' := (summable_nat_add_iff 1).2 ht
    exact ht'.congr (fun k => by rw [(coefficient_column x a hx ha k).tsum_eq, norm_neg])
  refine ⟨positive_norm_summable x a hx ha, hneg, ?_⟩
  have hpos : Summable (fun n : ℕ => (x - a ^ n) ^ n / (n : ℂ)) := by
    apply (summable_nat_add_iff 1).1
    refine ((positive_norm_summable x a hx ha).of_norm).congr ?_
    intro n
    simp only [positive, Nat.cast_add, Nat.cast_one]
  have hl := (Complex.hasSum_taylorSeries_neg_log hx).summable
  have hpossum : ∑' n : ℕ, (x - a ^ n) ^ n / (n : ℂ) = ∑' k, positive x a k := by
    simpa [positive] using (hpos.sum_add_tsum_nat_add 1).symm
  have hcolsum : ∑' m, ∑' n, coefficient x a n m = -(∑' k, negative x a k) := by
    have hs : Summable (fun m => ∑' n, coefficient x a n m) := hc.prod_symm.prod
    rw [← hs.sum_add_tsum_nat_add 1]
    have hz : (∑' n, coefficient x a n 0) = 0 := by simp [coefficient]
    rw [show (∑ m ∈ range 1, ∑' n, coefficient x a n m) = 0 by simpa using hz, zero_add]
    calc
      (∑' k, ∑' n, coefficient x a n (k + 1)) = ∑' k, -negative x a k :=
        tsum_congr (fun k => (coefficient_column x a hx ha k).tsum_eq)
      _ = -(∑' k, negative x a k) := tsum_neg
  have hrowsum : ∑' n, ∑' m, coefficient x a n m =
      (∑' k, positive x a k) - -Complex.log (1 - x) := by
    simp_rw [coefficient_row]
    rw [hpos.tsum_sub hl, hpossum, (Complex.hasSum_taylorSeries_neg_log hx).tsum_eq]
  have hcomm : (∑' m, ∑' n, coefficient x a n m) =
      ∑' n, ∑' m, coefficient x a n m := hc.tsum_comm
  rw [hcolsum, hrowsum] at hcomm
  dsimp [regularSum]
  linear_combination -hcomm

private def integerTerm (x : ℂ) (a : {a : ℂ // a ≠ 0}) (n : ℤ) : ℂ :=
  if h : n = 0 then 0 else raw x a ⟨n, h⟩

private theorem integer_positive (x : ℂ) (a : {a : ℂ // a ≠ 0}) (k : ℕ) :
    integerTerm x a (k + 1) = positive x a k := by
  unfold integerTerm
  rw [dif_neg (show (k : ℤ) + 1 ≠ 0 by omega)]
  unfold raw
  dsimp only
  rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by simp]
  rw [zpow_natCast, zpow_natCast, Int.cast_natCast]
  simp only [positive, Nat.cast_add, Nat.cast_one]

private theorem integer_negative (x : ℂ) (a : {a : ℂ // a ≠ 0})
    (k : ℕ) :
    integerTerm x a (-(k + 1)) = negative x a k := by
  have hp : (a : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ a.property
  have hb : x - ((a : ℂ) ^ (k + 1))⁻¹ =
      -(1 - x * (a : ℂ) ^ (k + 1)) / (a : ℂ) ^ (k + 1) := by
    field_simp
    ring
  unfold integerTerm
  rw [dif_neg (by omega : -(k + 1 : ℤ) ≠ 0)]
  unfold raw
  dsimp only
  rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by simp]
  simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast]
  rw [← inv_pow, hb, inv_div]
  simp only [div_neg]
  rw [neg_pow, div_pow]
  simp only [negative, div_mul_eq_div_mul_one_div, pow_succ (-1 : ℂ) (k + 1),
    mul_neg_one, neg_div, ← pow_mul, Nat.cast_add, Nat.cast_one]
  ring

private theorem bilateral (x : ℂ) (a : {a : ℂ // a ≠ 0})
    (hx : ‖x‖ < 1) (ha : ‖(a : ℂ)‖ < 1) :
    Summable (fun n => ‖raw x a n‖) ∧ HasSum (raw x a) (regularSum x a) ∧
      Tendsto (fun N : ℕ => ∑ k ∈ range N, (positive x a k + negative x a k))
        atTop (𝓝 (regularSum x a)) := by
  obtain ⟨hp, hq, hv⟩ := regular_identity x a hx ha
  have hip : Summable (fun k : ℕ => ‖integerTerm x a (k + 1)‖) := by
    simpa only [integer_positive] using hp
  have hiq : Summable (fun k : ℕ => ‖integerTerm x a (-(k + 1))‖) := by
    simpa only [integer_negative] using hq
  have habs : Summable (fun n : ℤ => ‖integerTerm x a n‖) :=
    Summable.of_add_one_of_neg_add_one (f := fun n : ℤ => ‖integerTerm x a n‖) hip hiq
  have hraw : Summable (fun n => ‖raw x a n‖) := by
    convert habs.subtype (fun n : ℤ => n ≠ 0) using 1
    ext n
    simp [integerTerm, n.property]
  have hiv : HasSum (integerTerm x a) (regularSum x a) := by
    have hpp : HasSum (fun k : ℕ => integerTerm x a (k + 1)) (∑' k, positive x a k) := by
      simpa only [integer_positive] using hp.of_norm.hasSum
    have hqq : HasSum (fun k : ℕ => integerTerm x a (-(k + 1))) (∑' k, negative x a k) := by
      simpa only [integer_negative] using hq.of_norm.hasSum
    have hz : integerTerm x a 0 = 0 := by simp [integerTerm]
    simpa only [hz, add_zero, regularSum] using
      (HasSum.of_add_one_of_neg_add_one (f := integerTerm x a) hpp hqq)
  have hsupport : Function.support (integerTerm x a) ⊆ {n : ℤ | n ≠ 0} := by
    intro n hn
    by_contra h
    simp only [Set.mem_setOf_eq, not_not] at h
    subst n
    simp [integerTerm, Function.mem_support] at hn
  have hsraw : HasSum (raw x a) (regularSum x a) := by
    have h : HasSum (fun n : {n : ℤ // n ≠ 0} => integerTerm x a n)
        (regularSum x a) := (hasSum_subtype_iff_of_support_subset hsupport).2 hiv
    apply h.congr
    intro s
    apply sum_congr rfl
    intro n hn
    simp [integerTerm, n.property]
  refine ⟨hraw, hsraw, ?_⟩
  exact (hp.of_norm.hasSum.add hq.of_norm.hasSum).tendsto_sum_nat

private theorem regular_continuous_zero (x : ℂ) (hx : ‖x‖ < 1) :
    ContinuousAt (regularSum x) 0 := by
  have hc : ContinuousAt (fun _ : ℂ => -Complex.log (1 - x)) 0 := continuousAt_const
  apply hc.congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with a ha
  have ha' : ‖a‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using ha
  exact (regular_identity x a hx ha').2.2.symm

private theorem extension_unique (x : ℂ) (hx : ‖x‖ < 1) (H : ℂ → ℂ)
    (hH : ContinuousWithinAt H {a | ‖a‖ < 1} 0)
    (hraw : ∀ (a : {a : ℂ // a ≠ 0}), ‖(a : ℂ)‖ < 1 →
      H a = ∑' n, raw x a n) :
    Set.EqOn H (regularSum x) {a | ‖a‖ < 1} := by
  have hH' : ContinuousAt H 0 := hH.continuousAt (by
    simpa [Metric.ball, dist_zero_right] using
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
  have he : H =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => -Complex.log (1 - x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))] with a ha hnorm
    have hne : a ≠ 0 := by simpa using ha
    have hna : ‖a‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hnorm
    rw [hraw ⟨a, hne⟩ hna, (bilateral x ⟨a, hne⟩ hx hna).2.1.tsum_eq]
    exact (regular_identity x a hx hna).2.2
  have hzero : H 0 = -Complex.log (1 - x) :=
    tendsto_nhds_unique_of_eventuallyEq (hH'.mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds he
  intro a ha
  by_cases hne : a = 0
  · subst a
    rw [hzero, (regular_identity x 0 hx (by simp)).2.2]
  · rw [hraw ⟨a, hne⟩ ha, (bilateral x ⟨a, hne⟩ hx ha).2.1.tsum_eq]

private theorem raw_field (x : ℂ) (a : {a : ℂ // a ≠ 0})
    (hx : ‖x‖ < 1) (ha : ‖(a : ℂ)‖ < 1) (n : {n : ℤ // n ≠ 0}) :
    (a : ℂ) ^ (n : ℤ) ≠ 0 ∧ ((n : ℤ) : ℂ) ≠ 0 ∧
      ((n : ℤ) < 0 → x - (a : ℂ) ^ (n : ℤ) ≠ 0) := by
  refine ⟨zpow_ne_zero _ a.property, by exact_mod_cast n.property, ?_⟩
  intro hn
  rcases n with ⟨n, hn0⟩
  cases n with
  | ofNat k =>
    change (k : ℤ) < 0 at hn
    omega
  | negSucc k =>
    have hp : (a : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ a.property
    have hb : x - ((a : ℂ) ^ (k + 1))⁻¹ =
        -(1 - x * (a : ℂ) ^ (k + 1)) / (a : ℂ) ^ (k + 1) := by
      field_simp
      ring
    change x - (a : ℂ) ^ (-((k + 1 : ℕ) : ℤ)) ≠ 0
    rw [zpow_neg, zpow_natCast, hb]
    exact div_ne_zero (neg_ne_zero.mpr (denominator_ne x a hx ha (k + 1))) hp

private theorem real_correspondence (x : ℝ) (a : {a : ℝ // a ≠ 0})
    (hx : |x| < 1) (ha : |(a : ℝ)| < 1) :
    Summable (fun n => ‖realRaw x a n‖) ∧ HasSum (realRaw x a) (-Real.log (1 - x)) := by
  let ac : {a : ℂ // a ≠ 0} := ⟨((a : ℝ) : ℂ), by exact_mod_cast a.property⟩
  have hxc : ‖(x : ℂ)‖ < 1 := by simpa using hx
  have hac : ‖(ac : ℂ)‖ < 1 := by simpa [ac] using ha
  have he (n : {n : ℤ // n ≠ 0}) : (realRaw x a n : ℂ) = raw x ac n := by
    simp [realRaw, raw, ac]
  have hpos : 0 ≤ 1 - x := by have := (abs_lt.mp hx).2; linarith
  have hv : regularSum (x : ℂ) ac = ((-Real.log (1 - x) : ℝ) : ℂ) := by
    rw [(regular_identity (x : ℂ) ac hxc hac).2.2]
    simpa only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one] using
      congrArg Neg.neg (Complex.ofReal_log hpos).symm
  obtain ⟨hs, hh, _⟩ := bilateral (x : ℂ) ac hxc hac
  refine ⟨hs.congr (fun n => ?_), Complex.hasSum_ofReal.1 ?_⟩
  · rw [← he]
    simp
  · simpa only [he, hv] using hh

/-- The complete separate-disk event, including the ordinary real source domain. -/
theorem full_event :
    (∀ x a : ℂ, ‖x‖ < 1 → ‖a‖ < 1 →
      Summable (fun k => ‖positive x a k‖) ∧
      Summable (fun k => ‖negative x a k‖) ∧
      regularSum x a = -Complex.log (1 - x) ∧
      (∀ k : ℕ, (k : ℂ) + 1 ≠ 0 ∧ 1 - x * a ^ (k + 1) ≠ 0) ∧
      (0 < (1 - x).re)) ∧
    (∀ (x : ℂ) (a : {a : ℂ // a ≠ 0}), ‖x‖ < 1 → ‖(a : ℂ)‖ < 1 →
      (∀ n : {n : ℤ // n ≠ 0}, (a : ℂ) ^ (n : ℤ) ≠ 0 ∧
        ((n : ℤ) : ℂ) ≠ 0 ∧ ((n : ℤ) < 0 → x - (a : ℂ) ^ (n : ℤ) ≠ 0)) ∧
      (∀ k : ℕ,
        raw x a ⟨(k : ℤ) + 1, by omega⟩ = positive x a k ∧
        raw x a ⟨-((k : ℤ) + 1), by omega⟩ = negative x a k) ∧
      Summable (fun n => ‖raw x a n‖) ∧ HasSum (raw x a) (regularSum x a) ∧
      (∑' n, raw x a n) = regularSum x a ∧
      ((∑' k : ℕ, raw x a ⟨(k : ℤ) + 1, by omega⟩) +
        ∑' k : ℕ, raw x a ⟨-((k : ℤ) + 1), by omega⟩) = regularSum x a ∧
      Tendsto (fun N : ℕ => ∑ k ∈ range N,
        (raw x a ⟨(k : ℤ) + 1, by omega⟩ +
          raw x a ⟨-((k : ℤ) + 1), by omega⟩)) atTop (𝓝 (regularSum x a))) ∧
    (∀ (x : ℝ) (a : {a : ℝ // a ≠ 0}), |x| < 1 → |(a : ℝ)| < 1 →
      Summable (fun n => ‖realRaw x a n‖) ∧ HasSum (realRaw x a) (-Real.log (1 - x))) ∧
    (∀ x : ℂ, ‖x‖ < 1 →
      (∀ k : ℕ, positive x 0 k = x ^ (k + 1) / (k + 1) ∧ negative x 0 k = 0) ∧
      ContinuousAt (regularSum x) 0 ∧
      ∀ H : ℂ → ℂ, ContinuousWithinAt H {a | ‖a‖ < 1} 0 →
        (∀ a : {a : ℂ // a ≠ 0}, ‖(a : ℂ)‖ < 1 → H a = ∑' n, raw x a n) →
          Set.EqOn H (regularSum x) {a | ‖a‖ < 1}) := by
  refine ⟨?_, ?_, real_correspondence, ?_⟩
  · intro x a hx ha
    obtain ⟨hp, hq, hv⟩ := regular_identity x a hx ha
    refine ⟨hp, hq, hv, fun k => ⟨by exact_mod_cast (by omega : k + 1 ≠ 0),
      denominator_ne x a hx ha (k + 1)⟩, ?_⟩
    have hr := Complex.re_le_norm x
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · intro x a hx ha
    obtain ⟨hs, hh, ht⟩ := bilateral x a hx ha
    have hc (k : ℕ) :
        raw x a ⟨(k : ℤ) + 1, by omega⟩ = positive x a k ∧
        raw x a ⟨-((k : ℤ) + 1), by omega⟩ = negative x a k := by
      constructor
      · simpa only [integerTerm, dif_neg (by omega : (k : ℤ) + 1 ≠ 0)] using
          integer_positive x a k
      · simpa only [integerTerm, dif_neg (by omega : -((k : ℤ) + 1) ≠ 0)] using
          integer_negative x a k
    refine ⟨raw_field x a hx ha, hc, hs, hh, hh.tsum_eq, ?_, ?_⟩
    · rw [tsum_congr (fun k => (hc k).1), tsum_congr (fun k => (hc k).2)]
      rfl
    · convert ht using 1
      ext N
      exact sum_congr rfl (fun k _ => by rw [(hc k).1, (hc k).2])
  · intro x hx
    refine ⟨?_, regular_continuous_zero x hx, extension_unique x hx⟩
    intro k
    simp [positive, negative, Nat.mul_eq_zero]

#print axioms full_event




end D5.S3.Analytic.PowerSeries.BalaBilateralLog

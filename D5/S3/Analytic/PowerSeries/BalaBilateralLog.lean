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
def regularSum (x a : ℂ) : ℂ := ∑' k, positive x a k + ∑' k, negative x a k

/-- The raw expression has no parameter at zero and no zero integer index. -/
def raw (x : ℂ) (a : {a : ℂ // a ≠ 0}) (n : {n : ℤ // n ≠ 0}) : ℂ :=
  (x - (a : ℂ) ^ (n : ℤ)) ^ (n : ℤ) / (n : ℤ)

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
  simp only [positive, norm_div, norm_pow, Complex.norm_natCast]
  calc
    ‖x - a ^ (k + 1)‖ ^ (k + 1) / (k + 1) ≤
        ‖x - a ^ (k + 1)‖ ^ (k + 1) :=
      div_le_self (by positivity) (by positivity)
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
  · simp [coefficient, hm0]; positivity
  simp only [coefficient, if_neg hm0, norm_div, norm_mul, norm_pow, norm_neg,
    Complex.norm_natCast]
  exact div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- Joint absolute summability precedes any interchange of the triangular array. -/
theorem coefficient_absolute (x a : ℂ) (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
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

end D5.S3.Analytic.PowerSeries.BalaBilateralLog

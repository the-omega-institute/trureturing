/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative recurrences for the actual strict nested source series. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionDisk
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators NNReal Topology

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionRecurrences

open CompositionDisk

/-- The exponent-zero version is the derivative series for a leading one. -/
def derivativeSeries (s : ℕ) (tail : List ℕ+) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((H tail n / ((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) * z ^ n

/-- Termwise differentiation of the defining source series on every smaller disk. -/
theorem source_derivative (head : ℕ+) (tail : List ℕ+) (z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (source (head :: tail)) (derivativeSeries ((head : ℕ) - 1) tail z) z := by
  let a : ℕ → ℕ → ℂ := fun s n =>
    ((H tail n / ((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ)
  have ha : ∀ s n, ‖a s n‖ ≤ (n : ℝ) ^ tail.length := by
    intro s n
    have hn := (source_coefficient_control tail n).1
    have hd : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ s :=
      one_le_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (by positivity))]
    exact (div_le_self hn hd).trans (source_coefficient_control tail n).2.1
  obtain ⟨r, hzr, hr1⟩ := exists_between hz
  have hr0 : 0 < r := (norm_nonneg z).trans_lt hzr
  have hmajor : Summable (fun n : ℕ => (n : ℝ) ^ tail.length * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one _ (by
      simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1)
  have hterm : ∀ n (w : ℂ), HasDerivAt
      (fun x : ℂ => a head n * x ^ (n + 1))
      (a ((head : ℕ) - 1) n * w ^ n) w := by
    intro n w
    convert! (hasDerivAt_pow (n + 1) w).const_mul (a head n) using 1
    simp only [Nat.add_sub_cancel]
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have he : (head : ℕ) = (head : ℕ) - 1 + 1 := (Nat.sub_add_cancel head.pos).symm
    dsimp [a]
    push_cast
    conv_rhs => rw [he, pow_succ]
    field_simp [hn]
  have hbound : ∀ n w, w ∈ Metric.ball (0 : ℂ) r →
      ‖a ((head : ℕ) - 1) n * w ^ n‖ ≤ (n : ℝ) ^ tail.length * r ^ n := by
    intro n w hw
    have hw' : ‖w‖ < r := by simpa using hw
    rw [norm_mul, norm_pow]
    exact mul_le_mul (ha _ n) (pow_le_pow_left₀ (norm_nonneg _) hw'.le _)
      (pow_nonneg (norm_nonneg _) _) (by positivity)
  have hzero : Summable (fun n : ℕ => a head n * (0 : ℂ) ^ (n + 1)) := by simp
  exact hasDerivAt_tsum_of_isPreconnected hmajor Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected (fun n w _ => hterm n w) hbound
    (by simpa using hr0) hzero (by simpa using hzr)

/-- Both source recurrences, with the derivative's actual value at the origin. -/
theorem source_recurrences :
    (∀ (tail : List ℕ+) (z : ℂ), ‖z‖ < 1 →
      deriv (source (1 :: tail)) z = source tail z / (1 - z)) ∧
    (∀ (head : ℕ+) (tail : List ℕ+) (hh : 1 < (head : ℕ)) (z : ℂ), ‖z‖ < 1 →
      deriv (source (head :: tail)) z =
        if z = 0 then (if tail = [] then 1 else 0)
        else source (⟨(head : ℕ) - 1, by omega⟩ :: tail) z / z) := by
  have hs : ∀ (tail : List ℕ+) (z : ℂ), ‖z‖ < 1 →
      Summable (fun n : ℕ => (H tail n : ℂ) * z ^ n) := by
    intro tail z hz
    apply Summable.of_norm_bounded
      (summable_pow_mul_geometric_of_norm_lt_one tail.length
        (show ‖(‖z‖ : ℝ)‖ < 1 by simpa using hz))
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (source_coefficient_control tail n).1]
    exact mul_le_mul_of_nonneg_right (source_coefficient_control tail n).2.1
      (pow_nonneg (norm_nonneg _) _)
  constructor
  · intro tail z hz
    rw [(source_derivative 1 tail z hz).deriv]
    simp only [PNat.val_ofNat, Nat.sub_self, derivativeSeries, pow_zero, div_one]
    have hne : 1 - z ≠ 0 := by
      intro h
      have : z = 1 := (sub_eq_zero.mp h).symm
      simp [this] at hz
    apply (eq_div_iff hne).mpr
    cases tail with
    | nil => simp [H, source, tsum_geometric_of_norm_lt_one hz, hne]
    | cons k ks =>
      let b : ℕ → ℂ := fun n => (H (k :: ks) n : ℂ) * z ^ n
      have hb : Summable b := hs (k :: ks) z hz
      have hb1 : Summable (fun n => b (n + 1)) := (summable_nat_add_iff 1).mpr hb
      have hbz : Summable (fun n => (H (k :: ks) n : ℂ) * z ^ (n + 1)) := by
        simpa only [b, pow_succ, mul_assoc] using hb.mul_right z
      have hshift : (∑' n, b (n + 1)) = ∑' n, b n := by
        have he := hb.tsum_eq_zero_add
        simpa [b, H] using he.symm
      have hdiff : ∀ n, b (n + 1) - (H (k :: ks) n : ℂ) * z ^ (n + 1) =
          ((H ks n / ((n + 1 : ℕ) : ℝ) ^ (k : ℕ) : ℝ) : ℂ) * z ^ (n + 1) := by
        intro n
        simp only [b, H, Finset.sum_range_succ, Complex.ofReal_add]
        ring
      calc
        (∑' n, (H (k :: ks) n : ℂ) * z ^ n) * (1 - z) =
            (∑' n, b (n + 1)) - ∑' n, (H (k :: ks) n : ℂ) * z ^ (n + 1) := by
          rw [hshift]
          simp only [b, pow_succ, ← mul_assoc, tsum_mul_right]
          ring
        _ = ∑' n, (b (n + 1) - (H (k :: ks) n : ℂ) * z ^ (n + 1)) :=
          (hb1.tsum_sub hbz).symm
        _ = source (k :: ks) z := tsum_congr hdiff
  · intro head tail hh z hz
    rw [(source_derivative head tail z hz).deriv]
    by_cases hzero : z = 0
    · subst z
      rw [if_pos rfl]
      unfold derivativeSeries
      rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
      cases tail <;> simp [H]
    · rw [if_neg hzero]
      apply (eq_div_iff hzero).mpr
      unfold derivativeSeries source
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      simp only [pow_succ, mul_assoc]
      rfl

#print axioms source_derivative
#print axioms source_recurrences

end D5.S3.AnalyticClosure.Polylogarithm.CompositionRecurrences

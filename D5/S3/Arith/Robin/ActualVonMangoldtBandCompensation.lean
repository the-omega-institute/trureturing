/- GID: D5/S3/Arith/Robin/ActualVonMangoldtBandCompensation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualVonMangoldtBandCompensation
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual finite von Mangoldt bands retain the cutoff atoms in the centered max-kernel response. -/

import D5.S3.Arith.Robin.QuotientIntegralBudget
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Interval ArithmeticFunction

namespace D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation

open QuotientIntegralBudget (arithmeticPrefix prefix_as_finite_sum prefix_difference_finite)

def maxKernel (A t : ℝ) : ℝ := 1 / (max A t * Real.log (max A t))

def dilatedKernel (A c t : ℝ) : ℝ := c⁻¹ * maxKernel A (t / c)

def tangentKernel (A t : ℝ) : ℝ :=
  if t ≤ A then -(1 / (A * Real.log A)) else 1 / (t * (Real.log t) ^ 2)

def centeredKernel (A c t : ℝ) : ℝ :=
  dilatedKernel A c t - maxKernel A t - (c - 1) * tangentKernel A t

def plateau (A c : ℝ) : ℝ := (c - 1) ^ 2 / (c * A * Real.log A)

def smoothRemainder (c t : ℝ) : ℝ :=
  1 / (t * (Real.log t - Real.log c)) - 1 / (t * Real.log t) -
    (c - 1) / (t * (Real.log t) ^ 2)

def regularKernel (A c t : ℝ) : ℝ :=
  if t ≤ A then plateau A c else smoothRemainder c t

def residualKernel (A c t : ℝ) : ℝ := regularKernel A c t - centeredKernel A c t

def reciprocalLog (c t : ℝ) : ℝ := 1 / (t * Real.log (t / c))

def bandDerivative (c t : ℝ) : ℝ :=
  (Real.log (t / c) + 1) / (t ^ 2 * (Real.log (t / c)) ^ 2)

def bandLow (A c : ℝ) : ℝ := min A (c * A)
def bandHigh (A c : ℝ) : ℝ := max A (c * A)

/-- Literal right-closed finite arithmetic sum; no continuous replacement of Λ. -/
def weightedPrefix (f : ℝ → ℝ) (R : ℝ) : ℝ :=
  arithmeticPrefix (fun n => Λ n * f n) R

def actualCompensation (A c : ℝ) : ℝ := weightedPrefix (residualKernel A c) (bandHigh A c)

/-- The literal Lebesgue volume of the compact residual. -/
def bandVolume (A c : ℝ) : ℝ := ∫ t in (0 : ℝ)..bandHigh A c, residualKernel A c t

def discrepancy (t : ℝ) : ℝ := Chebyshev.psi t - t

def finiteResponse (A c R : ℝ) : ℝ :=
  weightedPrefix (centeredKernel A c) R - ∫ t in (0 : ℝ)..R, centeredKernel A c t

def smoothBoundary (A c R : ℝ) : ℝ :=
  (plateau A c - smoothRemainder c A) * discrepancy A +
    smoothRemainder c R * discrepancy R -
      ∫ t in A..R, discrepancy t * deriv (smoothRemainder c) t

def shortAllowance (A c H : ℝ) : ℝ :=
  (517 / 1000 : ℝ) * min (H ^ 2) (A ^ 2 * (c - 1) ^ 2) / (A ^ 2 * Real.log A)

def ThetaIncrementLower (X H ε : ℝ) : Prop :=
  ∀ u v : ℝ, X ≤ u → u < v → v ≤ 2 * X → H ≤ v - u →
    (1 - ε) * (v - u) ≤ Chebyshev.theta v - Chebyshev.theta u

private theorem prefix_eq_Ioc (k : ℕ → ℝ) (y : ℝ) :
    arithmeticPrefix k y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, k n := by
  calc
    arithmeticPrefix k y = ∑ i ∈ Finset.range ⌊y⌋₊, k (1 + i) := by
      simp only [arithmeticPrefix, Nat.add_comm]
    _ = ∑ n ∈ Finset.Ico 1 (⌊y⌋₊ + 1), k n := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    _ = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, k n := by
      congr 1

private theorem prefix_psi (t : ℝ) : arithmeticPrefix (fun n => Λ n) t = Chebyshev.psi t := by
  exact prefix_eq_Ioc _ _

private theorem theta_increment_le_psi {u v : ℝ} (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u ≤ Chebyshev.psi v - Chebyshev.psi u := by
  have h : Chebyshev.psi u - Chebyshev.theta u ≤ Chebyshev.psi v - Chebyshev.theta v := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.psi_sub_theta_eq_sum_not_prime]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono huv)⟩, hn.2⟩
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  linarith

private theorem actual_increment {u v : ℝ} {N : ℕ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvN : v ≤ N) (hv : 0 < v) :
    Chebyshev.psi v - Chebyshev.psi u =
      ∑ i ∈ Finset.range N, if u < ((i + 1 : ℕ) : ℝ) ∧ ((i + 1 : ℕ) : ℝ) ≤ v
        then Λ (i + 1) else 0 := by
  have h := prefix_difference_finite (fun n => Λ n) (N := N) (c := u / v) (y := v)
    hv.le (by simpa [div_mul_cancel₀ _ hv.ne'] using hu)
    (by simpa [div_mul_cancel₀ _ hv.ne'] using huv) hvN
  simpa only [div_mul_cancel₀ _ hv.ne', prefix_psi] using h

private theorem reciprocalLog_deriv {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hz : Real.log (t / c) ≠ 0) :
    HasDerivAt (reciprocalLog c) (-bandDerivative c t) t := by
  have hl := (Real.hasDerivAt_log (div_ne_zero ht.ne' hc.ne')).comp t
    ((hasDerivAt_id t).div_const c)
  have h := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).mul hl)
    (mul_ne_zero ht.ne' hz)
  change HasDerivAt (reciprocalLog c) _ t at h
  apply h.congr_deriv
  simp only [bandDerivative, id_eq, Pi.mul_apply, Pi.div_apply, Function.comp_apply,
    one_mul, zero_mul, zero_sub]
  field_simp [hc.ne', ht.ne', hz]
  <;> ring

private theorem maxKernel_low {A t : ℝ} (ht : t ≤ A) :
    maxKernel A t = 1 / (A * Real.log A) := by
  rw [maxKernel, max_eq_left ht]

private theorem maxKernel_high {A t : ℝ} (ht : A ≤ t) :
    maxKernel A t = 1 / (t * Real.log t) := by
  rw [maxKernel, max_eq_right ht]

private theorem dilatedKernel_low {A c t : ℝ} (hc : 0 < c) (ht : t ≤ c * A) :
    dilatedKernel A c t = 1 / (c * A * Real.log A) := by
  rw [dilatedKernel, maxKernel_low ((div_le_iff₀ hc).mpr (by simpa [mul_comm] using ht))]
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private theorem dilatedKernel_high {A c t : ℝ} (hc : 0 < c) (ht : c * A ≤ t) :
    dilatedKernel A c t = reciprocalLog c t := by
  rw [dilatedKernel, maxKernel_high ((le_div_iff₀ hc).mpr (by simpa [mul_comm] using ht))]
  unfold reciprocalLog
  simp [div_eq_mul_inv, mul_inv_rev, hc.ne', mul_assoc, mul_comm, mul_left_comm]

private theorem reciprocalLog_cutoff {A c : ℝ} (hc : 0 < c) :
    reciprocalLog c (c * A) = 1 / (c * A * Real.log A) := by
  simp [reciprocalLog, mul_div_cancel_left₀ _ hc.ne']

private theorem residual_low {A c t : ℝ} (ha : 1 < A) (hc : 0 < c)
    (htA : t ≤ A) (htc : t ≤ c * A) : residualKernel A c t = 0 := by
  simp only [residualKernel, regularKernel, if_pos htA, centeredKernel, tangentKernel,
    dilatedKernel_low hc htc, maxKernel_low htA, plateau]
  have hl := (Real.log_pos ha).ne'
  field_simp [hc.ne', (lt_trans zero_lt_one ha).ne', hl]
  <;> ring

private theorem residual_high {A c t : ℝ} (ha : 0 < A) (hc : 0 < c)
    (htA : A < t) (htc : c * A ≤ t) : residualKernel A c t = 0 := by
  have ht : 0 < t := ha.trans htA
  simp only [residualKernel, regularKernel, if_neg (not_le.mpr htA), centeredKernel,
    tangentKernel, dilatedKernel_high hc htc, maxKernel_high htA.le, smoothRemainder,
    reciprocalLog, Real.log_div ht.ne' hc.ne']
  ring

private theorem residual_forward {A c t : ℝ} (ha : 1 < A) (hc : 1 ≤ c) :
    residualKernel A c t =
      if A < t ∧ t ≤ c * A then reciprocalLog c t - reciprocalLog c (c * A) else 0 := by
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hAA : A ≤ c * A := by nlinarith
  by_cases ht : t ≤ A
  · rw [if_neg (by intro h; linarith [h.1])]
    exact residual_low ha hc0 ht (ht.trans hAA)
  · have htA : A < t := lt_of_not_ge ht
    by_cases htc : t ≤ c * A
    · rw [if_pos ⟨htA, htc⟩, reciprocalLog_cutoff hc0]
      simp only [residualKernel, regularKernel, if_neg ht, centeredKernel, tangentKernel,
        dilatedKernel_low hc0 htc, maxKernel_high htA.le, smoothRemainder,
        reciprocalLog_cutoff hc0, reciprocalLog, Real.log_div (ha0.trans htA).ne' hc0.ne']
      ring
    · rw [if_neg (by intro h; exact htc h.2)]
      exact residual_high ha0 hc0 htA (le_of_lt (lt_of_not_ge htc))

private theorem residual_reverse {A c t : ℝ} (ha : 1 < A) (hc : 0 < c) (hc1 : c ≤ 1) :
    residualKernel A c t =
      if c * A < t ∧ t ≤ A then reciprocalLog c (c * A) - reciprocalLog c t else 0 := by
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hcAA : c * A ≤ A := by nlinarith
  by_cases ht : t ≤ c * A
  · rw [if_neg (by intro h; linarith [h.1])]
    exact residual_low ha hc (ht.trans hcAA) ht
  · have hct : c * A < t := lt_of_not_ge ht
    by_cases htA : t ≤ A
    · rw [if_pos ⟨hct, htA⟩]
      simp only [residualKernel, regularKernel, if_pos htA, centeredKernel, tangentKernel,
        dilatedKernel_high hc hct.le, maxKernel_low htA, plateau, reciprocalLog_cutoff hc]
      have hl := (Real.log_pos ha).ne'
      field_simp [hc.ne', ha0.ne', hl]
      <;> ring
    · rw [if_neg (by intro h; exact htA h.2)]
      exact residual_high ha0 hc (lt_of_not_ge htA) (hcAA.trans (le_of_lt (lt_of_not_ge htA)))

private theorem band_scale {A c : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) :
    1 < A ∧ 0 < c ∧ 78 ≤ Real.log A ∧
      ∀ t ∈ Icc (bandLow A c) (bandHigh A c),
        (99 / 100 : ℝ) * A ≤ t ∧ Real.log A - 1 / 100 ≤ Real.log (t / c) := by
  have he : (1 : ℝ) < Real.exp 78 := Real.one_lt_exp_iff.mpr (by norm_num)
  have ha : 1 < A := he.trans_le hA
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hc0 : 0 < c := by linarith
  have hl : 78 ≤ Real.log A := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 78) hA
  refine ⟨ha, hc0, hl, ?_⟩
  intro t ht
  have htmin : min A (c * A) ≤ t := ht.1
  have hlow : (99 / 100 : ℝ) * A ≤ t := by
    apply le_trans (le_min ?_ ?_) htmin <;> nlinarith
  have ht0 : 0 < t := (by positivity : 0 < (99 / 100 : ℝ) * A).trans_le hlow
  refine ⟨hlow, ?_⟩
  by_cases hc1 : 1 ≤ c
  · have hAt : A ≤ t := by
      have h : A ≤ c * A := by nlinarith
      simpa only [min_eq_left h] using htmin
    have hlogc : Real.log c ≤ (1 / 100 : ℝ) :=
      (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
    rw [Real.log_div ht0.ne' hc0.ne']
    have hlogt := Real.log_le_log ha0 hAt
    linarith
  · have hc1' : c ≤ 1 := (lt_of_not_ge hc1).le
    have hAt : c * A ≤ t := by
      have h : c * A ≤ A := by nlinarith
      simpa only [min_eq_right h] using htmin
    have hdiv : A ≤ t / c := (le_div_iff₀ hc0).mpr (by simpa [mul_comm] using hAt)
    have hlogt := Real.log_le_log ha0 hdiv
    linarith

private theorem bandDerivative_continuous {a b c : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hz : ∀ t ∈ Icc a b, 0 < Real.log (t / c)) :
    ContinuousOn (bandDerivative c) (Icc a b) := by
  intro t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have hl := Real.continuousAt_log (div_ne_zero ht0.ne' hc.ne')
  have hlog : ContinuousAt (fun s : ℝ => Real.log (s / c)) t :=
    hl.comp' (f := fun s : ℝ => s / c) (x := t) (continuousAt_id.div_const c)
  exact ((hlog.add_const 1).div
    ((continuousAt_id.pow 2).mul (hlog.pow 2))
    (by
      change t ^ 2 * (Real.log (t / c)) ^ 2 ≠ 0
      exact mul_ne_zero (pow_ne_zero 2 ht0.ne') (pow_ne_zero 2 (hz t ht).ne'))).continuousWithinAt

private theorem bandDerivative_cap {A c t : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ))
    (ht : t ∈ Icc (bandLow A c) (bandHigh A c)) :
    0 ≤ bandDerivative c t ∧ bandDerivative c t ≤ (517 / 500 : ℝ) / (A ^ 2 * Real.log A) := by
  obtain ⟨ha, hc0, hl, hband⟩ := band_scale hA hc hc'
  obtain ⟨htA, hzA⟩ := hband t ht
  have ha0 : 0 < A := zero_lt_one.trans ha
  have ht0 : 0 < t := (by positivity : 0 < (99 / 100 : ℝ) * A).trans_le htA
  let L := Real.log A
  let z := Real.log (t / c)
  have hL : 78 ≤ L := hl
  have hz : L - 1 / 100 ≤ z := hzA
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < L := by linarith
  have hzlower : (7799 / 100 : ℝ) ≤ z := by linarith
  have hinv : 1 / z ≤ (100 / 7799 : ℝ) := by
    apply (div_le_iff₀ hz0).mpr
    nlinarith
  have hratio : L / z ≤ (7800 / 7799 : ℝ) := by
    apply (div_le_iff₀ hz0).mpr
    nlinarith
  have hsq : A ^ 2 / t ^ 2 ≤ (10000 / 9801 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [sq_nonneg (t - (99 / 100 : ℝ) * A)]
  have heq : bandDerivative c t * (A ^ 2 * L) =
      (A ^ 2 / t ^ 2) * (L / z) * (1 + 1 / z) := by
    change (z + 1) / (t ^ 2 * z ^ 2) * (A ^ 2 * L) =
      (A ^ 2 / t ^ 2) * (L / z) * (1 + 1 / z)
    field_simp [ht0.ne', hz0.ne']
    <;> ring
  have hbound : bandDerivative c t * (A ^ 2 * L) ≤ (517 / 500 : ℝ) := by
    rw [heq]
    calc
      (A ^ 2 / t ^ 2) * (L / z) * (1 + 1 / z) ≤
          (10000 / 9801 : ℝ) * (7800 / 7799 : ℝ) * (1 + (100 / 7799 : ℝ)) := by
        gcongr
      _ ≤ (517 / 500 : ℝ) := by norm_num
  refine ⟨?_, (le_div_iff₀ (by positivity : 0 < A ^ 2 * L)).mpr hbound⟩
  unfold bandDerivative
  change 0 ≤ (z + 1) / (t ^ 2 * z ^ 2)
  positivity

private theorem weightedPrefix_sub {f g : ℝ → ℝ} (R : ℝ) :
    weightedPrefix (fun t => f t - g t) R = weightedPrefix f R - weightedPrefix g R := by
  simp [weightedPrefix, arithmeticPrefix, mul_sub, Finset.sum_sub_distrib]

private theorem weightedPrefix_const (q R : ℝ) :
    weightedPrefix (fun _ => q) R = q * Chebyshev.psi R := by
  unfold weightedPrefix arithmeticPrefix
  rw [← Finset.sum_mul]
  change arithmeticPrefix (fun n => Λ n) R * q = q * Chebyshev.psi R
  rw [prefix_psi]
  ring

theorem supported_prefix {a b : ℝ} {f r : ℝ → ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a ≤ b) (hr : ∀ t : ℝ, r t = if a < t ∧ t ≤ b then f t else 0) :
    weightedPrefix r b = weightedPrefix f b - weightedPrefix f a := by
  let N := ⌈b⌉₊
  have hbN : b ≤ (N : ℝ) := Nat.le_ceil b
  unfold weightedPrefix
  rw [prefix_as_finite_sum _ hb.le hbN]
  have h := prefix_difference_finite (fun n => Λ n * f n) (N := N) (c := a / b) (y := b)
    hb.le (by simpa [div_mul_cancel₀ _ hb.ne'] using ha)
    (by simpa [div_mul_cancel₀ _ hb.ne'] using hab) hbN
  rw [div_mul_cancel₀ _ hb.ne'] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr]
  simp only [Nat.cast_add, Nat.cast_one] at *
  split_ifs <;> simp_all

private theorem abel_prefix {a b : ℝ} {f : ℝ → ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Icc a b)) :
    weightedPrefix f b - weightedPrefix f a =
      f b * Chebyshev.psi b - f a * Chebyshev.psi a -
        ∫ t in a..b, deriv f t * Chebyshev.psi t := by
  have hsum := Finset.sum_Ioc_consecutive (fun n => Λ n * f n)
    (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab)
  have hw : weightedPrefix f b - weightedPrefix f a =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * Λ n := by
    simp only [weightedPrefix, prefix_eq_Ioc] at *
    simp only [mul_comm (f _) (Λ _)]
    linarith
  rw [hw]
  have h := sum_mul_eq_sub_sub_integral_mul (fun n => (Λ n : ℝ)) ha hab hf hfi
  simpa only [← Chebyshev.psi_eq_sum_Icc, ← intervalIntegral.integral_of_le hab] using h

private theorem prefix_product_integrable {a b : ℝ} {f : ℝ → ℝ} (ha : 0 ≤ a)
    (hf : IntegrableOn f (Icc a b)) :
    IntegrableOn (fun t => f t * Chebyshev.psi t) (Icc a b) := by
  simpa only [← Chebyshev.psi_eq_sum_Icc] using
    (integrableOn_mul_sum_Icc (fun n => (Λ n : ℝ)) ha hf (m := 0))

private theorem reciprocalLog_FTC {a b c : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ t ∈ Icc a b, 0 < Real.log (t / c)) :
    (∫ t in a..b, bandDerivative c t) = reciprocalLog c a - reciprocalLog c b := by
  have hi := (bandDerivative_continuous hc ha hz).intervalIntegrable_of_Icc (μ := volume) hab
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s => -reciprocalLog c s) (bandDerivative c t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    simpa only [neg_neg] using
      (reciprocalLog_deriv hc (ha.trans_le ht.1) (hz t ht).ne').fun_neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  linarith

theorem band_mass_forward {a b c : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ t ∈ Icc a b, 0 < Real.log (t / c)) :
    weightedPrefix (fun t => reciprocalLog c t - reciprocalLog c b) b -
      weightedPrefix (fun t => reciprocalLog c t - reciprocalLog c b) a =
        ∫ t in a..b, bandDerivative c t * (Chebyshev.psi t - Chebyshev.psi a) := by
  have hk := bandDerivative_continuous hc ha hz
  have hki := hk.integrableOn_Icc (μ := volume)
  have hg : ∀ t ∈ Icc a b, HasDerivAt (reciprocalLog c) (-bandDerivative c t) t :=
    fun t ht => reciprocalLog_deriv hc (ha.trans_le ht.1) (hz t ht).ne'
  have hderiv : ∀ t ∈ Icc a b, deriv (reciprocalLog c) t = -bandDerivative c t :=
    fun t ht => (hg t ht).deriv
  have hgi : IntegrableOn (deriv (reciprocalLog c)) (Icc a b) :=
    hki.neg.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have habel := abel_prefix ha.le hab (fun t ht => (hg t ht).differentiableAt) hgi
  have hpsi := prefix_product_integrable ha.le hki
  have hip : IntervalIntegrable (fun t => bandDerivative c t * Chebyshev.psi t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hpsi
  have hic := hk.intervalIntegrable_of_Icc (μ := volume) hab |>.mul_const (Chebyshev.psi a)
  have hdiff : (∫ t in a..b, deriv (reciprocalLog c) t * Chebyshev.psi t) =
      -(∫ t in a..b, bandDerivative c t * Chebyshev.psi t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    change deriv (reciprocalLog c) t * Chebyshev.psi t =
      -(bandDerivative c t * Chebyshev.psi t)
    rw [hderiv t ht]
    ring
  rw [hdiff] at habel
  simp only [weightedPrefix_sub, weightedPrefix_const]
  rw [show (fun t => bandDerivative c t * (Chebyshev.psi t - Chebyshev.psi a)) =
    (fun t => bandDerivative c t * Chebyshev.psi t - bandDerivative c t * Chebyshev.psi a) by funext t; ring,
    intervalIntegral.integral_sub hip hic, intervalIntegral.integral_mul_const, reciprocalLog_FTC hc ha hab hz]
  linarith

private theorem band_mass_reverse {a b c : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ t ∈ Icc a b, 0 < Real.log (t / c)) :
    weightedPrefix (fun t => reciprocalLog c a - reciprocalLog c t) b -
      weightedPrefix (fun t => reciprocalLog c a - reciprocalLog c t) a =
        ∫ t in a..b, bandDerivative c t * (Chebyshev.psi b - Chebyshev.psi t) := by
  have hfor := band_mass_forward hc ha hab hz
  have hk := bandDerivative_continuous hc ha hz
  have hi := hk.intervalIntegrable_of_Icc (μ := volume) hab
  have hip : IntervalIntegrable (fun t => bandDerivative c t * Chebyshev.psi t)
      volume a b := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (prefix_product_integrable ha.le (hk.integrableOn_Icc (μ := volume)))
  simp only [weightedPrefix_sub, weightedPrefix_const] at *
  rw [show (fun t => bandDerivative c t * (Chebyshev.psi b - Chebyshev.psi t)) =
    (fun t => bandDerivative c t * Chebyshev.psi b - bandDerivative c t * Chebyshev.psi t) by funext t; ring,
    intervalIntegral.integral_sub (hi.mul_const _) hip, intervalIntegral.integral_mul_const,
    reciprocalLog_FTC hc ha hab hz]
  rw [show (fun t => bandDerivative c t * (Chebyshev.psi t - Chebyshev.psi a)) =
    (fun t => bandDerivative c t * Chebyshev.psi t - bandDerivative c t * Chebyshev.psi a) by funext t; ring,
    intervalIntegral.integral_sub hip (hi.mul_const _), intervalIntegral.integral_mul_const,
    reciprocalLog_FTC hc ha hab hz] at hfor
  linarith

theorem triangle_volume_forward {a b c : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ t ∈ Icc a b, 0 < Real.log (t / c)) :
    (∫ t in a..b, reciprocalLog c t - reciprocalLog c b) =
      ∫ t in a..b, bandDerivative c t * (t - a) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (reciprocalLog c) (-bandDerivative c t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact reciprocalLog_deriv hc (ha.trans_le ht.1) (hz t ht).ne'
  have hki := (bandDerivative_continuous hc ha hz).intervalIntegrable_of_Icc (μ := volume) hab
  have hgi : IntervalIntegrable (reciprocalLog c) volume a b :=
    ContinuousOn.intervalIntegrable (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t - a) (v := reciprocalLog c)
    (u' := fun _ => (1 : ℝ)) (v' := fun t => -bandDerivative c t)
    (fun t _ => (hasDerivAt_id t).sub_const a) hd intervalIntegrable_const hki.neg
  rw [show (fun t => (t - a) * -bandDerivative c t) =
    (fun t => -(bandDerivative c t * (t - a))) by funext t; ring,
    intervalIntegral.integral_neg] at hparts
  simp only [sub_self, zero_mul, one_mul] at hparts
  rw [intervalIntegral.integral_sub hgi intervalIntegrable_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  linarith

private theorem triangle_volume_reverse {a b c : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ t ∈ Icc a b, 0 < Real.log (t / c)) :
    (∫ t in a..b, reciprocalLog c a - reciprocalLog c t) =
      ∫ t in a..b, bandDerivative c t * (b - t) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (reciprocalLog c) (-bandDerivative c t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact reciprocalLog_deriv hc (ha.trans_le ht.1) (hz t ht).ne'
  have hki := (bandDerivative_continuous hc ha hz).intervalIntegrable_of_Icc (μ := volume) hab
  have hgi : IntervalIntegrable (reciprocalLog c) volume a b :=
    ContinuousOn.intervalIntegrable (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => b - t) (v := reciprocalLog c)
    (u' := fun _ => (-1 : ℝ)) (v' := fun t => -bandDerivative c t)
    (fun t _ => by simpa only [id_eq] using
      HasDerivAt.const_sub b (hasDerivAt_id t)) hd intervalIntegrable_const hki.neg
  rw [show (fun t => (b - t) * -bandDerivative c t) =
    (fun t => -(bandDerivative c t * (b - t))) by funext t; ring,
    intervalIntegral.integral_neg] at hparts
  simp only [sub_self, zero_mul, neg_one_mul, intervalIntegral.integral_neg] at hparts
  rw [intervalIntegral.integral_sub intervalIntegrable_const hgi, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  linarith

private theorem integral_supported {a b R : ℝ} {f r : ℝ → ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbR : b ≤ R)
    (hr : ∀ t : ℝ, r t = if a < t ∧ t ≤ b then f t else 0) :
    (∫ t in (0 : ℝ)..R, r t) = ∫ t in a..b, f t := by
  have he : r = (Ioc a b).indicator f := by
    funext t
    rw [hr]
    simp only [Set.indicator, Set.mem_Ioc]
  rw [he, intervalIntegral.integral_of_le (ha.trans (hab.trans hbR)),
    setIntegral_indicator measurableSet_Ioc]
  have hs : Ioc a b ⊆ Ioc (0 : ℝ) R := fun t ht => ⟨ha.trans_lt ht.1, ht.2.trans hbR⟩
  rw [inter_eq_right.mpr hs, ← intervalIntegral.integral_of_le hab]

private theorem supported_integrable {a b R : ℝ} {f r : ℝ → ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbR : b ≤ R) (hf : ContinuousOn f (Icc a b))
    (hr : ∀ t : ℝ, r t = if a < t ∧ t ≤ b then f t else 0) :
    IntervalIntegrable r volume 0 R := by
  have he : r = (Ioc a b).indicator f := by funext t; rw [hr]; simp only [Set.indicator, Set.mem_Ioc]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (ha.trans (hab.trans hbR)), he,
    IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn, Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc a b ⊆ Icc (0 : ℝ) R := fun t ht => ⟨(ha.trans_lt ht.1).le, ht.2.trans hbR⟩
  rw [inter_eq_left.mpr hs]
  exact hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem positive_distance_compensation {h H ε C : ℝ} {k m : ℝ → ℝ}
    (hh : 0 ≤ h) (hH : 0 < H) (hε : ε ≤ 1)
    (hk : ContinuousOn k (Icc 0 h))
    (hkm : IntervalIntegrable (fun r => k r * m r) volume 0 h)
    (hk0 : ∀ r ∈ Icc 0 h, 0 ≤ k r)
    (hkC : ∀ r ∈ Icc 0 h, k r ≤ C)
    (hm0 : ∀ r ∈ Icc 0 h, 0 ≤ m r)
    (hm : ∀ r ∈ Icc 0 h, H ≤ r → (1 - ε) * r ≤ m r) :
    (1 - ε) * max 0 ((∫ r in (0 : ℝ)..h, k r * r) - C / 2 * min (H ^ 2) (h ^ 2)) ≤
      ∫ r in (0 : ℝ)..h, k r * m r := by
  let s := min H h
  have hs0 : 0 ≤ s := le_min hH.le hh
  have hsh : s ≤ h := min_le_right _ _
  have hv : IntervalIntegrable (fun r => k r * r) volume 0 h :=
    (hk.mul continuousOn_id).intervalIntegrable_of_Icc hh
  have hs1 : IntervalIntegrable (fun r => k r * r) volume 0 s := hv.mono_set (by
    simp only [uIcc_of_le hh, uIcc_of_le hs0]
    exact Icc_subset_Icc le_rfl hsh)
  have hs2 : IntervalIntegrable (fun r => k r * r) volume s h := hv.mono_set (by
    simp only [uIcc_of_le hh, uIcc_of_le hsh]
    exact Icc_subset_Icc hs0 le_rfl)
  have hm1 := hkm.mono_set (show uIcc 0 s ⊆ uIcc 0 h by
    rw [uIcc_of_le hs0, uIcc_of_le hh]; exact Icc_subset_Icc le_rfl hsh)
  have hm2 := hkm.mono_set (show uIcc s h ⊆ uIcc 0 h by
    rw [uIcc_of_le hsh, uIcc_of_le hh]; exact Icc_subset_Icc hs0 le_rfl)
  have hshort0 : 0 ≤ ∫ r in (0 : ℝ)..s, k r * m r :=
    intervalIntegral.integral_nonneg hs0 (fun r hr =>
      mul_nonneg (hk0 r ⟨hr.1, hr.2.trans hsh⟩) (hm0 r ⟨hr.1, hr.2.trans hsh⟩))
  have hlong : (1 - ε) * (∫ r in s..h, k r * r) ≤ ∫ r in s..h, k r * m r := by
    by_cases hHh : H ≤ h
    · rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hsh (hs2.const_mul _) hm2
      intro r hr
      have hr' : r ∈ Icc 0 h := ⟨hs0.trans hr.1, hr.2⟩
      have hHr : H ≤ r := by simpa only [s, min_eq_left hHh] using hr.1
      nlinarith [mul_le_mul_of_nonneg_left (hm r hr' hHr) (hk0 r hr')]
    · simp only [s, min_eq_right (le_of_lt (lt_of_not_ge hHh)), intervalIntegral.integral_same,
        mul_zero, le_refl]
  have hshort : (∫ r in (0 : ℝ)..s, k r * r) ≤ C / 2 * s ^ 2 := by
    have hcint : IntervalIntegrable (fun r : ℝ => C * r) volume 0 s :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hb := intervalIntegral.integral_mono_on hs0 hs1 hcint (fun r hr =>
      mul_le_mul_of_nonneg_right (hkC r ⟨hr.1, hr.2.trans hsh⟩) hr.1)
    have heval : (∫ r in (0 : ℝ)..s, C * r) = C / 2 * s ^ 2 := by
      have hd : ∀ r ∈ uIcc (0 : ℝ) s,
          HasDerivAt (fun t : ℝ => C / 2 * t ^ 2) (C * r) r := by
        intro r _
        have hd := ((hasDerivAt_id r).pow 2).const_mul (C / 2)
        change HasDerivAt (fun t : ℝ => C / 2 * t ^ 2) _ r at hd
        apply hd.congr_deriv
        simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]
        ring
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcint
    rwa [heval] at hb
  have hsSq : s ^ 2 = min (H ^ 2) (h ^ 2) := by
    by_cases hHh : H ≤ h
    · simp only [s, min_eq_left hHh, min_eq_left (by nlinarith : H ^ 2 ≤ h ^ 2)]
    · have hhH : h ≤ H := le_of_lt (lt_of_not_ge hHh)
      simp only [s, min_eq_right hhH, min_eq_right (by nlinarith : h ^ 2 ≤ H ^ 2)]
  rw [hsSq] at hshort
  have hsplitv := intervalIntegral.integral_add_adjacent_intervals hs1 hs2
  have hsplitm := intervalIntegral.integral_add_adjacent_intervals hm1 hm2
  have hbound : (1 - ε) * ((∫ r in (0 : ℝ)..h, k r * r) - C / 2 * min (H ^ 2) (h ^ 2)) ≤
      ∫ r in (0 : ℝ)..h, k r * m r := by
    have hmul := mul_le_mul_of_nonneg_left hshort (by linarith : 0 ≤ 1 - ε)
    nlinarith
  by_cases hp : 0 ≤ (∫ r in (0 : ℝ)..h, k r * r) - C / 2 * min (H ^ 2) (h ^ 2)
  · rwa [max_eq_right hp]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hp)), mul_zero]
    exact intervalIntegral.integral_nonneg hh (fun r hr => mul_nonneg (hk0 r hr) (hm0 r hr))

private theorem actual_increment_nonneg {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : 0 < v) : 0 ≤ Chebyshev.psi v - Chebyshev.psi u := by
  rw [actual_increment hu huv (Nat.le_ceil v) hv]
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

private theorem local_band_geometry {A c : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) :
    0 < bandLow A c ∧
      ∀ t ∈ Icc (bandLow A c) (bandHigh A c),
        (99 / 100 : ℝ) * A ≤ t ∧ t ≤ 2 * ((99 / 100 : ℝ) * A) ∧ 0 < Real.log (t / c) := by
  obtain ⟨ha, hc0, hl, ht⟩ := band_scale hA hc hc'
  have ha0 : 0 < A := zero_lt_one.trans ha
  refine ⟨lt_min ha0 (mul_pos hc0 ha0), ?_⟩
  intro t htt
  obtain ⟨htA, hz⟩ := ht t htt
  have hhigh : bandHigh A c ≤ (101 / 100 : ℝ) * A := by
    unfold bandHigh
    apply max_le <;> nlinarith
  exact ⟨htA, by linarith [htt.2.trans hhigh], by linarith⟩

private theorem actual_layer_forward {A c : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) (hc1 : 1 ≤ c) :
    actualCompensation A c =
      (∫ t in A..c * A, bandDerivative c t * (Chebyshev.psi t - Chebyshev.psi A)) ∧
    bandVolume A c = (∫ t in A..c * A, bandDerivative c t * (t - A)) := by
  obtain ⟨ha, hc0, hl, ht⟩ := band_scale hA hc hc'
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hab : A ≤ c * A := by nlinarith
  have hband : Icc (bandLow A c) (bandHigh A c) = Icc A (c * A) := by
    simp [bandLow, bandHigh, min_eq_left hab, max_eq_right hab]
  have hz : ∀ t ∈ Icc A (c * A), 0 < Real.log (t / c) := by
    intro t htt
    have h := (ht t (hband.symm ▸ htt)).2
    linarith
  constructor
  · unfold actualCompensation
    rw [bandHigh, max_eq_right hab]
    rw [supported_prefix ha0.le (mul_pos hc0 ha0) hab (fun t => residual_forward (t := t) ha hc1)]
    exact band_mass_forward hc0 ha0 hab hz
  · unfold bandVolume
    rw [bandHigh, max_eq_right hab,
      integral_supported ha0.le hab le_rfl (fun t => residual_forward (t := t) ha hc1)]
    exact triangle_volume_forward hc0 ha0 hab hz

private theorem actual_layer_reverse {A c : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) (hc1 : c ≤ 1) :
    actualCompensation A c =
      (∫ t in c * A..A, bandDerivative c t * (Chebyshev.psi A - Chebyshev.psi t)) ∧
    bandVolume A c = (∫ t in c * A..A, bandDerivative c t * (A - t)) := by
  obtain ⟨ha, hc0, hl, ht⟩ := band_scale hA hc hc'
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hab : c * A ≤ A := by nlinarith
  have hband : Icc (bandLow A c) (bandHigh A c) = Icc (c * A) A := by
    simp [bandLow, bandHigh, min_eq_right hab, max_eq_left hab]
  have hz : ∀ t ∈ Icc (c * A) A, 0 < Real.log (t / c) := by
    intro t htt
    have h := (ht t (hband.symm ▸ htt)).2
    linarith
  constructor
  · unfold actualCompensation
    rw [bandHigh, max_eq_left hab]
    rw [supported_prefix (mul_pos hc0 ha0).le ha0 hab (fun t => residual_reverse (t := t) ha hc0 hc1)]
    exact band_mass_reverse hc0 (mul_pos hc0 ha0) hab hz
  · unfold bandVolume
    rw [bandHigh, max_eq_left hab,
      integral_supported (mul_pos hc0 ha0).le hab le_rfl (fun t => residual_reverse (t := t) ha hc0 hc1)]
    exact triangle_volume_reverse hc0 (mul_pos hc0 ha0) hab hz

private theorem forward_compensation {A c H ε : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) (hc1 : 1 ≤ c)
    (hH : 0 < H) (hε : ε < 1) (hθ : ThetaIncrementLower ((99 / 100 : ℝ) * A) H ε) :
    (1 - ε) * max 0 (bandVolume A c - shortAllowance A c H) ≤ actualCompensation A c := by
  obtain ⟨ha, hc0, hl, ht⟩ := band_scale hA hc hc'
  obtain ⟨hlow, hgeo⟩ := local_band_geometry hA hc hc'
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hab : A ≤ c * A := by nlinarith
  let h := c * A - A
  have hh : 0 ≤ h := sub_nonneg.mpr hab
  have hband : Icc (bandLow A c) (bandHigh A c) = Icc A (c * A) := by
    simp [bandLow, bandHigh, min_eq_left hab, max_eq_right hab]
  have hmap : ∀ r ∈ Icc (0 : ℝ) h, A + r ∈ Icc (bandLow A c) (bandHigh A c) := by
    intro r hr
    rw [hband]
    dsimp [h] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hz : ∀ t ∈ Icc A (c * A), 0 < Real.log (t / c) :=
    fun t htt => (hgeo t (hband.symm ▸ htt)).2.2
  have hk := bandDerivative_continuous hc0 ha0 hz
  have hkcoord : ContinuousOn (fun r => bandDerivative c (A + r)) (Icc 0 h) :=
    hk.comp (continuousOn_const.add continuousOn_id) (fun r hr => hband ▸ hmap r hr)
  have hip := prefix_product_integrable ha0.le (hk.integrableOn_Icc (μ := volume))
  have hi : IntervalIntegrable (fun t => bandDerivative c t * (Chebyshev.psi t - Chebyshev.psi A))
      volume A (c * A) := by
    have hs := hip.sub (hk.integrableOn_Icc (μ := volume).mul_const (Chebyshev.psi A))
    change IntegrableOn
      (fun t => bandDerivative c t * Chebyshev.psi t - bandDerivative c t * Chebyshev.psi A)
      (Icc A (c * A)) volume at hs
    simpa only [mul_sub] using (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hs
  have hicoord : IntervalIntegrable
      (fun r => bandDerivative c (A + r) * (Chebyshev.psi (A + r) - Chebyshev.psi A)) volume 0 h := by
    simpa [h] using hi.comp_add_left A
  have hbound := positive_distance_compensation hh hH hε.le hkcoord hicoord
    (fun r hr => (bandDerivative_cap hA hc hc' (hmap r hr)).1)
    (fun r hr => (bandDerivative_cap hA hc hc' (hmap r hr)).2)
    (fun r hr => actual_increment_nonneg ha0.le (by linarith [hr.1]) (by linarith [hr.1]))
    (fun r hr hHr => by
      have hm := hmap r hr
      have hma := hmap 0 ⟨le_rfl, hh⟩
      have hθ' := hθ A (A + r) (by simpa using (hgeo A (by simpa using hma)).1)
        (by linarith) (hgeo (A + r) hm).2.1 (by linarith)
      have hψ := theta_increment_le_psi (show A ≤ A + r by linarith [hr.1])
      nlinarith)
  have hmtrans := intervalIntegral.integral_comp_add_left
    (fun t => bandDerivative c t * (Chebyshev.psi t - Chebyshev.psi A)) A (a := 0) (b := h)
  have hvtrans := intervalIntegral.integral_comp_add_left
    (fun t => bandDerivative c t * (t - A)) A (a := 0) (b := h)
  simp only [add_zero, h, show A + (c * A - A) = c * A by ring] at hmtrans hvtrans
  simp only [add_sub_cancel_left] at hvtrans
  rw [hmtrans, hvtrans, ← (actual_layer_forward hA hc hc' hc1).1,
    ← (actual_layer_forward hA hc hc' hc1).2] at hbound
  have he : (517 / 500 : ℝ) / (A ^ 2 * Real.log A) / 2 * min (H ^ 2) (h ^ 2) =
      shortAllowance A c H := by
    have hs : h ^ 2 = A ^ 2 * (c - 1) ^ 2 := by dsimp [h]; ring
    rw [hs]
    unfold shortAllowance
    ring
  rwa [he] at hbound

private theorem reverse_compensation {A c H ε : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) (hc1 : c ≤ 1)
    (hH : 0 < H) (hε : ε < 1) (hθ : ThetaIncrementLower ((99 / 100 : ℝ) * A) H ε) :
    (1 - ε) * max 0 (bandVolume A c - shortAllowance A c H) ≤ actualCompensation A c := by
  obtain ⟨ha, hc0, hl, ht⟩ := band_scale hA hc hc'
  obtain ⟨hlow, hgeo⟩ := local_band_geometry hA hc hc'
  have ha0 : 0 < A := zero_lt_one.trans ha
  have hab : c * A ≤ A := by nlinarith
  let h := A - c * A
  have hh : 0 ≤ h := sub_nonneg.mpr hab
  have hband : Icc (bandLow A c) (bandHigh A c) = Icc (c * A) A := by
    simp [bandLow, bandHigh, min_eq_right hab, max_eq_left hab]
  have hmap : ∀ r ∈ Icc (0 : ℝ) h, A - r ∈ Icc (bandLow A c) (bandHigh A c) := by
    intro r hr
    rw [hband]
    dsimp [h] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hz : ∀ t ∈ Icc (c * A) A, 0 < Real.log (t / c) :=
    fun t htt => (hgeo t (hband.symm ▸ htt)).2.2
  have hk := bandDerivative_continuous hc0 (mul_pos hc0 ha0) hz
  have hkcoord : ContinuousOn (fun r => bandDerivative c (A - r)) (Icc 0 h) :=
    hk.comp (continuousOn_const.sub continuousOn_id) (fun r hr => hband ▸ hmap r hr)
  have hip := prefix_product_integrable (mul_pos hc0 ha0).le
    (hk.integrableOn_Icc (μ := volume))
  have hi : IntervalIntegrable (fun t => bandDerivative c t * (Chebyshev.psi A - Chebyshev.psi t))
      volume (c * A) A := by
    have hs := (hk.integrableOn_Icc (μ := volume).mul_const (Chebyshev.psi A)).sub hip
    change IntegrableOn
      (fun t => bandDerivative c t * Chebyshev.psi A - bandDerivative c t * Chebyshev.psi t)
      (Icc (c * A) A) volume at hs
    simpa only [mul_sub] using (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hs
  have hicoord : IntervalIntegrable
      (fun r => bandDerivative c (A - r) * (Chebyshev.psi A - Chebyshev.psi (A - r))) volume 0 h := by
    simpa [h] using (hi.comp_sub_left A).symm
  have hbound := positive_distance_compensation hh hH hε.le hkcoord hicoord
    (fun r hr => (bandDerivative_cap hA hc hc' (hmap r hr)).1)
    (fun r hr => (bandDerivative_cap hA hc hc' (hmap r hr)).2)
    (fun r hr => actual_increment_nonneg (hlow.trans_le (hmap r hr).1).le (by linarith [hr.1]) ha0)
    (fun r hr hHr => by
      have hm := hmap r hr
      have hma := hmap 0 ⟨le_rfl, hh⟩
      have hθ' := hθ (A - r) A (hgeo (A - r) hm).1
        (by linarith) (by simpa using (hgeo A (by simpa using hma)).2.1) (by linarith)
      have hψ := theta_increment_le_psi (show A - r ≤ A by linarith [hr.1])
      nlinarith)
  have hmtrans := intervalIntegral.integral_comp_sub_left
    (fun t => bandDerivative c t * (Chebyshev.psi A - Chebyshev.psi t)) A (a := 0) (b := h)
  have hvtrans := intervalIntegral.integral_comp_sub_left
    (fun t => bandDerivative c t * (A - t)) A (a := 0) (b := h)
  simp only [sub_zero, h, sub_sub_cancel] at hmtrans hvtrans
  rw [hmtrans, hvtrans, ← (actual_layer_reverse hA hc hc' hc1).1,
    ← (actual_layer_reverse hA hc hc' hc1).2] at hbound
  have he : (517 / 500 : ℝ) / (A ^ 2 * Real.log A) / 2 * min (H ^ 2) (h ^ 2) =
      shortAllowance A c H := by
    have hs : h ^ 2 = A ^ 2 * (c - 1) ^ 2 := by dsimp [h]; ring
    rw [hs]
    unfold shortAllowance
    ring
  rwa [he] at hbound

/-- The primitive real theta bound pays the actual finite Λ-weighted residual,
including empty and arbitrarily short bands and c=1. There is no clock shift. -/
theorem actual_vonMangoldt_band_compensation_of_theta_increment_lower {A c H ε : ℝ}
    (hA : Real.exp 78 ≤ A) (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ))
    (hH : 0 < H) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hθ : ThetaIncrementLower ((99 / 100 : ℝ) * A) H ε) :
    (1 - ε) * max 0 (bandVolume A c - shortAllowance A c H) ≤ actualCompensation A c := by
  rcases le_total 1 c with h | h
  · exact forward_compensation hA hc hc' h hH hε hθ
  · exact reverse_compensation hA hc hc' h hH hε hθ

private theorem plateau_prefix {A R q : ℝ} {f : ℝ → ℝ} (hA : 0 ≤ A) (hAR : A ≤ R) :
    weightedPrefix (fun t => if t ≤ A then q else f t) R =
      q * Chebyshev.psi A + weightedPrefix f R - weightedPrefix f A := by
  let N := ⌈R⌉₊
  have hRN : R ≤ (N : ℝ) := Nat.le_ceil R
  have hAN : A ≤ (N : ℝ) := hAR.trans hRN
  rw [← weightedPrefix_const q A]
  unfold weightedPrefix
  rw [prefix_as_finite_sum _ (hA.trans hAR) hRN, prefix_as_finite_sum _ hA hAN,
    prefix_as_finite_sum _ (hA.trans hAR) hRN, prefix_as_finite_sum _ hA hAN,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.cast_add, Nat.cast_one]
  by_cases hnA : (i : ℝ) + 1 ≤ A
  · simp [hnA, hnA.trans hAR]
  · simp [hnA]

private theorem plateau_response {A R q : ℝ} {f : ℝ → ℝ} (hA : 0 ≤ A) (hAR : A ≤ R)
    (hd : ∀ t ∈ Icc A R, DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Icc A R)) :
    weightedPrefix (fun t => if t ≤ A then q else f t) R -
        (∫ t in (0 : ℝ)..R, if t ≤ A then q else f t) =
      (q - f A) * discrepancy A + f R * discrepancy R -
        ∫ t in A..R, discrepancy t * deriv f t := by
  have hf : ContinuousOn f (Icc A R) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hfi := hf.intervalIntegrable_of_Icc (μ := volume) hAR
  have hdfi := hdf.intervalIntegrable_of_Icc (μ := volume) hAR
  have hlow : IntervalIntegrable (fun t : ℝ => if t ≤ A then q else f t) volume 0 A := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q) volume 0 A).congr
    intro t ht
    rw [uIoc_of_le hA] at ht
    simp only [if_pos ht.2]
  have hhigh : IntervalIntegrable (fun t : ℝ => if t ≤ A then q else f t) volume A R := by
    apply hfi.congr
    intro t ht
    rw [uIoc_of_le hAR] at ht
    simp only [if_neg (not_le.mpr ht.1)]
  have hpiece : (∫ t in (0 : ℝ)..R, if t ≤ A then q else f t) =
      q * A + ∫ t in A..R, f t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hlow hhigh]
    have h0 : (∫ t in (0 : ℝ)..A, if t ≤ A then q else f t) = A * q := by
      rw [show (∫ t in (0 : ℝ)..A, if t ≤ A then q else f t) = ∫ _ in (0 : ℝ)..A, q by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hA] at ht
        exact if_pos ht.2]
      simp [intervalIntegral.integral_const]
    have h1 : (∫ t in A..R, if t ≤ A then q else f t) = ∫ t in A..R, f t := by
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall (fun t ht => by
        rw [uIoc_of_le hAR] at ht
        exact if_neg (not_le.mpr ht.1))
    rw [h0, h1]
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ => (1 : ℝ)) (v := f) (v' := deriv f)
    (fun t _ => hasDerivAt_id t)
    (fun t ht => hd t ((uIcc_of_le hAR) ▸ ht) |>.hasDerivAt)
    intervalIntegrable_const hdfi
  simp only [one_mul] at hparts
  have hpsi := (intervalIntegrable_iff_integrableOn_Icc_of_le hAR).mpr
    (prefix_product_integrable hA hdf.integrableOn_Icc)
  have htprod : IntervalIntegrable (fun t => t * deriv f t) volume A R :=
    (continuousOn_id.mul hdf).intervalIntegrable_of_Icc hAR
  have hD : (∫ t in A..R, discrepancy t * deriv f t) =
      (∫ t in A..R, deriv f t * Chebyshev.psi t) - (∫ t in A..R, t * deriv f t) := by
    unfold discrepancy
    rw [show (fun t => (Chebyshev.psi t - t) * deriv f t) =
      (fun t => deriv f t * Chebyshev.psi t - t * deriv f t) by funext t; ring,
      intervalIntegral.integral_sub hpsi htprod]
  have habel := abel_prefix hA hAR hd hdf.integrableOn_Icc
  rw [plateau_prefix hA hAR, hpiece, hD]
  unfold discrepancy
  nlinarith

private theorem plateau_integrable {A R q : ℝ} {f : ℝ → ℝ} (hA : 0 ≤ A) (hAR : A ≤ R)
    (hf : ContinuousOn f (Icc A R)) :
    IntervalIntegrable (fun t => if t ≤ A then q else f t) volume 0 R := by
  have hlow : IntervalIntegrable (fun t : ℝ => if t ≤ A then q else f t) volume 0 A := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q) volume 0 A).congr
    intro t ht
    rw [uIoc_of_le hA] at ht
    simp only [if_pos ht.2]
  have hhigh : IntervalIntegrable (fun t : ℝ => if t ≤ A then q else f t) volume A R := by
    apply (hf.intervalIntegrable_of_Icc hAR).congr
    intro t ht
    rw [uIoc_of_le hAR] at ht
    simp only [if_neg (not_le.mpr ht.1)]
  exact hlow.trans hhigh

private theorem supported_prefix_stable {a b R : ℝ} {f r : ℝ → ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbR : b ≤ R)
    (hr : ∀ t : ℝ, r t = if a < t ∧ t ≤ b then f t else 0) :
    weightedPrefix r R = weightedPrefix r b := by
  let N := ⌈R⌉₊
  have hb : 0 ≤ b := ha.trans hab
  have hRN : R ≤ (N : ℝ) := Nat.le_ceil R
  unfold weightedPrefix
  rw [prefix_as_finite_sum _ (hb.trans hbR) hRN,
    prefix_as_finite_sum _ hb (hbR.trans hRN)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.cast_add, Nat.cast_one]
  by_cases hi : (i : ℝ) + 1 ≤ b
  · simp only [if_pos hi, if_pos (hi.trans hbR)]
  · rw [hr]
    simp [hi]

private theorem local_residual_support {A c : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc (bandLow A c) (bandHigh A c)) ∧
      ∀ t : ℝ, residualKernel A c t =
        if bandLow A c < t ∧ t ≤ bandHigh A c then f t else 0 := by
  obtain ⟨ha, hc0, hl, ht⟩ := band_scale hA hc hc'
  obtain ⟨hlow, hgeo⟩ := local_band_geometry hA hc hc'
  have hg : ContinuousOn (reciprocalLog c) (Icc (bandLow A c) (bandHigh A c)) := by
    intro t htt
    exact (reciprocalLog_deriv hc0 (hlow.trans_le htt.1) (hgeo t htt).2.2.ne').continuousAt.continuousWithinAt
  rcases le_total 1 c with hc1 | hc1
  · have hab : A ≤ c * A := by have := zero_lt_one.trans ha; nlinarith
    refine ⟨fun t => reciprocalLog c t - reciprocalLog c (c * A), hg.sub continuousOn_const, ?_⟩
    simpa only [bandLow, bandHigh, min_eq_left hab, max_eq_right hab] using (fun t => residual_forward (t := t) ha hc1)
  · have hab : c * A ≤ A := by have := zero_lt_one.trans ha; nlinarith
    refine ⟨fun t => reciprocalLog c (c * A) - reciprocalLog c t, continuousOn_const.sub hg, ?_⟩
    simpa only [bandLow, bandHigh, min_eq_right hab, max_eq_left hab] using (fun t => residual_reverse (t := t) ha hc0 hc1)

private def smoothSlope (c t : ℝ) : ℝ :=
  -(Real.log t - Real.log c + 1) / (t ^ 2 * (Real.log t - Real.log c) ^ 2) +
    (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) +
      (c - 1) * (Real.log t + 2) / (t ^ 2 * (Real.log t) ^ 3)

private theorem smoothRemainder_deriv {c t : ℝ} (ht : 0 < t)
    (hlog : Real.log t ≠ 0) (hz : Real.log t - Real.log c ≠ 0) :
    HasDerivAt (smoothRemainder c) (smoothSlope c t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have h1 := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).mul (hl.sub_const (Real.log c))) (mul_ne_zero ht.ne' hz)
  have h2 := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).mul hl) (mul_ne_zero ht.ne' hlog)
  have h3 := (hasDerivAt_const t (c - 1)).div
    ((hasDerivAt_id t).mul (hl.pow 2)) (mul_ne_zero ht.ne' (pow_ne_zero 2 hlog))
  have hd := (h1.sub h2).sub h3
  change HasDerivAt (smoothRemainder c) _ t at hd
  apply hd.congr_deriv
  simp only [smoothSlope, id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply,
    one_mul, zero_mul, zero_sub, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [ht.ne', hlog, hz]
  <;> ring

private theorem smooth_on_tail {A c R : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ)) :
    (∀ t ∈ Icc A R, DifferentiableAt ℝ (smoothRemainder c) t) ∧
      ContinuousOn (deriv (smoothRemainder c)) (Icc A R) := by
  obtain ⟨ha, hc0, hL, _⟩ := band_scale hA hc hc'
  have hlogc : Real.log c ≤ (1 / 100 : ℝ) :=
    (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
  have hpos : ∀ t ∈ Icc A R, 0 < t ∧ 0 < Real.log t ∧ 0 < Real.log t - Real.log c := by
    intro t ht
    have ht0 : 0 < t := (zero_lt_one.trans ha).trans_le ht.1
    have hl := Real.log_le_log (zero_lt_one.trans ha) ht.1
    exact ⟨ht0, by linarith, by linarith⟩
  have hd : ∀ t ∈ Icc A R, HasDerivAt (smoothRemainder c) (smoothSlope c t) t := by
    intro t ht
    obtain ⟨ht0, hl, hz⟩ := hpos t ht
    exact smoothRemainder_deriv ht0 hl.ne' hz.ne'
  refine ⟨fun t ht => (hd t ht).differentiableAt, ?_⟩
  have hcont : ContinuousOn (smoothSlope c) (Icc A R) := by
    intro t ht
    obtain ⟨ht0, hl, hz⟩ := hpos t ht
    have hlogcont := Real.continuousAt_log ht0.ne'
    unfold smoothSlope
    fun_prop (disch := first | positivity | exact ht0.ne')
  exact hcont.congr (fun t ht => (hd t ht).deriv)

/-- Exact finite signed response, with the actual right-closed R atom and the
smooth formula's trace at A. No derivative of the Chebyshev staircase occurs. -/
theorem finite_signed_response_identity {A c R : ℝ} (hA : Real.exp 78 ≤ A)
    (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ))
    (hAR : A < R) (hcAR : c * A ≤ R) :
    finiteResponse A c R = smoothBoundary A c R + bandVolume A c - actualCompensation A c := by
  obtain ⟨ha, hc0, hl, _⟩ := band_scale hA hc hc'
  obtain ⟨hlow, _⟩ := local_band_geometry hA hc hc'
  obtain ⟨f, hf, hres⟩ := local_residual_support hA hc hc'
  have hlh : bandLow A c ≤ bandHigh A c := min_le_max
  have hhigh : bandHigh A c ≤ R := max_le hAR.le hcAR
  obtain ⟨hdf, hdc⟩ := smooth_on_tail (R := R) hA hc hc'
  have hreg := plateau_integrable (q := plateau A c) (zero_lt_one.trans ha).le hAR.le
    (fun t ht => (hdf t ht).continuousAt.continuousWithinAt)
  have hresi := supported_integrable hlow.le hlh hhigh hf hres
  have he : centeredKernel A c = fun t => regularKernel A c t - residualKernel A c t := by
    funext t
    unfold residualKernel
    ring
  have hresponse := plateau_response (q := plateau A c) (zero_lt_one.trans ha).le hAR.le hdf hdc
  have hPi : weightedPrefix (residualKernel A c) R = actualCompensation A c := by
    exact supported_prefix_stable hlow.le hlh hhigh hres
  have hV : (∫ t in (0 : ℝ)..R, residualKernel A c t) = bandVolume A c := by
    unfold bandVolume
    rw [integral_supported hlow.le hlh hhigh hres, integral_supported hlow.le hlh le_rfl hres]
  change IntervalIntegrable (regularKernel A c) volume 0 R at hreg
  unfold finiteResponse
  rw [he, weightedPrefix_sub]
  change weightedPrefix (regularKernel A c) R - weightedPrefix (residualKernel A c) R -
    (∫ t in (0 : ℝ)..R, regularKernel A c t - residualKernel A c t) = _
  rw [intervalIntegral.integral_sub hreg hresi, hPi, hV]
  change _ = smoothBoundary A c R + _ - _
  change weightedPrefix (regularKernel A c) R - (∫ t in (0 : ℝ)..R, regularKernel A c t) = _ at hresponse
  change _ = smoothBoundary A c R at hresponse
  linarith

/-- The finite signed-response consumer uses the actual band payment and keeps
the complete smooth finite boundary. No infinite Gamma or signed anchor claim. -/
theorem finite_signed_response_upper_of_theta_increment_lower {A c R H ε : ℝ}
    (hA : Real.exp 78 ≤ A) (hc : (99 / 100 : ℝ) ≤ c) (hc' : c ≤ (101 / 100 : ℝ))
    (hAR : A < R) (hcAR : c * A ≤ R) (hH : 0 < H) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hθ : ThetaIncrementLower ((99 / 100 : ℝ) * A) H ε) :
    finiteResponse A c R ≤ smoothBoundary A c R + ε * bandVolume A c +
      (1 - ε) * shortAllowance A c H := by
  have hPi := actual_vonMangoldt_band_compensation_of_theta_increment_lower hA hc hc' hH hε0 hε hθ
  have hmax := le_max_right (0 : ℝ) (bandVolume A c - shortAllowance A c H)
  have hpay := mul_le_mul_of_nonneg_left hmax (by linarith : 0 ≤ 1 - ε)
  rw [finite_signed_response_identity hA hc hc' hAR hcAR]
  nlinarith

end D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation

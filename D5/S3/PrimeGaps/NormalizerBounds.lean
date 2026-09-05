/- GID: D5/S3/PrimeGaps/NormalizerBounds
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the normalizer integral bounds and the tilted coefficient moment estimates. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.EulerProducts

namespace LongGapsBetweenPrimes

noncomputable section

/-- The normalizer dominates every positive-half-line integral of U_(-t)-1. -/
theorem normalizer_integral_le {P : ℕ} (hP : P ≠ 0) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, divisorEulerMoment P (-t) - 1) ≤ normalizer P := by
  have hsum (t : ℝ) : divisorEulerMoment P (-t) - 1 =
      ∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ (-t) / d.totient := by
    rw [divisorEulerMoment,
      ← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr hP)]
    simp
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum]
  · unfold normalizer
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : (1 : ℝ) < d := by
      exact_mod_cast one_lt_of_mem_divisors_erase_one hd
    have hlog : 0 < Real.log d := Real.log_pos hd1
    simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hd1), mul_neg,
      ← neg_mul]
    rw [intervalIntegral.integral_div]
    calc
      (∫ t : ℝ in a..b, Real.exp (-Real.log d * t)) / (d.totient : ℝ) ≤
          (1 / Real.log d) / (d.totient : ℝ) :=
        div_le_div_of_nonneg_right (integral_exp_decay_le hlog ha b) (Nat.cast_nonneg _)
      _ = 1 / ((d.totient : ℝ) * Real.log d) := by ring
  · intro d hd
    have hdpos : 0 < (d : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd))
    apply Continuous.intervalIntegrable
    simp_rw [Real.rpow_def_of_pos hdpos]
    fun_prop

/-- Integrating the lower Euler-product bound gives a completely finite
lower bound for B; no sieve asymptotic is assumed. -/
theorem normalizer_lower_integral {Z Y : ℕ} (hZY : Z ≤ Y) {A a b : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ a * Real.log ((Y : ℝ) + 1)) :
    (Real.log b - Real.log a) / (2 * A) - (b - a) ≤ normalizer (auxiliaryProduct Z Y) := by
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => ha.trans_le ht.1
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) MeasureTheory.volume a b :=
    (continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')).intervalIntegrable
  calc
    _ = ∫ t : ℝ in a..b, (1 / t) / (2 * A) - 1 := by
      rw [intervalIntegral.integral_sub (hinv.div_const _) intervalIntegrable_const,
        intervalIntegral.integral_div, integral_one_div (by
          intro ht
          exact (hpos 0 ht).false),
        Real.log_div (ha.trans_le hab).ne' ha.ne']
      simp
    _ ≤ ∫ t : ℝ in a..b, divisorEulerMoment (auxiliaryProduct Z Y) (-t) - 1 := by
      apply intervalIntegral.integral_mono_on hab
        ((hinv.div_const _).sub intervalIntegrable_const)
        (((continuous_divisorEulerMoment _).sub continuous_const).intervalIntegrable a b)
      intro t ht
      have htpos := ha.trans_le ht.1
      have htscale : 1 ≤ t * Real.log ((Y : ℝ) + 1) :=
        hscale.trans (mul_le_mul_of_nonneg_right ht.1
          (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg Y))))
      calc
        (1 / t) / (2 * A) - 1 = 1 / (2 * t * A) - 1 := by ring
        _ ≤ _ := sub_le_sub_right (divisorEulerMoment_lower hZY htpos hA hZA htscale) 1
    _ ≤ normalizer (auxiliaryProduct Z Y) :=
      normalizer_integral_le (auxiliaryProduct_pos Z Y).ne' ha.le b

/-- A logarithmic lower bound for the auxiliary normalizer. -/
lemma normalizer_lower_bound {Z Y : ℕ} (hZY : Z ≤ Y) {A : ℝ}
    (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hAY : A ≤ Real.log ((Y : ℝ) + 1)) :
    Real.log (Real.log ((Y : ℝ) + 1)) - Real.log A - 2 ≤
      2 * A * normalizer (auxiliaryProduct Z Y) := by
  have hlog : 0 < Real.log ((Y : ℝ) + 1) := hA.trans_le hAY
  have h := normalizer_lower_integral hZY hA (one_div_pos.mpr hlog)
    (one_div_le_one_div_of_le hA hAY) hZA
    (by rw [one_div_mul_cancel hlog.ne'])
  simp only [one_div, Real.log_inv] at h
  have hmul := (div_le_iff₀ (show 0 < 2 * A by positivity)).mp
    (sub_le_iff_le_add.mp h)
  nlinarith [mul_inv_cancel₀ hA.ne',
    mul_nonneg hA.le (inv_nonneg.mpr hlog.le)]

/-- A nontrivial coefficient has absolute value `1 / (normalizer P * log d)`. -/
lemma abs_coefficient_eq {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    |coefficient P d| = 1 / (normalizer P * Real.log d) := by
  rw [abs_of_neg (coefficient_neg hP hd), coefficient, if_neg (ne_of_gt hd)]
  ring

/-- Splitting at Y gives the tilted absolute-moment bound in (3.6). -/
theorem coefficientAbsMoment_le {P Y : ℕ} (hP : 1 < P) (hY : 1 < Y)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hYE : (Y : ℝ) ^ γ ≤ E) :
    coefficientAbsMoment P γ ≤ E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by
  have hB : 0 < normalizer P := normalizer_pos hP
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hden : 0 < normalizer P * Real.log Y := mul_pos hB hlogY
  have hE : 0 ≤ E := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hYE
  have hpoint (d : ℕ) (hd : d ∈ P.divisors.erase 1) :
      |coefficient P d| * (d : ℝ) ^ γ / d.totient ≤
        E * (|coefficient P d| / d.totient) +
          (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient) := by
    have hd1 := one_lt_of_mem_divisors_erase_one hd
    have hf : 0 ≤ |coefficient P d| / (d.totient : ℝ) :=
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    have hg : 0 ≤ (d : ℝ) ^ γ / d.totient :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    by_cases hdY : d ≤ Y
    · have hpow : (d : ℝ) ^ γ ≤ E :=
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdY) hγ).trans hYE
      calc
        _ = (|coefficient P d| / d.totient) * (d : ℝ) ^ γ := by ring
        _ ≤ (|coefficient P d| / d.totient) * E := mul_le_mul_of_nonneg_left hpow hf
        _ ≤ _ := by nlinarith [mul_nonneg (one_div_nonneg.mpr hden.le) hg]
    · have hac : |coefficient P d| ≤ 1 / (normalizer P * Real.log Y) := by
        rw [abs_coefficient_eq hP hd1]
        apply one_div_le_one_div_of_le hden
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < Y))
            (by exact_mod_cast (by omega : Y ≤ d))) hB.le
      calc
        _ = |coefficient P d| * ((d : ℝ) ^ γ / d.totient) := by ring
        _ ≤ (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient) :=
          mul_le_mul_of_nonneg_right hac hg
        _ ≤ _ := by nlinarith [mul_nonneg hE hf]
  have hsmall : (∑ d ∈ P.divisors.erase 1, |coefficient P d| / d.totient) = 1 := by
    simpa [coefficientAbsMoment] using coefficientAbsMoment_zero hP
  have hlarge : (∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ γ / d.totient) ≤ divisorEulerMoment P γ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun d _ _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
  calc
    coefficientAbsMoment P γ ≤ ∑ d ∈ P.divisors.erase 1,
        (E * (|coefficient P d| / d.totient) +
          (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient)) :=
      Finset.sum_le_sum hpoint
    _ = E + (1 / (normalizer P * Real.log Y)) *
        ∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ γ / d.totient := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsmall, mul_one]
    _ ≤ E + (1 / (normalizer P * Real.log Y)) * divisorEulerMoment P γ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hlarge (one_div_nonneg.mpr hden.le))
    _ = E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by ring

/-- At exponent zero, the auxiliary divisor moment is an Euler-product ratio. -/
lemma divisorEulerMoment_zero_factorization {Z Y : ℕ} (hZY : Z ≤ Y) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 * eulerProduct Z 1 = eulerProduct Y 1 := by
  rw [auxiliaryProduct, divisorEulerMoment_primeProduct _
    (fun _ hp => auxiliaryPrimes_prime hp)]
  convert auxiliary_euler_factorization hZY (1 : ℝ) using 2
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (auxiliaryPrimes_prime hp).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (auxiliaryPrimes_prime hp).ne_one)
  simp only [Real.rpow_zero, Real.rpow_neg_one]
  field_simp
  ring

/-- Bound the auxiliary zero moment by a ratio of logarithms. -/
lemma divisorEulerMoment_zero_le {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      Real.exp 6 * (1 + Real.log Y) / Real.log Z := by
  have hlog : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) (divisorEulerMoment_nonneg _ _)
    _ = eulerProduct Y 1 := divisorEulerMoment_zero_factorization hZY
    _ ≤ Real.exp 6 * (1 + Real.log Y) := eulerProduct_one_le (hZ.trans hZY)

/-- An exponential bound for tilting a squarefree Euler factor. -/
lemma squarefree_euler_factor_tilt {p γ E : ℝ} (hp : 1 < p)
    (hγ : 0 ≤ γ) (hpE : p ^ γ ≤ E) :
    1 + p ^ γ / (p - 1) ≤
      (1 + 1 / (p - 1)) * Real.exp (E * γ * Real.log p / p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hlog : 0 ≤ Real.log p := (Real.log_pos hp).le
  have hdiff : p ^ γ - 1 ≤ E * γ * Real.log p := by
    have h := rpow_sub_one_le (γ := γ) hp0
    have hmul := mul_le_mul_of_nonneg_right hpE (mul_nonneg hγ hlog)
    nlinarith
  have hexp : 1 + (p ^ γ - 1) / p ≤ Real.exp (E * γ * Real.log p / p) := by
    calc
      _ ≤ 1 + E * γ * Real.log p / p :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hdiff hp0.le)
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (E * γ * Real.log p / p)
  have he : 1 + p ^ γ / (p - 1) = (1 + 1 / (p - 1)) * (1 + (p ^ γ - 1) / p) := by
    field_simp [ne_of_gt hp0, ne_of_gt hpm]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Tilting a squarefree divisor moment costs an exponential factor. -/
lemma divisorEulerMoment_tilt (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hE : ∀ p ∈ ps, (p : ℝ) ^ γ ≤ E) :
    divisorEulerMoment (∏ p ∈ ps, p) γ ≤
      divisorEulerMoment (∏ p ∈ ps, p) 0 *
        Real.exp (E * γ * ∑ p ∈ ps, Real.log p / p) := by
  have h := Finset.prod_le_prod (s := ps)
    (f := fun p : ℕ => 1 + (p : ℝ) ^ γ / ((p : ℝ) - 1))
    (g := fun p : ℕ => (1 + 1 / ((p : ℝ) - 1)) * Real.exp (E * γ * Real.log p / p))
    (fun p hp => by
      have hpm : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (hps p hp).one_lt)
      positivity)
    (fun p hp => squarefree_euler_factor_tilt (by exact_mod_cast (hps p hp).one_lt) hγ (hE p hp))
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at h
  have he : (∑ p ∈ ps, E * γ * Real.log p / p) = E * γ * ∑ p ∈ ps, Real.log p / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simpa only [divisorEulerMoment_primeProduct ps hps, Real.rpow_zero, he] using h

/-- Uniformly bound the cost of tilting the auxiliary divisor moment. -/
lemma auxiliary_divisorEulerMoment_tilt {Z Y : ℕ} (hY : 2 ≤ Y)
    {γ : ℝ} (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) := by
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by linarith [hscale])
  have hlog4 : Real.log 4 ≤ 2 * Real.log Y := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (Y : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) ≤ 3 * Real.log Y := by
    calc
      _ ≤ ∑ p ∈ Y.primesLE, Real.log p / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun p hp _ => div_nonneg (Nat.mem_primesLE.mp hp).2.log_pos.le
            (Nat.cast_nonneg p))
      _ ≤ 3 * Real.log Y := by
        linarith [sum_prime_log_div_le (by omega : 1 ≤ Y)]
  have hcost : γ * (∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hsum hγ]
  calc
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 *
        Real.exp (Real.exp 2 * γ * ∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) :=
      divisorEulerMoment_tilt (auxiliaryPrimes Z Y) (fun _ hp => auxiliaryPrimes_prime hp)
        hγ (fun p hp => (Real.rpow_le_rpow (Nat.cast_nonneg p)
          (by exact_mod_cast (mem_auxiliaryPrimes.mp hp).2.2) hγ).trans hYE)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg 2)]))
      (divisorEulerMoment_nonneg _ _)

/-- Every prime divisor of the auxiliary product is an auxiliary prime. -/
lemma prime_dvd_auxiliaryProduct {Z Y p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ auxiliaryProduct Z Y) : p ∈ auxiliaryPrimes Z Y := by
  obtain ⟨q, hq, hpq⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp hdvd
  exact ((Nat.prime_dvd_prime_iff_eq hp (auxiliaryPrimes_prime hq)).mp hpq).symm ▸ hq

/-- Every nontrivial auxiliary divisor exceeds the lower cutoff `Z`. -/
lemma auxiliary_divisor_gt {Z Y d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors.erase 1) :
    Z < d := by
  obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpP := prime_dvd_auxiliaryProduct hp (hpd.trans (Nat.mem_divisors.mp hd).1)
  exact (mem_auxiliaryPrimes.mp hpP).2.1.trans_le
    (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hpd)

/-- A normalizer lower bound makes every auxiliary coefficient at most one in magnitude. -/
lemma auxiliary_coefficient_le_one {Z Y : ℕ} (hP : 1 < auxiliaryProduct Z Y)
    (hZ : 1 < Z) (hB : 1 ≤ normalizer (auxiliaryProduct Z Y) * Real.log Z)
    {d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors) :
    |coefficient (auxiliaryProduct Z Y) d| ≤ 1 := by
  by_cases hd1 : d = 1
  · simp [hd1, coefficient]
  have hZd := auxiliary_divisor_gt (Finset.mem_erase.mpr ⟨hd1, hd⟩)
  rw [abs_coefficient_eq hP (hZ.trans hZd)]
  have hden : 1 ≤ normalizer (auxiliaryProduct Z Y) * Real.log d :=
    hB.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans hZ))
        (by exact_mod_cast hZd.le)) (normalizer_pos hP).le)
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden

/-- An explicit absolute moment bound from a lower bound on the normalizer. -/
def absoluteMomentBound (b : ℝ) : ℝ :=
  Real.exp 2 + 2 * Real.exp 6 * Real.exp (6 * Real.exp 2) / b

/-- The absolute moment bound divided by the normalizer lower bound. -/
def coefficientControl (b : ℝ) : ℝ := absoluteMomentBound b / b

/-- The absolute moment bound is positive for positive `b`. -/
lemma absoluteMomentBound_pos {b : ℝ} (hb : 0 < b) : 0 < absoluteMomentBound b := by
  unfold absoluteMomentBound
  positivity

/-- The coefficient control constant is positive for positive `b`. -/
lemma coefficientControl_pos {b : ℝ} (hb : 0 < b) : 0 < coefficientControl b :=
  div_pos (absoluteMomentBound_pos hb) hb

/-- Bound the auxiliary absolute moment by `absoluteMomentBound`. -/
lemma auxiliary_coefficientAbsMoment_le {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤ absoluteMomentBound b := by
  have hY : 1 < Y := by omega
  have hlogY : 1 ≤ Real.log (Y : ℝ) :=
    hlogZ.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < Z))
      (by exact_mod_cast hZY))
  have hlogYpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < Y))]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hscale)
  have hzero : divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      2 * Real.exp 6 * Real.log Y := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log Y) / Real.log Z :=
        divisorEulerMoment_zero_le hZY hZ
      _ ≤ Real.exp 6 * (1 + Real.log Y) := div_le_self (by positivity) hlogZ
      _ ≤ 2 * Real.exp 6 * Real.log Y := by nlinarith [Real.exp_pos 6]
  have hmoment : divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      (2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y := by
    calc
      _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) :=
        auxiliary_divisorEulerMoment_tilt (hZ.trans hZY) hγ hscale
      _ ≤ (2 * Real.exp 6 * Real.log Y) * Real.exp (6 * Real.exp 2) :=
        mul_le_mul_of_nonneg_right hzero (Real.exp_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ Real.exp 2 + divisorEulerMoment (auxiliaryProduct Z Y) γ /
        (normalizer (auxiliaryProduct Z Y) * Real.log Y) :=
      coefficientAbsMoment_le hP hY hγ hYE
    _ ≤ Real.exp 2 +
        ((2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y) /
          (b * Real.log Y) := by
      gcongr
    _ = absoluteMomentBound b := by
      unfold absoluteMomentBound
      rw [mul_div_mul_right _ _ hlogYpos.ne']

/-- Bound the auxiliary absolute moment by a constant times the normalizer. -/
lemma auxiliary_coefficientAbsMoment_control {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤
      coefficientControl b * normalizer (auxiliaryProduct Z Y) := by
  calc
    _ ≤ absoluteMomentBound b := auxiliary_coefficientAbsMoment_le hZY hZ hlogZ hP hb hB hγ hscale
    _ = coefficientControl b * b := by
      rw [coefficientControl, div_mul_cancel₀ _ (ne_of_gt hb)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (coefficientControl_pos hb).le

/-- The auxiliary prime ranges of Section 3.1, with integral endpoints. -/
def sieveZ (x : ℝ) : ℕ := ⌊x ^ 6⌋₊

/-- The logarithmic upper cutoff `x / (log x)^5` for the sieve primes. -/
def sieveUpperLog (x : ℝ) : ℝ := x / (Real.log x) ^ 5

/-- The upper sieve cutoff, rounded down to an integer. -/
def sieveY (x : ℝ) : ℕ := ⌊Real.exp (sieveUpperLog x)⌋₊

/-- The product of primes between the two sieve cutoffs. -/
def sieveP (x : ℝ) : ℕ := auxiliaryProduct (sieveZ x) (sieveY x)

/-- A fixed positive lower bound used for the sieve normalizer. -/
def normalizerLower : ℝ := 1 / (100 * Real.exp 6)

/-- The fixed normalizer lower bound is positive. -/
lemma normalizerLower_pos : 0 < normalizerLower := by
  unfold normalizerLower
  positivity

/-- Explicit size bounds ensure ordered cutoffs and a uniform normalizer lower bound. -/
lemma sieve_normalizer_lower_of_bounds {x : ℝ} (hx : 0 < x)
    (hlx : 1 ≤ Real.log x) (hZ : 2 ≤ sieveZ x)
    (hlarge : 7 * Real.exp 6 * (Real.log x) ^ 6 ≤ x)
    (hsmall : 6 * Real.log (Real.log x) + Real.log 7 + 8 ≤ Real.log x / 2) :
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by
  have hlxpos : 0 < Real.log x := zero_lt_one.trans_le hlx
  have hexp : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hscale : 7 * Real.exp 6 * Real.log x ≤ sieveUpperLog x := by
    apply (le_div_iff₀ (pow_pos hlxpos 5)).mpr
    nlinarith [hlarge]
  have hZY : sieveZ x ≤ sieveY x := by
    apply Nat.floor_le_floor
    calc
      x ^ 6 = Real.exp (6 * Real.log x) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hx] using
          (Real.exp_nat_mul (Real.log x) 6).symm
      _ ≤ Real.exp (sieveUpperLog x) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hexp hlxpos.le])
  refine ⟨hZY, ?_⟩
  have hlogZ : Real.log (sieveZ x) ≤ 6 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 6) := Real.log_le_log
        (by exact_mod_cast (by omega : 0 < sieveZ x)) (Nat.floor_le (by positivity))
      _ = _ := by rw [Real.log_pow]; norm_num
  have hZA : eulerProduct (sieveZ x) 1 ≤ 7 * Real.exp 6 * Real.log x := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (sieveZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * (7 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg 6)
      _ = _ := by ring
  have hYlog : sieveUpperLog x ≤ Real.log ((sieveY x : ℝ) + 1) := by
    calc
      _ = Real.log (Real.exp (sieveUpperLog x)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (Nat.lt_floor_add_one _).le
  have hApos : 0 < 7 * Real.exp 6 * Real.log x := by positivity
  have hbound := normalizer_lower_bound hZY hApos hZA (hscale.trans hYlog)
  have hloglog : Real.log x - 5 * Real.log (Real.log x) ≤
      Real.log (Real.log ((sieveY x : ℝ) + 1)) := by
    calc
      _ = Real.log (sieveUpperLog x) := by
        rw [sieveUpperLog, Real.log_div hx.ne' (pow_pos hlxpos 5).ne', Real.log_pow]
        norm_num
      _ ≤ _ := Real.log_le_log (hApos.trans_le hscale) hYlog
  have hlogA : Real.log (7 * Real.exp 6 * Real.log x) =
      Real.log 7 + 6 + Real.log (Real.log x) := by
    rw [Real.log_mul (by positivity : (7 * Real.exp 6 : ℝ) ≠ 0) hlxpos.ne',
      Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (Real.exp_ne_zero 6), Real.log_exp]
  rw [hlogA] at hbound
  have hlower : Real.log x / 2 ≤
      2 * (7 * Real.exp 6 * Real.log x) * normalizer (sieveP x) := by
    change _ ≤ 2 * (7 * Real.exp 6 * Real.log x) *
      normalizer (auxiliaryProduct (sieveZ x) (sieveY x))
    linarith
  unfold normalizerLower
  apply (div_le_iff₀ (by positivity : 0 < 100 * Real.exp 6)).mpr
  nlinarith

/-- The lower sieve cutoff tends to infinity. -/
lemma tendsto_sieveZ : Filter.Tendsto sieveZ Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp (Filter.tendsto_pow_atTop (by decide : (6 : ℕ) ≠ 0))

/-- The logarithm of the lower sieve cutoff tends to infinity. -/
lemma tendsto_log_sieveZ :
    Filter.Tendsto (fun x : ℝ => Real.log (sieveZ x)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_sieveZ)

/-- The unconditional positive lower bound for B for the paper's parameters. -/
theorem eventually_sieve_normalizer_lower : ∀ᶠ x : ℝ in Filter.atTop,
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by
  have hpow : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 6 / x)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_sieveZ.eventually_ge_atTop 2,
    hpow.eventually_le_const (by positivity : (0 : ℝ) < 1 / (7 * Real.exp 6)),
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 24),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * (Real.log 7 + 8))]
    with x hx hlx hZ hpow hlog hconst
  apply sieve_normalizer_lower_of_bounds hx hlx hZ
  · simpa [mul_comm] using
      (div_le_div_iff₀ hx (by positivity : 0 < 7 * Real.exp 6)).mp hpow
  · have h := (div_le_iff₀ (zero_lt_one.trans_le hlx)).mp hlog
    linarith

end

end LongGapsBetweenPrimes

/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact prefix-lcm power decomposition and unconditional endpoint corrections. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect
import D5.S3.Analytic.Zeta.EulerLogBridge
import Mathlib.Tactic

/-! Exact prime-power and logarithmic identities for the real-power divisor transform. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction

namespace D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

private def sigmaPower (κ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (ArithmeticFunction.sigma 1 n : ℝ) ^ κ, by simp⟩

/-- The real-power divisor transform. -/
def sigmaKappa (κ : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) *
    (ArithmeticFunction.sigma 1 d : ℝ) ^ κ

/-- The normalized real-power divisor ratio. -/
def G (κ : ℝ) (n : ℕ) : ℝ :=
  (riemannZeta (κ : ℂ)).re * sigmaKappa κ n /
    (Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)) ^ κ

/-- Primes not exceeding the real cutoff. -/
def primeCutoff (x : ℝ) : Finset ℕ := (Ioc 0 ⌊x⌋₊).filter Nat.Prime

/-- The Mertens correction measured at the prime clock. -/
def B (x : ℝ) : ℝ := Real.eulerMascheroniConstant +
  Real.log (Real.log (Chebyshev.theta x)) +
    ∑ p ∈ primeCutoff x, Real.log (1 - 1 / (p : ℝ))

/-- The omitted terminal layers in the ordinary divisor ratio. -/
def A (x : ℝ) : ℝ :=
  -∑ p ∈ primeCutoff x, Real.log (1 - 1 / (p : ℝ) ^ (p.log ⌊x⌋₊ + 1))

/-- The change from the prime clock to the prime-power clock. -/
def J (x : ℝ) : ℝ :=
  Real.log (Real.log (Chebyshev.psi x)) - Real.log (Real.log (Chebyshev.theta x))

/-- The logarithm of the missing Euler factors. -/
def T (κ x : ℝ) : ℝ := Real.log (riemannZeta (κ : ℂ)).re +
  ∑ p ∈ primeCutoff x, Real.log (1 - (p : ℝ) ^ (-κ))

/-- The ratio of successive prime-power divisor sums. -/
private def localRatio (p a : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 (p ^ (a - 1)) : ℝ) /
    (ArithmeticFunction.sigma 1 (p ^ a) : ℝ)

/-- The nonnegative correction from the exact successive-power ratio. -/
def C (κ x : ℝ) : ℝ := ∑ p ∈ primeCutoff x,
  Real.log ((1 - localRatio p (p.log ⌊x⌋₊) ^ κ) /
    (1 - (p : ℝ) ^ (-κ)))

private lemma sigmaPower_apply {κ : ℝ} {n : ℕ} (hn : n ≠ 0) :
    sigmaPower κ n = (ArithmeticFunction.sigma 1 n : ℝ) ^ κ := by
  simp [sigmaPower, hn]

private lemma sigmaKappa_eq_convolution (κ : ℝ) (n : ℕ) :
    sigmaKappa κ n =
      ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * sigmaPower κ) n := by
  rw [ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply]
  rw [
    Nat.sum_divisorsAntidiagonal' (fun i j =>
      (ArithmeticFunction.moebius i : ℝ) * sigmaPower κ j)]
  unfold sigmaKappa
  apply sum_congr rfl
  intro d hd
  rw [sigmaPower_apply (Nat.pos_of_mem_divisors hd).ne']

private lemma sigmaPower_multiplicative (κ : ℝ) :
    (sigmaPower κ).IsMultiplicative := by
  constructor
  · simp [sigmaPower]
  · intro m n hmn
    by_cases hm : m = 0
    · subst m; simp [sigmaPower]
    by_cases hn : n = 0
    · subst n; simp [sigmaPower]
    rw [sigmaPower_apply (Nat.mul_ne_zero hm hn), sigmaPower_apply hm,
      sigmaPower_apply hn, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn,
      Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

private lemma sigmaKappa_multiplicative (κ : ℝ) :
    (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * sigmaPower κ)).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul (sigmaPower_multiplicative κ)

private lemma sigmaKappa_sum_divisors (κ : ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, sigmaKappa κ d) = sigmaPower κ n := by
  simp_rw [sigmaKappa_eq_convolution]
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ← mul_assoc,
    ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

private lemma sigmaKappa_prime_power (κ : ℝ) {p a : ℕ} (hp : p.Prime) :
    sigmaKappa κ (p ^ (a + 1)) =
      (ArithmeticFunction.sigma 1 (p ^ (a + 1)) : ℝ) ^ κ -
        (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) ^ κ := by
  have ha := sigmaKappa_sum_divisors κ (p ^ a)
  have hb := sigmaKappa_sum_divisors κ (p ^ (a + 1))
  rw [Nat.sum_divisors_prime_pow hp, sigmaPower_apply (pow_ne_zero a hp.ne_zero)] at ha
  rw [Nat.sum_divisors_prime_pow hp,
    sigmaPower_apply (pow_ne_zero (a + 1) hp.ne_zero), sum_range_succ] at hb
  linarith

private lemma sigmaKappa_factorization (κ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    sigmaKappa κ n = ∏ p ∈ n.primeFactors, sigmaKappa κ (p ^ n.factorization p) := by
  simp_rw [sigmaKappa_eq_convolution]
  rw [(sigmaKappa_multiplicative κ).multiplicative_factorization _ hn,
    Nat.prod_factorization_eq_prod_primeFactors]

private lemma sigma_prime_power_recurrence {p a : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ (a + 1)) =
      p * ArithmeticFunction.sigma 1 (p ^ a) + 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,
    ArithmeticFunction.sigma_one_apply_prime_pow hp, geom_sum_succ]

private lemma localRatio_bounds {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < localRatio p a ∧ localRatio p a < 1 / (p : ℝ) := by
  have hpa : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have hprev : p ^ (a - 1) ≠ 0 := pow_ne_zero (a - 1) hp.ne_zero
  have hS : 0 < (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 _ hpa
  have hP : 0 < (ArithmeticFunction.sigma 1 (p ^ (a - 1)) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 _ hprev
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr := sigma_prime_power_recurrence (a := a - 1) hp
  have he : a - 1 + 1 = a := by omega
  rw [he] at hr
  have hr' : (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) =
      p * (ArithmeticFunction.sigma 1 (p ^ (a - 1)) : ℝ) + 1 := by exact_mod_cast hr
  refine ⟨div_pos hP hS, ?_⟩
  dsimp [localRatio]
  exact (div_lt_div_iff₀ hS hp0).mpr (by linarith)

private lemma sigmaKappa_prime_power_pos {κ : ℝ} (hκ : 0 < κ) {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) : 0 < sigmaKappa κ (p ^ a) := by
  have he : a - 1 + 1 = a := by omega
  have hform := sigmaKappa_prime_power κ (a := a - 1) hp
  rw [he] at hform
  rw [hform]
  have hp1 : 1 < p := hp.one_lt
  have hprev : 0 < ArithmeticFunction.sigma 1 (p ^ (a - 1)) :=
    ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)
  have hr := sigma_prime_power_recurrence (a := a - 1) hp
  rw [he] at hr
  apply sub_pos.mpr
  apply Real.rpow_lt_rpow (Nat.cast_nonneg _) ?_ hκ
  exact_mod_cast (show ArithmeticFunction.sigma 1 (p ^ (a - 1)) <
    ArithmeticFunction.sigma 1 (p ^ a) by nlinarith)

private lemma sigmaKappa_pos {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : n ≠ 0) :
    0 < sigmaKappa κ n := by
  rw [sigmaKappa_factorization κ hn]
  apply prod_pos
  intro p hp
  exact sigmaKappa_prime_power_pos hκ (Nat.prime_of_mem_primeFactors hp)
    (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
      (Nat.dvd_of_mem_primeFactors hp))

private lemma localRatio_rpow_bounds {κ : ℝ} (hκ : 0 < κ) {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) :
    0 ≤ localRatio p a ^ κ ∧ localRatio p a ^ κ < (p : ℝ) ^ (-κ) ∧
      (p : ℝ) ^ (-κ) < 1 := by
  have hb := localRatio_bounds hp ha
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have he : (1 / (p : ℝ)) ^ κ = (p : ℝ) ^ (-κ) := by
    rw [one_div, Real.inv_rpow hp0.le, Real.rpow_neg hp0.le]
  refine ⟨Real.rpow_nonneg hb.1.le _, ?_, ?_⟩
  · rw [← he]
    exact Real.rpow_lt_rpow hb.1.le hb.2 hκ
  · rw [← he]
    exact Real.rpow_lt_one (by positivity) ((div_lt_one hp0).mpr hp1) hκ

/-- The exact local correction has a nonnegative logarithm. -/
theorem C_nonneg {κ : ℝ} (hκ : 0 < κ) (x : ℝ) : 0 ≤ C κ x := by
  apply sum_nonneg
  intro p hp
  have hprime := (mem_filter.mp hp).2
  have hpn := (mem_Ioc.mp (mem_filter.mp hp).1).2
  have hb := localRatio_rpow_bounds hκ hprime (Nat.log_pos hprime.one_lt hpn)
  have hd : 0 < 1 - (p : ℝ) ^ (-κ) := sub_pos.mpr hb.2.2
  apply Real.log_nonneg
  exact (le_div_iff₀ hd).mpr (by linarith [hb.2.1])

private lemma C_eq_log_difference {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    C κ x = (∑ p ∈ primeCutoff x, Real.log (1 - localRatio p (p.log ⌊x⌋₊) ^ κ)) -
      ∑ p ∈ primeCutoff x, Real.log (1 - (p : ℝ) ^ (-κ)) := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime := (mem_filter.mp hp).2
  have hpn := (mem_Ioc.mp (mem_filter.mp hp).1).2
  have hb := localRatio_rpow_bounds hκ hprime (Nat.log_pos hprime.one_lt hpn)
  exact Real.log_div (sub_pos.mpr (hb.2.1.trans hb.2.2)).ne'
    (sub_pos.mpr hb.2.2).ne'

private lemma log_sigmaKappa_prime_power {κ : ℝ} (hκ : 0 < κ) {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) :
    Real.log (sigmaKappa κ (p ^ a)) =
      κ * Real.log (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) +
        Real.log (1 - localRatio p a ^ κ) := by
  have hS : 0 < (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)
  have hP : 0 ≤ (ArithmeticFunction.sigma 1 (p ^ (a - 1)) : ℝ) := by positivity
  have hb := localRatio_rpow_bounds hκ hp ha
  have hlocal : 0 < 1 - localRatio p a ^ κ := sub_pos.mpr (hb.2.1.trans hb.2.2)
  have he : a - 1 + 1 = a := by omega
  have hf := sigmaKappa_prime_power κ (a := a - 1) hp
  rw [he] at hf
  have hfactor : sigmaKappa κ (p ^ a) =
      (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) ^ κ * (1 - localRatio p a ^ κ) := by
    rw [hf, localRatio, Real.div_rpow hP hS.le]
    field_simp [(Real.rpow_pos_of_pos hS κ).ne']
    <;> ring
  rw [hfactor, Real.log_mul (Real.rpow_pos_of_pos hS κ).ne' hlocal.ne',
    Real.log_rpow hS]

private lemma log_sigmaKappa_lcm {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    Real.log (sigmaKappa κ (Nat.lcmUpto ⌊x⌋₊)) =
      κ * Real.log (ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℝ) +
        ∑ p ∈ primeCutoff x, Real.log (1 - localRatio p (p.log ⌊x⌋₊) ^ κ) := by
  let n := Nat.lcmUpto ⌊x⌋₊
  have hn := Nat.lcmUpto_ne_zero ⌊x⌋₊
  have hfactor := sigmaKappa_factorization κ hn
  have hsig := ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization
    (ArithmeticFunction.sigma 1) hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hsig
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) := Nat.prime_of_mem_primeFactors hp
  have hval (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p :=
    (hprime p hp).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  rw [hfactor, Real.log_prod (fun p hp =>
    (sigmaKappa_prime_power_pos hκ (hprime p hp) (hval p hp)).ne')]
  rw [hsig, Nat.cast_prod, Real.log_prod (fun p hp => by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 _
      (pow_ne_zero _ (hprime p hp).ne_zero)).ne')]
  rw [mul_sum]
  have he := Finset.sum_congr rfl (fun p hp =>
    log_sigmaKappa_prime_power hκ (hprime p hp) (hval p hp))
  rw [he, sum_add_distrib]
  congr 1
  dsimp [n]
  rw [Nat.primeFactors_lcmUpto, Nat.primesLE_eq_filter_Ioc_zero]
  apply sum_congr rfl
  intro p hp
  rw [Nat.factorization_lcmUpto _ (mem_filter.mp hp).2]

private lemma log_sigma_ratio (x : ℝ) :
    Real.log ((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℝ) /
      (Nat.lcmUpto ⌊x⌋₊ : ℝ)) =
      -A x - ∑ p ∈ primeCutoff x, Real.log (1 - 1 / (p : ℝ)) := by
  let n := ⌊x⌋₊
  have hn := Nat.lcmUpto_pos n
  have hf := D5.S3.Arith.GoldenResourceObjectiveFactorization.golden_resource_objective_factorization
    0 hn
  rw [D5.S3.Arith.GoldenResourceOptimalInteger.golden_resource_sigma_identity 0 hn,
    zero_mul, sub_zero] at hf
  rw [hf, Nat.primeFactors_lcmUpto, Nat.primesLE_eq_filter_Ioc_zero]
  change (∑ p ∈ primeCutoff x,
    D5.S3.Arith.GoldenLocalThreshold.goldenPrimeLocalObjective 0 p
      ((Nat.lcmUpto n).factorization p)) = _
  unfold A
  rw [neg_neg, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime := (mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hi1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hnum : 0 < 1 - (p : ℝ)⁻¹ ^ (p.log n + 1) :=
    sub_pos.mpr (pow_lt_one₀ hi0.le hi1 (by omega))
  have hden : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr hi1
  simp only [D5.S3.Arith.GoldenLocalThreshold.goldenPrimeLocalObjective,
    zero_mul, sub_zero, Nat.factorization_lcmUpto n hprime]
  rw [Real.log_div hnum.ne' hden.ne']
  simp only [inv_pow, one_div, n]

/-- The actual normalized divisor transform is positive above the logarithmic clock cutoff. -/
theorem G_pos {κ x : ℝ} (hκ : 1 < κ) (hpsi : 1 < Chebyshev.psi x) :
    0 < G κ (Nat.lcmUpto ⌊x⌋₊) := by
  have hn : 0 < (Nat.lcmUpto ⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.lcmUpto_pos ⌊x⌋₊
  have hlog : Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  apply div_pos
  · exact mul_pos (riemannZeta_re_pos_of_one_lt hκ)
      (sigmaKappa_pos (by linarith) (Nat.lcmUpto_ne_zero _))
  · apply Real.rpow_pos_of_pos
    exact mul_pos (mul_pos (Real.exp_pos _) hn) (by rw [hlog]; exact Real.log_pos hpsi)

/-- The exact logarithmic decomposition of the normalized prefix-lcm transform. -/
theorem log_G_decomposition {κ x : ℝ} (hκ : 1 < κ) (hpsi : 1 < Chebyshev.psi x) :
    Real.log (G κ (Nat.lcmUpto ⌊x⌋₊)) =
      -κ * B x - κ * A x - κ * J x + T κ x + C κ x := by
  have hk : 0 < κ := by linarith
  have hn : 0 < (Nat.lcmUpto ⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.lcmUpto_pos ⌊x⌋₊
  have hs : 0 < (ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (Nat.lcmUpto_ne_zero _)
  have hsig := sigmaKappa_pos hk (Nat.lcmUpto_ne_zero ⌊x⌋₊)
  have hz := riemannZeta_re_pos_of_one_lt hκ
  have hlog : Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have hll : 0 < Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ)) := by
    rw [hlog]; exact Real.log_pos hpsi
  have hb : 0 < Real.exp Real.eulerMascheroniConstant *
      (Nat.lcmUpto ⌊x⌋₊ : ℝ) * Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ)) := by positivity
  have hordinary := log_sigma_ratio x
  rw [Real.log_div hs.ne' hn.ne', hlog] at hordinary
  rw [G, Real.log_div (mul_pos hz hsig).ne' (Real.rpow_pos_of_pos hb κ).ne',
    Real.log_mul hz.ne' hsig.ne', Real.log_rpow hb,
    Real.log_mul (mul_pos (Real.exp_pos _) hn).ne' hll.ne',
    Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp,
    log_sigmaKappa_lcm hk, hlog, C_eq_log_difference hk]
  unfold B J T
  linear_combination κ * hordinary


open Filter
open scoped Topology
private lemma linear_clock_data {f : ℝ → ℝ}
    (hf : Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) :
    (∀ᶠ x : ℝ in atTop, 1 < f x) ∧
    Tendsto (fun x : ℝ => Real.log (f x) / Real.log x) atTop (𝓝 1) := by
  have hhalf := hf.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hpos : ∀ᶠ x : ℝ in atTop, 1 < f x := by
    filter_upwards [hhalf, eventually_gt_atTop (2 : ℝ)] with x hx hx2
    have hx0 : 0 < x := by linarith
    have := (lt_div_iff₀ hx0).mp hx
    linarith
  have hlog : Tendsto (fun x : ℝ => Real.log (f x / x)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hf
  have hzero := hlog.div_atTop Real.tendsto_log_atTop
  refine ⟨hpos, ?_⟩
  have hh := hzero.add_const 1
  simp only [zero_add] at hh
  refine hh.congr' ?_
  filter_upwards [hpos, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.log_div (by linarith : f x ≠ 0) (by linarith : x ≠ 0)]
  field_simp [(Real.log_pos hx1).ne']
  <;> ring

/-- The clock displacement is asymptotic to one at the root-log scale. -/
theorem J_scaled_limit :
    Tendsto (fun x : ℝ => (Real.sqrt x * Real.log x) * J x)
      atTop (𝓝 1) := by
  have hp := EulerLayerRootCorrection.prime_number_limits.1
  have ht := EulerLayerRootCorrection.prime_number_limits.2
  have hpd := linear_clock_data hp
  have htd := linear_clock_data ht
  have hroot := EulerLayerRootCorrection.psi_theta_root_limit
  have hdenp := hp.mul hpd.2
  have hdent := ht.mul htd.2
  have hlow := hroot.div hdenp (by norm_num : (1 : ℝ) * 1 ≠ 0)
  have hupp := hroot.div hdent (by norm_num : (1 : ℝ) * 1 ≠ 0)
  norm_num only [one_mul, div_one] at hlow hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [hpd.1, htd.1, eventually_gt_atTop (1 : ℝ)] with x hpsi htheta hx
    have hx0 : 0 < x := by linarith
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hl : 0 < Real.log x := Real.log_pos hx
    have hD : 0 ≤ Real.sqrt x * Real.log x := by positivity
    have hineq : (Chebyshev.psi x - Chebyshev.theta x) /
        (Chebyshev.psi x * Real.log (Chebyshev.psi x)) ≤ J x := by
      by_cases heq : Chebyshev.psi x = Chebyshev.theta x
      · simp [J, heq]
      · have hh := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
          hpsi htheta heq
        dsimp [D5.S3.Arith.Robin.ActualRobinClockCovariance.g] at hh
        dsimp [J]
        have hn := neg_le_neg hh.le
        convert hn using 1 <;> ring
    have hh := mul_le_mul_of_nonneg_left hineq hD
    convert hh using 1
    dsimp only [Pi.div_apply]
    field_simp [hx0.ne', hs.ne', hl.ne',
      (by linarith : Chebyshev.psi x ≠ 0), (Real.log_pos hpsi).ne']
    <;> nlinarith [Real.sq_sqrt hx0.le]
  · filter_upwards [hpd.1, htd.1, eventually_gt_atTop (1 : ℝ)] with x hpsi htheta hx
    have hx0 : 0 < x := by linarith
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hl : 0 < Real.log x := Real.log_pos hx
    have hD : 0 ≤ Real.sqrt x * Real.log x := by positivity
    have hineq : J x ≤ (Chebyshev.psi x - Chebyshev.theta x) /
        (Chebyshev.theta x * Real.log (Chebyshev.theta x)) := by
      by_cases heq : Chebyshev.theta x = Chebyshev.psi x
      · simp [J, ← heq]
      · have hh := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
          htheta hpsi heq
        simpa [J, D5.S3.Arith.Robin.ActualRobinClockCovariance.g,
          div_eq_mul_inv] using hh.le
    have hh := mul_le_mul_of_nonneg_left hineq hD
    convert hh using 1
    dsimp only [Pi.div_apply]
    field_simp [hx0.ne', hs.ne', hl.ne',
      (by linarith : Chebyshev.theta x ≠ 0), (Real.log_pos htheta).ne']
    <;> nlinarith [Real.sq_sqrt hx0.le]

open Finset Filter
open scoped Topology
private def tau (x : ℝ) (p : ℕ) : ℝ :=
  1 / (p : ℝ) ^ (p.log ⌊x⌋₊ + 1)

private lemma tau_data {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hp : p ∈ primeCutoff x) :
    0 ≤ tau x p ∧ tau x p < 1 / x ∧
    (Real.sqrt x < p → tau x p = 1 / (p : ℝ) ^ 2) ∧
    ((p : ℝ) ≤ Real.sqrt x → tau x p ≤ 1 / (p : ℝ) ^ 3) := by
  have hpprime := (mem_filter.mp hp).2
  have hpNat : p ≤ ⌊x⌋₊ := (mem_Ioc.mp (mem_filter.mp hp).1).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
  have hx0 : 0 < x := by linarith
  have hpowNat : ⌊x⌋₊ < p ^ (p.log ⌊x⌋₊ + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hpprime.one_lt ⌊x⌋₊
  have hpow : x < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) := by
    have hfloor : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by simpa using Nat.lt_floor_add_one x
    exact hfloor.trans_le (by exact_mod_cast (show ⌊x⌋₊ + 1 ≤ p ^ (p.log ⌊x⌋₊ + 1) by omega))
  refine ⟨by dsimp [tau]; positivity, ?_, ?_, ?_⟩
  · dsimp [tau]
    exact one_div_lt_one_div_of_lt hx0 hpow
  · intro hps
    have hsq : x < (p : ℝ) ^ 2 := by
      nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
    have hn : ⌊x⌋₊ < p * p := by
      have hfr := (Nat.floor_le hx0.le).trans_lt hsq
      have hn2 : ⌊x⌋₊ < p ^ 2 := by exact_mod_cast hfr
      simpa only [pow_two] using hn2
    have he := Nat.log_eq_one_iff.mpr ⟨hn, hpprime.one_lt, hpNat⟩
    simp [tau, he]
  · intro hps
    have hsq : (p : ℝ) ^ 2 ≤ x := by
      nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
    have hpn : p ^ 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hsq)
    have ha : 2 ≤ p.log ⌊x⌋₊ := Nat.le_log_of_pow_le hpprime.one_lt hpn
    dsimp [tau]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ hp1.le (by omega : 3 ≤ p.log ⌊x⌋₊ + 1))

private lemma repeated_layer_bound {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ (primeCutoff x).filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x), tau x p) ≤
      3 / x ^ (2 / 3 : ℝ) := by
  classical
  let u := x ^ (1 / 3 : ℝ)
  let S := (primeCutoff x).filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x)
  let small := S.filter (fun p : ℕ => (p : ℝ) ≤ u)
  let large := S.filter (fun p : ℕ => u < (p : ℝ))
  have hx0 : 0 < x := by linarith
  have hu : 0 < u := Real.rpow_pos_of_pos hx0 _
  have hu3 : u ^ 3 = x := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hu2 : u ^ 2 = x ^ (2 / 3 : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hcard : (small.card : ℝ) ≤ u := by
    have hsub : small ⊆ Ioc 0 ⌊u⌋₊ := by
      intro p hp
      have hS := (mem_filter.mp hp).1
      have hprime := (mem_filter.mp (mem_filter.mp hS).1).2
      exact mem_Ioc.mpr ⟨hprime.pos, Nat.le_floor (mem_filter.mp hp).2⟩
    calc
      _ ≤ ((Ioc 0 ⌊u⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (⌊u⌋₊ : ℝ) := by simp
      _ ≤ u := Nat.floor_le hu.le
  have hsmall : (∑ p ∈ small, tau x p) ≤ 1 / u ^ 2 := by
    have hs := sum_le_card_nsmul small (tau x) (1 / x) (by
      intro p hp
      exact (tau_data hx (mem_filter.mp (mem_filter.mp hp).1).1).2.1.le)
    rw [nsmul_eq_mul] at hs
    calc
      _ ≤ (small.card : ℝ) * (1 / x) := hs
      _ ≤ u * (1 / x) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / u ^ 2 := by rw [← hu3]; field_simp
  have hlarge : (∑ p ∈ large, tau x p) ≤ 2 / u ^ 2 := by
    calc
      _ ≤ ∑ p ∈ large, 1 / (p : ℝ) ^ 3 := by
        apply sum_le_sum
        intro p hp
        have hS := (mem_filter.mp hp).1
        exact (tau_data hx (mem_filter.mp hS).1).2.2.2 (mem_filter.mp hS).2
      _ ≤ 2 / u ^ 2 :=
        D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure.finite_cubic_tail hu large
          (fun p hp => (mem_filter.mp hp).2)
  have hsplit : (∑ p ∈ S, tau x p) =
      (∑ p ∈ small, tau x p) + ∑ p ∈ large, tau x p := by
    simpa only [small, large, not_le] using
      (sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ u) (tau x)).symm
  change (∑ p ∈ S, tau x p) ≤ _
  rw [hsplit, ← hu2]
  calc
    _ ≤ 1 / u ^ 2 + 2 / u ^ 2 := add_le_add hsmall hlarge
    _ = 3 / u ^ 2 := by ring

private lemma ordinary_layer_bracket {x : ℝ} (hx : 2 ≤ x) :
    let S := ∑ p ∈ (Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime,
      1 / (p : ℝ) ^ 2
    S ≤ A x ∧ A x ≤ (1 + 1 / x) * (S + 3 / x ^ (2 / 3 : ℝ)) := by
  classical
  dsimp only
  let Q := ∑ p ∈ primeCutoff x, tau x p
  let H := (primeCutoff x).filter (fun p : ℕ => Real.sqrt x < (p : ℝ))
  have hx0 : 0 < x := by linarith
  have hH : H = (Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [H, primeCutoff, mem_filter, mem_Ioc]
    have hs := Nat.floor_lt (Real.sqrt_nonneg x) (n := p)
    constructor
    · rintro ⟨⟨⟨_, hp⟩, hprime⟩, hroot⟩
      exact ⟨⟨hs.mpr hroot, hp⟩, hprime⟩
    · rintro ⟨⟨hroot, hp⟩, hprime⟩
      exact ⟨⟨⟨hprime.pos, hp⟩, hprime⟩, hs.mp hroot⟩
  have hmain : (∑ p ∈ H, tau x p) = ∑ p ∈ H, 1 / (p : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro p hp
    exact (tau_data hx (mem_filter.mp hp).1).2.2.1 (mem_filter.mp hp).2
  have hsum : (∑ p ∈ H, 1 / (p : ℝ) ^ 2) ≤ Q ∧
      Q ≤ (∑ p ∈ H, 1 / (p : ℝ) ^ 2) + 3 / x ^ (2 / 3 : ℝ) := by
    have hsplit := (sum_filter_add_sum_filter_not (primeCutoff x)
      (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x) (tau x)).symm
    have hnot : (primeCutoff x).filter (fun p : ℕ => ¬(p : ℝ) ≤ Real.sqrt x) = H := by
      ext p; simp [H]
    rw [hnot, hmain] at hsplit
    have hlo : 0 ≤ ∑ p ∈ (primeCutoff x).filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x),
        tau x p := sum_nonneg (fun p hp => (tau_data hx (mem_filter.mp hp).1).1)
    have hhi := repeated_layer_bound hx
    dsimp only [Q]
    constructor <;> linarith
  have hlog : Q ≤ A x ∧ A x ≤ (1 + 1 / x) * Q := by
    have hterm (p : ℕ) (hp : p ∈ primeCutoff x) :
        tau x p ≤ -Real.log (1 - tau x p) ∧
        -Real.log (1 - tau x p) ≤ (1 + 1 / x) * tau x p := by
      have hd := tau_data hx hp
      have hhalf : tau x p ≤ 1 / 2 := hd.2.1.le.trans
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx)
      have hz : 0 < 1 - tau x p := by linarith
      have hlo := Real.log_le_sub_one_of_pos hz
      have hhi := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le hd.1 hhalf
      constructor
      · linarith
      · nlinarith [mul_le_mul_of_nonneg_right hd.2.1.le hd.1]
    dsimp [Q, A]
    simp only [← sum_neg_distrib]
    constructor
    · exact sum_le_sum (fun p hp => (hterm p hp).1)
    · rw [mul_sum]
      exact sum_le_sum (fun p hp => (hterm p hp).2)
  rw [hH] at hsum
  exact ⟨hsum.1.trans hlog.1, hlog.2.trans
    (mul_le_mul_of_nonneg_left hsum.2 (by positivity))⟩

/-- The full terminal Euler-layer correction has leading root-log coefficient two. -/
theorem A_scaled_limit :
    Tendsto (fun x : ℝ => (Real.sqrt x * Real.log x) * A x) atTop (𝓝 2) := by
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ (Ioc ⌊Real.sqrt x⌋₊ ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2
  have hmain : Tendsto (fun x => (Real.sqrt x * Real.log x) * S x) atTop (𝓝 2) := by
    simpa only [D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect.scale,
      D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.squareSum,
      D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeInterval,
      one_mul, div_one] using
      D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect.scaled_tail_limit
        (c := 1) zero_lt_one
  have hsmall : Tendsto (fun x : ℝ => (Real.sqrt x * Real.log x) *
      (3 / x ^ (2 / 3 : ℝ))) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => 3 * (Real.log x / x ^ (1 / 6 : ℝ)))
        atTop (𝓝 0) := by
      simpa only [Real.rpow_one, mul_zero] using
        ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero).const_mul 3
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow]
    have he : x ^ (1 / 2 : ℝ) / x ^ (2 / 3 : ℝ) = 1 / x ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_sub hx, show (1 / 2 : ℝ) - 2 / 3 = -(1 / 6 : ℝ) by norm_num,
        Real.rpow_neg hx.le]
      simp only [one_div]
    calc
      _ = 3 * Real.log x * (1 / x ^ (1 / 6 : ℝ)) := by ring
      _ = 3 * Real.log x * (x ^ (1 / 2 : ℝ) / x ^ (2 / 3 : ℝ)) := by rw [he]
      _ = _ := by ring
  have hfactor : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  have hu := hfactor.mul (hmain.add hsmall)
  norm_num only [add_zero, one_mul] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hu
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hd : 0 ≤ Real.sqrt x * Real.log x := by
      have := Real.log_nonneg (show 1 ≤ x by linarith)
      positivity
    exact mul_le_mul_of_nonneg_left (ordinary_layer_bracket hx).1 hd
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hd : 0 ≤ Real.sqrt x * Real.log x := by
      have := Real.log_nonneg (show 1 ≤ x by linarith)
      positivity
    convert mul_le_mul_of_nonneg_left (ordinary_layer_bracket hx).2 hd using 1 <;> ring

open Finset Filter MeasureTheory Set
open scoped Topology Chebyshev
private def kernel (t : ℝ) : ℝ := 1 / (t * Real.sqrt t)

private lemma kernel_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt kernel (-3 / (2 * t ^ 2 * Real.sqrt t)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  convert (hasDerivAt_const t (1 : ℝ)).fun_div
    ((hasDerivAt_id t).mul (Real.hasDerivAt_sqrt ht.ne'))
    (mul_ne_zero ht.ne' hs.ne') using 1
  · rfl
  · simp only [Pi.mul_apply, id_eq]
    field_simp [ht.ne', hs.ne']
    rw [Real.sq_sqrt ht.le]
    ring

private lemma finite_weighted_lower {y z rho : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (htheta : ∀ t ∈ Set.Icc y z,
      (1 - rho) * t ≤ θ t ∧ θ t ≤ (1 + rho) * t) :
    (2 - 4 * rho) / Real.sqrt y - (2 - 2 * rho) / Real.sqrt z ≤
      ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        Real.log p * kernel p := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := hy0.trans_le hyz
  have hc (t : ℝ) : (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, c p) = θ t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hcont : ContinuousOn (fun t : ℝ => -3 / (2 * t ^ 2 * Real.sqrt t))
      (Set.Icc y z) := by
    apply continuousOn_const.div
      ((continuousOn_const.mul (continuousOn_id.pow 2)).mul Real.continuous_sqrt.continuousOn)
    intro t ht
    have ht0 := hy0.trans_le ht.1
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ht0.ne'))
      (Real.sqrt_pos.mpr ht0).ne'
  have hi : IntegrableOn (deriv kernel) (Set.Icc y z) :=
    hcont.integrableOn_Icc.congr_fun
      (fun t ht => (kernel_deriv (hy0.trans_le ht.1)).deriv.symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hy0.le hyz
    (fun t ht => (kernel_deriv (hy0.trans_le ht.1)).differentiableAt) hi
  simp_rw [hc] at habel
  rw [← intervalIntegral.integral_of_le hyz] at habel
  have hprod : IntegrableOn (fun t => deriv kernel t * θ t) (Set.Icc y z) := by
    simpa only [hc] using integrableOn_mul_sum_Icc c hy0.le hi (m := 0)
  have hmajor : ContinuousOn (fun t : ℝ => -3 * (1 - rho) / (2 * t * Real.sqrt t))
      (Set.Icc y z) := by
    apply continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).mul Real.continuous_sqrt.continuousOn)
    intro t ht
    have ht0 := hy0.trans_le ht.1
    exact mul_ne_zero (mul_ne_zero (by norm_num) ht0.ne')
      (Real.sqrt_pos.mpr ht0).ne'
  have hmajorint := hmajor.intervalIntegrable_of_Icc (μ := volume) hyz
  have hint := intervalIntegral.integral_mono_on hyz
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr hprod) hmajorint
    (fun t ht => by
      rw [(kernel_deriv (hy0.trans_le ht.1)).deriv]
      have ht0 : 0 < t := hy0.trans_le ht.1
      have hh := mul_le_mul_of_nonpos_left (htheta t ht).1
        (show -3 / (2 * t ^ 2 * Real.sqrt t) ≤ 0 by
          apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
          positivity)
      convert hh using 1
      field_simp)
  have hFTC : (∫ t in y..z, -3 * (1 - rho) / (2 * t * Real.sqrt t)) =
      3 * (1 - rho) / Real.sqrt z - 3 * (1 - rho) / Real.sqrt y := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => 3 * (1 - rho) / Real.sqrt t) _ hmajorint
    intro t ht
    rw [Set.uIcc_of_le hyz] at ht
    have ht0 : 0 < t := hy0.trans_le ht.1
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    convert (hasDerivAt_const t (3 * (1 - rho))).fun_div
      (Real.hasDerivAt_sqrt ht0.ne') hs.ne' using 1
    field_simp [ht0.ne', hs.ne']
    rw [Real.sq_sqrt ht0.le]
    ring
  rw [hFTC] at hint
  have htop : (1 - rho) / Real.sqrt z ≤ kernel z * θ z := by
    have hh := mul_le_mul_of_nonneg_left (htheta z ⟨hyz, le_rfl⟩).1
      (show 0 ≤ kernel z by dsimp [kernel]; positivity)
    convert hh using 1
    dsimp [kernel]
    field_simp
  have hbot : kernel y * θ y ≤ (1 + rho) / Real.sqrt y := by
    have hh := mul_le_mul_of_nonneg_left (htheta y ⟨le_rfl, hyz⟩).2
      (show 0 ≤ kernel y by dsimp [kernel]; positivity)
    convert hh using 1
    dsimp [kernel]
    field_simp
  have hs : (∑ p ∈ Finset.Ioc ⌊y⌋₊ ⌊z⌋₊, kernel p * c p) =
      ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        Real.log p * kernel p := by
    simp only [sum_filter, c, mul_ite, mul_zero]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> ring
  rw [hs] at habel
  have he : (1 - rho) / Real.sqrt z - (1 + rho) / Real.sqrt y -
      (3 * (1 - rho) / Real.sqrt z - 3 * (1 - rho) / Real.sqrt y) =
      (2 - 4 * rho) / Real.sqrt y - (2 - 2 * rho) / Real.sqrt z := by ring
  linarith

private lemma finite_prime_tail_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 < C ∧ ∀ᶠ y : ℝ in atTop,
      2 - epsilon < Real.sqrt y * Real.log y *
        (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime, kernel p) := by
  classical
  let eta : ℝ := min (epsilon / 16) (1 / 16)
  have heta0 : 0 < eta := lt_min (by positivity) (by norm_num)
  have heta16 : eta ≤ 1 / 16 := min_le_right _ _
  have hetaE : 16 * eta ≤ epsilon := by
    have h := min_le_left (epsilon / 16) (1 / 16 : ℝ)
    change eta ≤ epsilon / 16 at h
    linarith
  have heta1 : eta < 1 := by linarith
  let C : ℝ := (1 / eta) ^ 2
  have hC : 1 < C := by
    have hi : 1 < 1 / eta := (lt_div_iff₀ heta0).mpr (by simpa using heta1)
    dsimp [C]
    nlinarith
  have hC0 : 0 < C := by linarith
  have hCsqrt : Real.sqrt C = 1 / eta := by
    dsimp [C]
    rw [Real.sqrt_sq (by positivity)]
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.eventually
      (Metric.ball_mem_nhds (1 : ℝ) heta0))
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop
    (max T (max 2 (Real.exp (Real.log C / eta))))] with y hy
  have hy2 : 2 ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy1 : 1 < y := by linarith
  have hy0 : 0 < y := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hyCy : y ≤ C * y := by nlinarith
  have hlogCy : 0 < Real.log (C * y) := Real.log_pos (hy1.trans_le hyCy)
  have htheta (t : ℝ) (hyt : y ≤ t) :
      (1 - eta) * t ≤ θ t ∧ θ t ≤ (1 + eta) * t := by
    have ht0 : 0 < t := hy0.trans_le hyt
    have hTt : T ≤ t := (le_max_left _ _).trans (hy.trans hyt)
    have herr : |θ t / t - 1| < eta := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hT t hTt
    obtain ⟨hl, hu⟩ := abs_lt.mp herr
    constructor
    · exact (le_div_iff₀ ht0).mp (by linarith : 1 - eta ≤ θ t / t)
    · exact (div_le_iff₀ ht0).mp (by linarith : θ t / t ≤ 1 + eta)
  have hweighted := finite_weighted_lower hy1 hyCy (fun t ht => htheta t ht.1)
  have hroot : Real.sqrt (C * y) = Real.sqrt y / eta := by
    rw [Real.sqrt_mul hC0.le, hCsqrt]
    ring
  have hw : (2 - 6 * eta) / Real.sqrt y ≤
      ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
        Real.log p * kernel p := by
    apply le_trans _ hweighted
    rw [hroot]
    have hn : 0 ≤ eta ^ 2 := sq_nonneg eta
    field_simp
    nlinarith
  have hcompare :
      (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
        Real.log p * kernel p) ≤
      Real.log (C * y) *
        (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime, kernel p) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpCy : (p : ℝ) ≤ C * y :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp (mem_filter.mp hp).1).2).trans
        (Nat.floor_le (mul_pos hC0 hy0).le)
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hpp.pos) hpCy)
      (by dsimp [kernel]; positivity)
  have hlogbound : Real.log C ≤ eta * Real.log y := by
    have hexp : Real.exp (Real.log C / eta) ≤ y :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hy)
    have h := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at h
    simpa only [mul_comm] using (div_le_iff₀ heta0).mp h
  have hlogratio : 1 - eta ≤ Real.log y / Real.log (C * y) := by
    apply (le_div_iff₀ hlogCy).mpr
    rw [Real.log_mul hC0.ne' hy0.ne']
    have hlogC : 0 ≤ Real.log C := (Real.log_pos hC).le
    nlinarith [mul_nonneg heta0.le hlogC]
  have hmul := mul_le_mul_of_nonneg_left (hw.trans hcompare)
    (div_nonneg (mul_nonneg hsy.le hlogy.le) hlogCy.le)
  have he1 : Real.sqrt y * Real.log y / Real.log (C * y) *
      ((2 - 6 * eta) / Real.sqrt y) =
        (2 - 6 * eta) * (Real.log y / Real.log (C * y)) := by
    field_simp
  have he2 : Real.sqrt y * Real.log y / Real.log (C * y) *
      (Real.log (C * y) *
        (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime, kernel p)) =
      Real.sqrt y * Real.log y *
        (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime, kernel p) := by
    rw [← mul_assoc, div_mul_cancel₀ _ hlogCy.ne']
  rw [he1, he2] at hmul
  have hr := mul_le_mul_of_nonneg_left hlogratio
    (show 0 ≤ 2 - 6 * eta by linarith)
  have hc : 2 - 8 * eta ≤ (2 - 6 * eta) * (1 - eta) := by
    nlinarith [sq_nonneg eta]
  have hf := hc.trans (hr.trans hmul)
  linarith

private lemma kernel_eq_rpow {p : ℕ} (hp : p.Prime) :
    kernel p = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_neg hp0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hp0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  simp only [kernel, one_div]

private lemma finite_euler_tail_lower {x z : ℝ} (hx : 1 < x) (hxz : x ≤ z) :
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, kernel p) ≤
      Real.log (riemannZeta ((3 / 2 : ℝ) : ℂ)).re +
        ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          Real.log (1 - (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  classical
  let e : ℕ → ℝ := fun p => -Real.log (1 - (p : ℝ) ^ (-(3 / 2 : ℝ)))
  have he0 (p : Nat.Primes) : 0 ≤ e p := by
    have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 ≤ (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hq1 : (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
    exact neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr hq1).le (by linarith))
  have hsum : Summable (fun p : Nat.Primes => e p) :=
    D5.S3.Analytic.Zeta.EulerLogBridge.summable_prime_eulerLog
      (3 / 2) (by norm_num)
  have hEuler : (∑' p : Nat.Primes, e p) =
      Real.log (riemannZeta ((3 / 2 : ℝ) : ℂ)).re := by
    have hz := congrArg Complex.re
      (D5.S3.Analytic.ZetaGibbs.partition_function_toReal_eq_riemannZeta
        (3 / 2) (by norm_num))
    simp only [Complex.ofReal_re] at hz
    rw [← hz]
    exact (D5.S3.Analytic.Zeta.EulerLogBridge.log_partitionFunction_eq_tsum_prime
      (3 / 2) (by norm_num)).symm
  have hfull : (∑ p ∈ (Finset.Ioc 0 ⌊z⌋₊).filter Nat.Prime, e p) ≤
      Real.log (riemannZeta ((3 / 2 : ℝ) : ℂ)).re := by
    rw [← hEuler, ← Finset.sum_subtype_eq_sum_filter e]
    have hlim : Tendsto (fun s : Finset Nat.Primes => ∑ p ∈ s, e p)
        atTop (𝓝 (∑' p : Nat.Primes, e p)) := hsum.hasSum
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop ((Finset.Ioc 0 ⌊z⌋₊).subtype Nat.Prime)] with s hs
    exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => he0 p)
  have hpoint :
      (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, kernel p) ≤
        ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊z⌋₊).filter Nat.Prime, e p := by
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hq1 : (p : ℝ) ^ (-(3 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
    have hl := Real.log_le_sub_one_of_pos (sub_pos.mpr hq1)
    rw [kernel_eq_rpow hpp]
    dsimp [e]
    linarith
  have hsplit := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then e p else 0)
    (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxz)
  simp only [← Finset.sum_filter] at hsplit
  have hpref : (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, e p) =
      -(∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        Real.log (1 - (p : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    simp only [e, Finset.sum_neg_distrib]
  rw [hpref] at hsplit
  linarith

/-- The exact endpoint Euler remainder has the lower constant two at every
sufficiently large real cutoff. -/
theorem endpoint_euler_tail_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      2 - epsilon < Real.sqrt x * Real.log x *
        (Real.log (riemannZeta ((3 / 2 : ℝ) : ℂ)).re +
          ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
            Real.log (1 - (p : ℝ) ^ (-(3 / 2 : ℝ)))) := by
  obtain ⟨C, hC, hfinite⟩ := finite_prime_tail_lower epsilon hepsilon
  filter_upwards [hfinite, eventually_gt_atTop (1 : ℝ)] with x hfinite hx
  have hx0 : 0 < x := by linarith
  have hxC : x ≤ C * x := by nlinarith
  exact hfinite.trans_le (mul_le_mul_of_nonneg_left
    (finite_euler_tail_lower hx hxC)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.log_pos hx).le))

end D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

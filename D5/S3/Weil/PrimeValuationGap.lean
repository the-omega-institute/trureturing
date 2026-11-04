/- GID: D5/S3/Weil/PrimeValuationGap
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeValuationGap
   mirror-E: none(waiver:qualitative-asymptotic-estimate)
   anchors: []
   utility: none
   digest: Bounded valuations at a fixed prime leave a positive asymptotic Robin margin. -/

import D5.S3.Weil.GronwallLowerEnvelope
import Mathlib.Tactic.FieldSimp

/-!
The local Euler factor is retained exactly when a fixed number of prime layers
is added. The number of added layers is chosen before the integer threshold.
All statements concern arbitrary primes and unbounded natural or real parameters.
They are arithmetic identities or analytic estimates, not finite enumeration,
checkers, numerical reductions, or certified finite instances.
-/

set_option autoImplicit false

namespace D5.S3.Weil.PrimeValuationGap

open Filter
open scoped Topology
open D5.S3.Arith.Robin.PaddingRatio
open D5.S3.Weil.GronwallLowerEnvelope

local notation "Z" => (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℝ) / n)

private theorem reciprocal_prime_bounds {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ < 1 := by
  exact ⟨inv_pos.mpr (Nat.cast_pos.mpr hp.pos),
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)⟩

theorem retention_pos {p : ℕ} (hp : p.Prime) (a : ℕ) :
    0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
  sub_pos.mpr (pow_lt_one₀ (reciprocal_prime_bounds hp).1.le
    (reciprocal_prime_bounds hp).2 (by omega))

private theorem abundancy_pos {n : ℕ} (hn : n ≠ 0) : 0 < Z n :=
  div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n hn))
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))

private theorem normalized_sigma_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Z (p ^ a) = (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  dsimp only
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_eq hp1]
  simp only [inv_pow, pow_succ]
  field_simp

theorem normalized_sigma_pow_mul {p m : ℕ} (hp : p.Prime)
    (hm : p.Coprime m) (a : ℕ) :
    Z (p ^ a * m) =
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) * Z m := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    (hm.pow_left a)
  change (ArithmeticFunction.sigma 1 (p ^ a * m) : ℝ) / (p ^ a * m : ℕ) = _
  rw [h, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]
  exact congrArg (fun x : ℝ => x * Z m) (normalized_sigma_prime_pow hp a)

/-- Exact abundancy gain from adding `b` layers at a prime, including `b = 0`. -/
theorem prime_power_abundancy_ratio {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (b : ℕ) :
    Z (p ^ b * n) / Z n =
      (1 - (p : ℝ)⁻¹ ^ (n.factorization p + b + 1)) /
        (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1)) := by
  have hcop := Nat.coprime_ordCompl hp hn
  have hn' : n = p ^ n.factorization p * (ordCompl[p] n) :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hm' : p ^ b * n = p ^ (n.factorization p + b) * (ordCompl[p] n) := by
    conv_lhs => arg 2; rw [hn']
    rw [← mul_assoc, ← pow_add, Nat.add_comm b]
  have hZn : Z n =
      (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1)) / (1 - (p : ℝ)⁻¹) *
        Z (ordCompl[p] n) := by
    calc
      Z n = Z (p ^ n.factorization p * (ordCompl[p] n)) := congrArg Z hn'
      _ = _ := normalized_sigma_pow_mul hp hcop _
  have hZm : Z (p ^ b * n) =
      (1 - (p : ℝ)⁻¹ ^ (n.factorization p + b + 1)) / (1 - (p : ℝ)⁻¹) *
        Z (ordCompl[p] n) := by
    calc
      Z (p ^ b * n) = Z (p ^ (n.factorization p + b) * (ordCompl[p] n)) :=
        congrArg Z hm'
      _ = _ := normalized_sigma_pow_mul hp hcop _
  rw [hZn, hZm, mul_div_mul_right _ _ (abundancy_pos (Nat.ordCompl_pos p hn).ne').ne']
  exact div_div_div_cancel_right₀ (sub_pos.mpr (reciprocal_prime_bounds hp).2).ne' _ _

/-- The smallest gain on an exponent window occurs at its largest exponent. -/
theorem prime_power_abundancy_gain {p n A : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (ha : n.factorization p ≤ A) (b : ℕ) :
    (1 - (p : ℝ)⁻¹ ^ (A + b + 1)) / (1 - (p : ℝ)⁻¹ ^ (A + 1)) ≤
      Z (p ^ b * n) / Z n := by
  rw [prime_power_abundancy_ratio hp hn b]
  apply (div_le_div_iff₀ (retention_pos hp A) (retention_pos hp _)).mpr
  have hr := reciprocal_prime_bounds hp
  have hpow := pow_le_pow_of_le_one hr.1.le hr.2.le (Nat.add_le_add_right ha 1)
  have hb := pow_le_one₀ hr.1.le hr.2.le (n := b)
  have hproduct := mul_nonneg (sub_nonneg.mpr hpow) (sub_nonneg.mpr hb)
  rw [show A + b + 1 = (A + 1) + b by omega,
    show n.factorization p + b + 1 = (n.factorization p + 1) + b by omega,
    pow_add _ (A + 1) b, pow_add _ (n.factorization p + 1) b]
  nlinarith only [hproduct]

/-- The sharp logarithmic local defect is positive for each fixed prime and exponent bound. -/
theorem prime_valuation_gap_pos {p : ℕ} (hp : p.Prime) (A : ℕ) :
    0 < -Real.log (1 - (p : ℝ)⁻¹ ^ (A + 1)) := by
  apply neg_pos.mpr
  apply Real.log_neg (retention_pos hp A)
  exact sub_lt_self 1 (pow_pos (reciprocal_prime_bounds hp).1 _)

theorem tendsto_loglog_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (Real.log (c * n)) / Real.log (Real.log n))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hdiff := (Real.tendsto_log_comp_add_sub_log (Real.log c)).comp hlog
  have hlim := (hdiff.div_atTop hloglog).add_const 1
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 5041] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [Function.comp_def]
  rw [Real.log_mul hc.ne' hn0, add_comm (Real.log c) (Real.log (n : ℝ))]
  field_simp [(loglog_pos hn).ne']
  ring

-- Here b is an input, so the threshold may depend on it, never conversely.
private theorem fixed_boost_envelope {p : ℕ} (hp : p.Prime) (A b : ℕ) (q : ℝ)
    (hq : (1 - (p : ℝ)⁻¹ ^ (A + 1)) / (1 - (p : ℝ)⁻¹ ^ (A + b + 1)) < q) :
    ∃ N ≥ 5041, ∀ n ≥ N, n.factorization p ≤ A → robinRatio n ≤ q := by
  let k := (1 - (p : ℝ)⁻¹ ^ (A + 1)) / (1 - (p : ℝ)⁻¹ ^ (A + b + 1))
  have hk : 0 < k := div_pos (retention_pos hp A) (retention_pos hp (A + b))
  change k < q at hq
  let η := (q / k - 1) / 2
  have hη : 0 < η := div_pos
    (sub_pos.mpr ((lt_div_iff₀ hk).mpr (by simpa only [one_mul] using hq))) two_pos
  have hmid : k * (1 + η) = (k + q) / 2 := by
    dsimp only [η]
    field_simp
    ring
  have hmargin : k * (1 + η) < q := by rw [hmid]; linarith only [hq]
  have hscale : Tendsto (fun n : ℕ =>
      Real.log (Real.log (p ^ b * n : ℕ)) / Real.log (Real.log n)) atTop (𝓝 1) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      (tendsto_loglog_scale (pow_pos (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p) b))
  have hlim : Tendsto (fun n : ℕ => k * (1 + η) *
      (Real.log (Real.log (p ^ b * n : ℕ)) / Real.log (Real.log n)))
      atTop (𝓝 (k * (1 + η))) := by
    simpa only [mul_one] using hscale.const_mul (k * (1 + η))
  obtain ⟨N₁, hN₁⟩ := GronwallUpperEnvelope.gronwall_upper_envelope η hη
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually_lt_const hmargin)
  refine ⟨max 5041 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro n hn ha
  have hnlarge : 5041 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnm : n ≤ p ^ b * n := Nat.le_mul_of_pos_left n (pow_pos hp.pos b)
  have hmlarge : 5041 ≤ p ^ b * n := hnlarge.trans hnm
  have hmR : (0 : ℝ) < (p ^ b * n : ℕ) := Nat.cast_pos.mpr (by omega)
  have hLn := loglog_pos hnlarge
  have hLm := loglog_pos hmlarge
  have hu : robinRatio (p ^ b * n) ≤ 1 + η := hN₁ _ (by omega)
  have hgain := prime_power_abundancy_gain hp hn0 ha b
  have hcross := (div_le_div_iff₀ (retention_pos hp A) (abundancy_pos hn0)).mp hgain
  have hsig : Z n ≤ k * Z (p ^ b * n) := by
    calc
      Z n ≤ Z (p ^ b * n) * (1 - (p : ℝ)⁻¹ ^ (A + 1)) /
          (1 - (p : ℝ)⁻¹ ^ (A + b + 1)) :=
        (le_div_iff₀ (retention_pos hp (A + b))).mpr
          (by simpa only [mul_comm] using hcross)
      _ = k * Z (p ^ b * n) := by dsimp only [k]; ring
  calc
    robinRatio n = Z n / (Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log n)) := by
      dsimp only [robinRatio]
      rw [div_div]
      congr 1
      ring
    _ ≤ (k * Z (p ^ b * n)) / (Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log n)) :=
      div_le_div_of_nonneg_right hsig (mul_pos (Real.exp_pos _) hLn).le
    _ = (k * robinRatio (p ^ b * n)) *
        (Real.log (Real.log (p ^ b * n : ℕ)) / Real.log (Real.log n)) := by
      dsimp only [robinRatio]
      field_simp [hnR.ne', hmR.ne', hLn.ne', hLm.ne', Real.exp_ne_zero]
    _ ≤ (k * (1 + η)) *
        (Real.log (Real.log (p ^ b * n : ℕ)) / Real.log (Real.log n)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hk.le)
        (div_pos hLm hLn).le
    _ ≤ q := (hN₂ n (by omega)).le

/-- The quantitative sharp upper envelope on every fixed bounded-valuation class. -/
theorem bounded_prime_valuation_robin_ratio {p : ℕ} (hp : p.Prime) (A : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N ≥ 5041, ∀ n ≥ N, n.factorization p ≤ A →
      robinRatio n ≤ 1 - (p : ℝ)⁻¹ ^ (A + 1) + ε := by
  have hr := reciprocal_prime_bounds hp
  have hpow : Tendsto (fun b : ℕ => (p : ℝ)⁻¹ ^ (A + b + 1)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le hr.2).const_mul
      ((p : ℝ)⁻¹ ^ (A + 1))
    simpa only [mul_zero, ← pow_add, Nat.add_right_comm A 1] using h
  have hquot : Tendsto (fun b : ℕ =>
      (1 - (p : ℝ)⁻¹ ^ (A + 1)) / (1 - (p : ℝ)⁻¹ ^ (A + b + 1)))
      atTop (𝓝 (1 - (p : ℝ)⁻¹ ^ (A + 1))) := by
    have h : Tendsto (fun b : ℕ =>
        (1 - (p : ℝ)⁻¹ ^ (A + 1)) / (1 - (p : ℝ)⁻¹ ^ (A + b + 1)))
        atTop (𝓝 ((1 - (p : ℝ)⁻¹ ^ (A + 1)) / (1 - (0 : ℝ)))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub hpow) (by norm_num)
    simpa only [sub_zero, div_one] using h
  have hsmall := hquot.eventually_lt_const
    (lt_add_of_pos_right (1 - (p : ℝ)⁻¹ ^ (A + 1)) hε)
  -- Select the layer count once, before obtaining the n-threshold for that count.
  obtain ⟨b, _, hb⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  exact fixed_boost_envelope hp A b _ hb

/-- A fixed prime with bounded valuation leaves its strictly positive asymptotic log margin. -/
theorem bounded_prime_valuation_robin_margin_gap {p : ℕ} (hp : p.Prime) (A : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N ≥ 5041, ∀ n ≥ N, n.factorization p ≤ A →
      -Real.log (1 - (p : ℝ)⁻¹ ^ (A + 1)) - ε ≤ robinLogMargin n := by
  have hd := retention_pos hp A
  have he : 0 < Real.exp ε - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hε)
  obtain ⟨N, hN, hbound⟩ := bounded_prime_valuation_robin_ratio hp A
    ((1 - (p : ℝ)⁻¹ ^ (A + 1)) * (Real.exp ε - 1)) (mul_pos hd he)
  refine ⟨N, hN, ?_⟩
  intro n hn ha
  have hnlarge := hN.trans hn
  have hpos : 0 < robinRatio n :=
    div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (by omega)))
      (mul_pos (mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (by omega)))
        (loglog_pos hnlarge))
  have hu : robinRatio n ≤ Real.exp (Real.log (1 - (p : ℝ)⁻¹ ^ (A + 1)) + ε) := by
    calc
      robinRatio n ≤ 1 - (p : ℝ)⁻¹ ^ (A + 1) +
          (1 - (p : ℝ)⁻¹ ^ (A + 1)) * (Real.exp ε - 1) := hbound n hn ha
      _ = _ := by rw [Real.exp_add, Real.exp_log hd]; ring
  have hlog := (Real.log_le_iff_le_exp hpos).mpr hu
  rw [robin_log_margin_eq_neg_log hnlarge]
  linarith only [hlog]

#print axioms prime_power_abundancy_ratio
#print axioms prime_power_abundancy_gain
#print axioms prime_valuation_gap_pos
#print axioms bounded_prime_valuation_robin_ratio
#print axioms bounded_prime_valuation_robin_margin_gap

end D5.S3.Weil.PrimeValuationGap

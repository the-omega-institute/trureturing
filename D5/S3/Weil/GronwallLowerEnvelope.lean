/- GID: D5/S3/Weil/GronwallLowerEnvelope
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct the lower Gronwall envelope from powers of primorials. -/

import D5.S3.Weil.GronwallUpperEnvelope
import Mathlib.NumberTheory.Primorial

/-!
Powers of primorials give the lower half of Gronwall's theorem.
The uniform prime-power error is bounded by a geometric factor times the
summable series of reciprocal squares. The logarithmic denominator uses
only the Chebyshev upper bound `primorial_le_four_pow`.
-/

set_option autoImplicit false

namespace D5.S3.Weil.GronwallLowerEnvelope

open Finset Filter Real Asymptotics
open scoped BigOperators Topology

private theorem one_sub_sum_le_product (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ s, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 - f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hfp := hf p (Finset.mem_insert_self p s)
    have hfs : ∀ q ∈ s, 0 ≤ f q ∧ f q ≤ 1 :=
      fun q hq => hf q (Finset.mem_insert_of_mem hq)
    have hsum : 0 ≤ ∑ q ∈ s, f q := Finset.sum_nonneg fun q hq => (hfs q hq).1
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    calc
      1 - (f p + ∑ q ∈ s, f q) ≤ (1 - f p) * (1 - ∑ q ∈ s, f q) := by
        nlinarith only [mul_nonneg hfp.1 hsum]
      _ ≤ (1 - f p) * ∏ q ∈ s, (1 - f q) :=
        mul_le_mul_of_nonneg_left (ih hfs) (sub_nonneg.mpr hfp.2)

private theorem prime_power_error (a y : ℕ) :
    1 - (1 / 2 : ℝ) ^ a * (∑' m : ℕ, 1 / (m : ℝ) ^ 2) ≤
      ∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ) ^ (a + 2)) := by
  have hpoint (p : ℕ) (hp : p ∈ Nat.primesLE y) :
      1 / (p : ℝ) ^ (a + 2) ≤ (1 / 2 : ℝ) ^ a * (1 / (p : ℝ) ^ 2) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
    calc
      1 / (p : ℝ) ^ (a + 2) = (1 / (p : ℝ)) ^ a * (1 / (p : ℝ) ^ 2) := by
        simp only [pow_add, one_div, mul_inv, inv_pow]
      _ ≤ (1 / 2 : ℝ) ^ a * (1 / (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity)
            (one_div_le_one_div_of_le (by norm_num) hp2) a) (by positivity)
  have hsum : (∑ p ∈ Nat.primesLE y, 1 / (p : ℝ) ^ (a + 2)) ≤
      (1 / 2 : ℝ) ^ a * (∑' m : ℕ, 1 / (m : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE y, (1 / 2 : ℝ) ^ a * (1 / (p : ℝ) ^ 2) :=
        Finset.sum_le_sum hpoint
      _ = (1 / 2 : ℝ) ^ a * ∑ p ∈ Nat.primesLE y, 1 / (p : ℝ) ^ 2 :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((summable_one_div_nat_pow.mpr (by omega : 1 < 2)).sum_le_tsum
          (Nat.primesLE y) (fun _ _ => by positivity)) (by positivity)
  refine (sub_le_sub_left hsum 1).trans (one_sub_sum_le_product _ _ ?_)
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (one_le_pow₀ hp1)⟩

private theorem sigma_primorial_power (y a : ℕ) :
    (ArithmeticFunction.sigma 1 (primorial y ^ (a + 1)) : ℝ) /
        (primorial y ^ (a + 1) : ℕ) =
      (∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ) ^ (a + 2))) *
        ∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹ := by
  let n := primorial y ^ (a + 1)
  have hn : n ≠ 0 := pow_ne_zero _ (primorial_ne_zero y)
  have hpf : n.primeFactors = Nat.primesLE y := by
    rw [Nat.primeFactors_pow_succ, primeFactors_primorial]
  have hfac (p : ℕ) (hp : p ∈ Nat.primesLE y) : n.factorization p = a + 1 := by
    have hp' := Nat.prime_of_mem_primesLE hp
    have hpdiv : p ∣ primorial y := hp'.dvd_primorial_iff.mpr (Nat.le_of_mem_primesLE hp)
    simp only [n, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree (squarefree_primorial y) hp' hpdiv, mul_one]
  have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  have hsigma : (ArithmeticFunction.sigma 1 n : ℝ) =
      ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), (p : ℝ) ^ i := by
    simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
      congrArg (fun k : ℕ => (k : ℝ))
        (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hn)
  change (ArithmeticFunction.sigma 1 n : ℝ) / n = _
  rw [hsigma, hnprod, ← Finset.prod_div_distrib, hpf, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [hfac p hp]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
  rw [geom_sum_eq hp1.ne']
  simp only [show a + 2 = (a + 1) + 1 by omega, pow_succ]
  field_simp

private theorem normalized_mertens : Tendsto
    (fun y : ℕ =>
      (∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹) /
        (Real.exp Real.eulerMascheroniConstant * Real.log y)) atTop (𝓝 1) := by
  have hne : ∀ᶠ x : ℝ in atTop,
      (Real.exp (-Real.eulerMascheroniConstant) / Real.log x)⁻¹ ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact inv_ne_zero (div_ne_zero (Real.exp_ne_zero _) (Real.log_pos hx).ne')
  have h := (isEquivalent_iff_tendsto_one hne).mp Mertens.E₃.bound''.inv
  change Tendsto (fun x : ℝ =>
    (∏ p ∈ Ioc (0 : ℕ) ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ)))⁻¹ /
      (Real.exp (-Real.eulerMascheroniConstant) / Real.log x)⁻¹) atTop (𝓝 1) at h
  have hreal : Tendsto
      (fun x : ℝ =>
        (∏ p ∈ Ioc (0 : ℕ) ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹) /
          (Real.exp Real.eulerMascheroniConstant * Real.log x)) atTop (𝓝 1) := by
    simpa only [Pi.div_apply, Pi.inv_apply, inv_div, Real.exp_neg,
      div_inv_eq_mul, Finset.prod_inv_distrib, mul_comm] using h
  simpa only [Function.comp_def, Nat.floor_natCast, ← Nat.primesLE_eq_filter_Ioc_zero]
    using hreal.comp tendsto_natCast_atTop_atTop

private theorem loglog_primorial_power_le (y a : ℕ) (hy : 0 < y)
    (hn : 0 < Real.log (primorial y ^ (a + 1) : ℕ)) :
    Real.log (Real.log (primorial y ^ (a + 1) : ℕ)) ≤
      Real.log y + Real.log ((a + 1 : ℕ) * Real.log 4) := by
  have hupper : (primorial y : ℝ) ≤ (4 : ℝ) ^ y := by
    exact_mod_cast primorial_le_four_pow y
  have hlog : Real.log (primorial y : ℝ) ≤ (y : ℝ) * Real.log 4 := by
    simpa only [Real.log_pow] using
      Real.log_le_log (Nat.cast_pos.mpr (primorial_pos y)) hupper
  have hpower : Real.log (primorial y ^ (a + 1) : ℕ) ≤
      (y : ℝ) * ((a + 1 : ℕ) * Real.log 4) := by
    rw [Nat.cast_pow, Real.log_pow]
    calc
      _ ≤ (a + 1 : ℕ) * ((y : ℝ) * Real.log 4) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = _ := by ring
  have hc : (0 : ℝ) < (a + 1 : ℕ) * Real.log 4 :=
    mul_pos (Nat.cast_pos.mpr (Nat.succ_pos a)) (Real.log_pos (by norm_num))
  simpa only [Real.log_mul (Nat.cast_pos.mpr hy).ne' hc.ne'] using
    Real.log_le_log hn hpower

/-- The normalized divisor-sum ratio is arbitrarily close to one from below
at arbitrarily large integers. -/
theorem gronwall_lower_envelope (ε : ℝ) (hε : 0 < ε) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      1 - ε ≤ (ArithmeticFunction.sigma 1 n : ℝ) /
        (Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)) := by
  let K : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ 2
  have herror : Tendsto (fun a : ℕ => (1 / 2 : ℝ) ^ a * K) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const K
  obtain ⟨a, ha⟩ := (herror.eventually_lt_const hε).exists
  let b : ℝ := 1 - (1 / 2 : ℝ) ^ a * K
  have hbε : 1 - ε < b := sub_lt_sub_left ha 1
  let c : ℝ := (a + 1 : ℕ) * Real.log 4
  have hlog : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcorr : Tendsto (fun y : ℕ => 1 + Real.log c / Real.log y) atTop (𝓝 1) := by
    simpa only [add_zero] using (hlog.const_div_atTop (Real.log c)).const_add 1
  have hbound : Tendsto
      (fun y : ℕ =>
        (b * ((∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹) /
          (Real.exp Real.eulerMascheroniConstant * Real.log y))) /
            (1 + Real.log c / Real.log y)) atTop (𝓝 b) := by
    have h := (normalized_mertens.const_mul b).div hcorr (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    · ext y
      rfl
    · simp only [mul_one, div_one]
  intro N
  obtain ⟨y, hyN, hy0, hylog, hybound⟩ :=
    ((eventually_ge_atTop N).and
      ((eventually_gt_atTop (0 : ℕ)).and
        ((hlog.eventually (eventually_gt_atTop (1 : ℝ))).and
          (hbound.eventually_const_lt hbε)))).exists
  let n : ℕ := primorial y ^ (a + 1)
  have hyn : y ≤ n :=
    le_primorial_self.trans
      (le_self_pow₀ (Nat.succ_le_iff.mpr (primorial_pos y)) (Nat.succ_ne_zero a))
  have hn0 : 0 < n := lt_of_lt_of_le hy0 hyn
  have hlogn : 1 < Real.log (n : ℝ) := hylog.trans_le
    (Real.log_le_log (Nat.cast_pos.mpr hy0) (Nat.cast_le.mpr hyn))
  have hloglogn : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlogn
  have hdenbound : Real.log (Real.log (n : ℝ)) ≤ Real.log y + Real.log c :=
    loglog_primorial_power_le y a hy0 (lt_trans zero_lt_one hlogn)
  have hdenpos : 0 < Real.log (y : ℝ) + Real.log c := hloglogn.trans_le hdenbound
  have hlogy0 : Real.log (y : ℝ) ≠ 0 := (lt_trans zero_lt_one hylog).ne'
  have hMnonneg : 0 ≤ ∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (le_of_lt (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hp1)))
  have habund : b * (∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹) ≤
      (ArithmeticFunction.sigma 1 n : ℝ) / n := by
    rw [sigma_primorial_power y a]
    exact mul_le_mul_of_nonneg_right (prime_power_error a y) hMnonneg
  have hsigma0 : 0 ≤ (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨n, hyN.trans hyn, hybound.le.trans ?_⟩
  calc
    (b * ((∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹) /
        (Real.exp Real.eulerMascheroniConstant * Real.log y))) /
          (1 + Real.log c / Real.log y) =
        (b * (∏ p ∈ Nat.primesLE y, (1 - 1 / (p : ℝ))⁻¹)) /
          (Real.exp Real.eulerMascheroniConstant * (Real.log y + Real.log c)) := by
      field_simp [hlogy0]
    _ ≤ ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
        (Real.exp Real.eulerMascheroniConstant * (Real.log y + Real.log c)) :=
      div_le_div_of_nonneg_right habund (mul_pos (Real.exp_pos _) hdenpos).le
    _ ≤ ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) :=
      div_le_div_of_nonneg_left hsigma0 (mul_pos (Real.exp_pos _) hloglogn)
        (mul_le_mul_of_nonneg_left hdenbound (Real.exp_pos _).le)
    _ = (ArithmeticFunction.sigma 1 n : ℝ) /
        (Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)) := by
      rw [div_div]
      congr 1
      ring

/-- The two epsilon envelopes expressing the sharp Gronwall limsup. -/
theorem gronwall_envelopes (ε : ℝ) (hε : 0 < ε) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (ArithmeticFunction.sigma 1 n : ℝ) /
        (Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)) ≤ 1 + ε) ∧
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      1 - ε ≤ (ArithmeticFunction.sigma 1 n : ℝ) /
        (Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n))) :=
  ⟨GronwallUpperEnvelope.gronwall_upper_envelope ε hε, gronwall_lower_envelope ε hε⟩

#print axioms gronwall_lower_envelope
#print axioms gronwall_envelopes

end D5.S3.Weil.GronwallLowerEnvelope

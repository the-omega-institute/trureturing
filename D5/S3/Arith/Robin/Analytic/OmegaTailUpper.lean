/- GID: D5/S3/Arith/Robin/Analytic/OmegaTailUpper
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTailUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Optimized Rankin upper bounds and the zero-rate distinct-prime endpoint. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Finite Euler products, prime-counting bounds, and the distinct-prime tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTailUpper

/-- The logarithmic counting scale. -/
def scale (x : ℝ) : ℝ := log x / log (log x)

/-- The second-order distinct-prime threshold. -/
def threshold (lambda x : ℝ) : ℝ :=
  scale x + lambda * scale x / log (log x)

/-- Positive integers up to the real cutoff with more distinct prime factors than the threshold. -/
def tailCount (lambda x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => threshold lambda x < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card

/-- The optimizing root of the Rankin parameter. -/
def a (s : ℝ) : ℝ := s * sin (π / s) / π

/-- The optimized exponential rate. -/
def rate (lambda s : ℝ) : ℝ := s * (1 - lambda - log (a s))

private lemma scale_pos {x : ℝ} (hx : exp 1 < x) : 0 < scale x := by
  have hl : 1 < log x := (lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx
  exact div_pos (zero_lt_one.trans hl) (log_pos hl)

private lemma scale_tendsto : Tendsto scale atTop atTop := by
  change Tendsto (fun x : ℝ => log x / log (log x)) atTop atTop
  have h := (isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_log_atTop
  have hn : ∀ᶠ x : ℝ in atTop, 0 < log (log x) / log x := by
    filter_upwards [eventually_gt_atTop (exp 1)] with x hx
    have hl : 1 < log x := (lt_log_iff_exp_lt (lt_trans (exp_pos _) hx)).mpr hx
    exact div_pos (log_pos hl) (zero_lt_one.trans hl)
  simpa only [scale, inv_div, Function.comp_def, id_eq] using
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h, hn⟩)

private lemma rankin_log_cancellation (lambda s c x : ℝ)
    (hx : 1 < log x) (hc : 0 < c) :
    (s * log x - threshold lambda x * log (c * (log x) ^ s)) / scale x =
      -log c - s * lambda - lambda * log c / log (log x) := by
  have hL : 0 < log x := zero_lt_one.trans hx
  have hell : log (log x) ≠ 0 := (log_pos hx).ne'
  rw [log_mul hc.ne' (rpow_pos_of_pos hL s).ne', log_rpow hL]
  dsimp [threshold, scale]
  field_simp
  <;> ring

private lemma rankin_log_limit (lambda s : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      (s * log x - threshold lambda x * log (c * (log x) ^ s)) / scale x)
      atTop (𝓝 (-log c - s * lambda)) := by
  have he : Tendsto (fun x : ℝ => lambda * log c / log (log x)) atTop (𝓝 0) :=
    (tendsto_log_atTop.comp tendsto_log_atTop).const_div_atTop _
  have h := (tendsto_const_nhds (x := -log c - s * lambda) (f := atTop)).sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [tendsto_log_atTop.eventually_gt_atTop 1] with x hx
  exact (rankin_log_cancellation lambda s c x hx hc).symm

private lemma a_pos {s : ℝ} (hs : 1 < s) : 0 < a s := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ht0 : 0 < π / s := div_pos pi_pos hs0
  have htpi : π / s < π := (div_lt_self pi_pos hs)
  exact div_pos (mul_pos hs0 (sin_pos_of_pos_of_lt_pi ht0 htpi)) pi_pos

private lemma optimized_coefficient {s : ℝ} (hs : 1 < s) (lambda : ℝ) :
    π * (a s ^ s) ^ (1 / s) / sin (π / s) - log (a s ^ s) - s * lambda =
      rate lambda s := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hsin := sin_pos_of_pos_of_lt_pi (div_pos pi_pos hs0) (div_lt_self pi_pos hs)
  rw [← rpow_mul (a_pos hs).le, mul_one_div_cancel hs0.ne', rpow_one,
    log_rpow (a_pos hs)]
  dsimp [a, rate]
  field_simp
  <;> ring

private lemma rate_one_bound {s : ℝ} (hs : π ≤ s) :
    0 ≤ rate 1 s ∧ rate 1 s ≤ π ^ 2 / (3 * s) := by
  have hs0 : 0 < s := pi_pos.trans_le hs
  have ht0 : 0 < π / s := div_pos pi_pos hs0
  have ht1 : π / s ≤ 1 := (div_le_one hs0).mpr hs
  have ha : a s = sin (π / s) / (π / s) := by
    dsimp [a]
    field_simp
  have hsmall : 1 - (π / s) ^ 2 / 6 ≤ a s := by
    rw [ha, le_div_iff₀ ht0]
    nlinarith [sin_gt_sub_cube ht0]
  have hau : a s ≤ 1 := by
    rw [ha, div_le_one ht0]
    exact sin_le ht0.le
  have hal : (1 : ℝ) / 2 ≤ a s := by
    have ht2 : (π / s) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hap : 0 < a s := by linarith
  have hlog : -log (a s) ≤ 2 * (1 - a s) := by
    have h := one_sub_inv_le_log_of_pos hap
    have hinv : (a s)⁻¹ - 1 ≤ 2 * (1 - a s) := by
      apply (mul_le_mul_iff_left₀ hap).mp
      rw [sub_mul, inv_mul_cancel₀ hap.ne']
      nlinarith
    linarith
  constructor
  · dsimp [rate]
    have := log_nonpos hap.le hau
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left hlog hs0.le
    have he : s * ((π / s) ^ 2 / 3) = π ^ 2 / (3 * s) := by
      field_simp
      <;> ring
    dsimp [rate]
    rw [← he]
    nlinarith

private lemma rate_one_tendsto : Tendsto (rate 1) atTop (𝓝 0) := by
  have hup : Tendsto (fun s : ℝ => π ^ 2 / (3 * s)) atTop (𝓝 0) :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).const_div_atTop _
  apply squeeze_zero' _ _ hup
  · filter_upwards [eventually_ge_atTop π] with s hs
    exact (rate_one_bound hs).1
  · filter_upwards [eventually_ge_atTop π] with s hs
    exact (rate_one_bound hs).2

private lemma log_count_limit_of_upper
    (hupper : ∀ (s : ℝ), 1 < s → ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ x : ℝ in atTop,
        (tailCount 1 x : ℝ) ≤ exp ((rate 1 s + epsilon) * scale x)) :
    Tendsto (fun x : ℝ => log (1 + (tailCount 1 x : ℝ)) / scale x)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hsmall := rate_one_tendsto.eventually_lt_const (by linarith : 0 < epsilon / 4)
  obtain ⟨s, hsπ, hsr⟩ :=
    ((eventually_gt_atTop π).and hsmall).exists
  have hs : 1 < s := (by linarith [pi_gt_three] : (1 : ℝ) < π).trans hsπ
  have hsnonneg := (rate_one_bound hsπ.le).1
  have hscale : Tendsto (fun x : ℝ => log 2 / scale x) atTop (𝓝 0) :=
    scale_tendsto.const_div_atTop _
  have hscaleSmall := hscale.eventually_lt_const (by linarith : 0 < epsilon / 2)
  filter_upwards [hupper s hs (epsilon / 4) (by linarith), hscaleSmall,
    eventually_gt_atTop (exp 1)] with x hx hxsmall hxlarge
  have hy := scale_pos hxlarge
  have ht : 0 ≤ (rate 1 s + epsilon / 4) * scale x := by positivity
  have hexp : 1 ≤ exp ((rate 1 s + epsilon / 4) * scale x) := one_le_exp ht
  have hlog : log (1 + (tailCount 1 x : ℝ)) ≤
      log 2 + (rate 1 s + epsilon / 4) * scale x := by
    calc
      _ ≤ log (2 * exp ((rate 1 s + epsilon / 4) * scale x)) :=
        log_le_log (by positivity) (by linarith)
      _ = _ := by rw [log_mul (by norm_num) (exp_pos _).ne', log_exp]
  have hnonneg : 0 ≤ log (1 + (tailCount 1 x : ℝ)) / scale x := by
    exact div_nonneg (log_nonneg (by
      have hN : (0 : ℝ) ≤ tailCount 1 x := Nat.cast_nonneg _
      linarith)) hy.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hbound := (div_le_div_iff_of_pos_right hy).mpr hlog
  rw [add_div, mul_div_cancel_right₀ _ hy.ne'] at hbound
  linarith

private def rankinWeight (s z : ℝ) (n : ℕ) : ℝ :=
  z ^ ArithmeticFunction.cardDistinctFactors n * (n : ℝ) ^ (-s)

private lemma rankinWeight_one (s z : ℝ) : rankinWeight s z 1 = 1 := by
  simp [rankinWeight]

private lemma rankinWeight_nonneg {s z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ rankinWeight s z n := by
  exact mul_nonneg (pow_nonneg hz _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private lemma rankinWeight_mul (s z : ℝ) {m n : ℕ} (h : m.Coprime n) :
    rankinWeight s z (m * n) = rankinWeight s z m * rankinWeight s z n := by
  simp only [rankinWeight, ArithmeticFunction.cardDistinctFactors_mul h,
    pow_add, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

private lemma rankinWeight_prime_pow (s z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    rankinWeight s z (p ^ k) = z * ((p : ℝ) ^ (-s)) ^ k := by
  rw [rankinWeight, ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp hk,
    pow_one, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
    mul_comm (k : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]

private lemma prime_decay {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ) ^ (-s) ∧ (p : ℝ) ^ (-s) < 1 := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg p) _, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hs)

private lemma rankinWeight_local_summable {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖rankinWeight s z (p ^ k)‖) := by
  have hq := prime_decay hs hp
  have hgeom := (summable_geometric_of_lt_one hq.1 hq.2).mul_left z
  apply (summable_nat_add_iff 1).mp
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (rankinWeight_nonneg hz _),
    rankinWeight_prime_pow s z hp (Nat.add_one_ne_zero _)]
  exact (summable_nat_add_iff 1).mpr hgeom

private lemma rankinWeight_local_tsum {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, rankinWeight s z (p ^ k)) =
      1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s)) := by
  have hsum := (rankinWeight_local_summable hs hz hp).of_norm
  have hq := prime_decay hs hp
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, rankinWeight_one]
  simp_rw [rankinWeight_prime_pow s z hp (Nat.add_one_ne_zero _), pow_succ]
  simp_rw [show ∀ k : ℕ, z * (((p : ℝ) ^ (-s)) ^ k * (p : ℝ) ^ (-s)) =
    (z * (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ k by intro k; ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq.1 hq.2]
  rfl

private lemma rankinWeight_factored_sum {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z)
    (P : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers P => rankinWeight s z n)
      (∏ p ∈ P with p.Prime,
        (1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s)))) := by
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (rankinWeight_one s z) (rankinWeight_mul s z)
    (fun hp => rankinWeight_local_summable hs hz hp) P).2
  convert h using 1
  apply prod_congr rfl
  intro p hp
  exact (rankinWeight_local_tsum hs hz (mem_filter.mp hp).2).symm

private lemma prefix_factored {N n : ℕ} (hn : n ∈ Icc 1 N) :
    n ∈ Nat.factoredNumbers (Icc 1 N) := by
  have hn' := mem_Icc.mp hn
  rw [Nat.mem_factoredNumbers_iff_forall_le]
  refine ⟨by omega, fun p hpn hp _ => mem_Icc.mpr ⟨hp.one_lt.le, hpn.trans hn'.2⟩⟩

private lemma rankinWeight_prefix_le_product {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z)
    (N : ℕ) :
    (∑ n ∈ Icc 1 N, rankinWeight s z n) ≤
      ∏ p ∈ Icc 1 N with p.Prime,
        (1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s))) := by
  let S : Finset (Nat.factoredNumbers (Icc 1 N)) :=
    (Icc 1 N).attach.image (fun n => ⟨n.1, prefix_factored n.2⟩)
  have h := sum_le_hasSum S (fun n _ => rankinWeight_nonneg hz n)
    (rankinWeight_factored_sum hs hz (Icc 1 N))
  have heq : (∑ n ∈ S, rankinWeight s z n) = ∑ n ∈ Icc 1 N, rankinWeight s z n := by
    rw [show S = (Icc 1 N).attach.image (fun n => ⟨n.1, prefix_factored n.2⟩) from rfl,
      sum_image]
    · exact sum_attach _ _
    · intro a _ b _ hab
      exact Subtype.ext (congrArg (fun n : Nat.factoredNumbers (Icc 1 N) => (n : ℕ)) hab)
  rwa [heq] at h

private lemma rankin_point {s z x T : ℝ} (hs : 0 < s) (hz : 1 ≤ z)
    (hx : 0 < x) {n : ℕ} (hn : n ∈ Icc 1 ⌊x⌋₊)
    (hT : T < (ArithmeticFunction.cardDistinctFactors n : ℝ)) :
    1 ≤ x ^ s * z ^ (-T) * rankinWeight s z n := by
  have hn' := mem_Icc.mp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn'.1)
  have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le hx.le)
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hw : z ^ T * x ^ (-s) ≤ rankinWeight s z n := by
    unfold rankinWeight
    rw [← Real.rpow_natCast]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hz hT.le)
      (Real.rpow_le_rpow_of_nonpos hnpos hnle (neg_nonpos.mpr hs.le))
      (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hzpos.le _)
  have hc : 0 ≤ x ^ s * z ^ (-T) := by positivity
  have h := mul_le_mul_of_nonneg_left hw hc
  have heq : x ^ s * z ^ (-T) * (z ^ T * x ^ (-s)) = 1 := by
    rw [Real.rpow_neg hzpos.le, Real.rpow_neg hx.le]
    have hxs := (Real.rpow_pos_of_pos hx s).ne'
    have hzt := (Real.rpow_pos_of_pos hzpos T).ne'
    field_simp
  rwa [heq] at h

private lemma rankin_finite_product {s z x T : ℝ} (hs : 0 < s) (hz : 1 ≤ z)
    (hx : 0 < x) :
    (((Icc 1 ⌊x⌋₊).filter (fun n => T <
      (ArithmeticFunction.cardDistinctFactors n : ℝ))).card : ℝ) ≤
      x ^ s * z ^ (-T) *
        ∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
          (1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s))) := by
  let S := (Icc 1 ⌊x⌋₊).filter (fun n => T <
    (ArithmeticFunction.cardDistinctFactors n : ℝ))
  let C := x ^ s * z ^ (-T)
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, C * rankinWeight s z n := by
      apply sum_le_sum
      intro n hn
      exact rankin_point hs hz hx (mem_filter.mp hn).1 (mem_filter.mp hn).2
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, C * rankinWeight s z n := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun n _ _ => mul_nonneg hC (rankinWeight_nonneg hz0 n))
    _ = C * ∑ n ∈ Icc 1 ⌊x⌋₊, rankinWeight s z n := by rw [mul_sum]
    _ ≤ C * ∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
        (1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s))) :=
      mul_le_mul_of_nonneg_left (rankinWeight_prefix_le_product hs hz0 _) hC

private lemma inverse_euler_product_le_pseries {s : ℝ} (hs : 1 < s) (P : Finset ℕ) :
    (∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-s))⁻¹) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-s)
      map_one' := by simp
      map_mul' := by
        intro m n
        simp only [Nat.cast_mul]
        exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n) }
  calc
    (∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-s))⁻¹) =
        ∑' n : Nat.factoredNumbers P, (n : ℝ) ^ (-s) :=
      EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers (f := f) hsum P
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) :=
      hsum.tsum_subtype_le _ _ (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

private lemma local_euler_majorant {s z : ℝ} (hs : 0 < s)
    {p : ℕ} (hp : p.Prime) :
    1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s)) ≤
      (1 + z * (p : ℝ) ^ (-s)) * (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hq := prime_decay hs hp
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (sub_pos.mpr hq.2)).mpr
  rw [add_mul, div_mul_cancel₀ _ (sub_pos.mpr hq.2).ne']
  nlinarith

private lemma rankin_euler_majorant {s z x T : ℝ} (hs : 1 < s) (hz : 1 ≤ z)
    (hx : 0 < x) :
    (((Icc 1 ⌊x⌋₊).filter (fun n => T <
      (ArithmeticFunction.cardDistinctFactors n : ℝ))).card : ℝ) ≤
      x ^ s * z ^ (-T) * (∑' n : ℕ, (n : ℝ) ^ (-s)) *
        ∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s)) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hC : 0 ≤ x ^ s * z ^ (-T) := by positivity
  have hP : 0 ≤ ∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
      (1 + z * (p : ℝ) ^ (-s)) := by
    apply prod_nonneg
    intro p _
    exact add_nonneg zero_le_one (mul_nonneg hz0 (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hprod :
      (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
        (1 + z * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s)))) ≤
      (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s))) *
        (∑' n : ℕ, (n : ℝ) ^ (-s)) := by
    calc
      _ ≤ ∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
          ((1 + z * (p : ℝ) ^ (-s)) * (1 - (p : ℝ) ^ (-s))⁻¹) := by
        apply prod_le_prod₀
        · intro p hp
          have hq := prime_decay hs0 (mem_filter.mp hp).2
          exact add_nonneg zero_le_one
            (div_nonneg (mul_nonneg hz0 hq.1) (sub_pos.mpr hq.2).le)
        · intro p hp
          exact local_euler_majorant hs0 (mem_filter.mp hp).2
      _ = (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s))) *
          (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 - (p : ℝ) ^ (-s))⁻¹) := by
        rw [prod_mul_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (inverse_euler_product_le_pseries hs _) hP
  exact (rankin_finite_product hs0 hz hx).trans
    ((mul_le_mul_of_nonneg_left hprod hC).trans_eq (by ring))

private lemma rankin_exponential_bound {s z x T : ℝ} (hs : 1 < s) (hz : 1 ≤ z)
    (hx : 0 < x) :
    (((Icc 1 ⌊x⌋₊).filter (fun n => T <
      (ArithmeticFunction.cardDistinctFactors n : ℝ))).card : ℝ) ≤
      Real.exp (s * Real.log x - T * Real.log z +
        Real.log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) +
        ∑ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, Real.log (1 + z * (p : ℝ) ^ (-s))) := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hZ : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) :=
    tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hZ1 : 0 < 1 + ∑' n : ℕ, (n : ℝ) ^ (-s) := by linarith
  have hp : 0 ≤ ∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s)) := by
    apply prod_nonneg
    intro p _
    exact add_nonneg zero_le_one (mul_nonneg hzpos.le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have h := rankin_euler_majorant (T := T) hs hz hx
  have h' :
      x ^ s * z ^ (-T) * (∑' n : ℕ, (n : ℝ) ^ (-s)) *
        (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s))) ≤
      x ^ s * z ^ (-T) * (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) *
        (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s))) := by
    gcongr
    linarith
  refine h.trans (h'.trans_eq ?_)
  have heprod :
      (∏ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, (1 + z * (p : ℝ) ^ (-s))) =
      Real.exp (∑ p ∈ Icc 1 ⌊x⌋₊ with p.Prime, Real.log (1 + z * (p : ℝ) ^ (-s))) := by
    rw [Real.exp_sum]
    apply prod_congr rfl
    intro p _
    rw [Real.exp_log (by positivity)]
  rw [heprod, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hzpos,
    ← Real.exp_log hZ1, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_exp]
  ring

section Kernel
open Set

private theorem power_kernel_integral {s c : ℝ} (hs : 1 < s) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => s * c / (u ^ s + c)) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), s * c / (u ^ s + c)) =
        Real.pi * c ^ (1 / s) / Real.sin (Real.pi / s) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hsne : s ≠ 0 := hs0.ne'
  have hp : 1 / s ∈ Ioo (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hs0, (div_lt_one hs0).mpr hs⟩
  let A : ℝ := c ^ (1 / s)
  have hA : 0 < A := Real.rpow_pos_of_pos hc _
  have hAs : A ^ s = c := by
    dsimp [A]
    simpa only [one_div] using Real.rpow_inv_rpow hc.le hsne
  let phi : ℝ → ℝ := fun t => A * t ^ (1 / s)
  let phi' : ℝ → ℝ := fun t => A * ((1 / s) * t ^ (1 / s - 1))
  let g : ℝ → ℝ := fun u => s * c / (u ^ s + c)
  have hphi : phi '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mul_pos hA (Real.rpow_pos_of_pos ht _)
    · intro hu
      refine ⟨(u / A) ^ s, Real.rpow_pos_of_pos (div_pos hu hA) _, ?_⟩
      dsimp only [phi]
      rw [one_div, Real.rpow_rpow_inv (div_pos hu hA).le hsne]
      field_simp [hA.ne']
  have hinj : InjOn phi (Ioi (0 : ℝ)) := by
    intro t ht u hu he
    have he' : t ^ (1 / s) = u ^ (1 / s) := mul_left_cancel₀ hA.ne' he
    exact (Real.rpow_left_inj ht.le hu.le (ne_of_gt hp.1)).mp he'
  have hder (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt phi (phi' t) (Ioi 0) t := by
    exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).const_mul A).hasDerivWithinAt
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      |phi' t| • g (phi t) = A * Real.rpowIntegrand₀₁ (1 / s) t 1 := by
    have ht0 : 0 < t := ht
    have hphis : (phi t) ^ s = c * t := by
      dsimp only [phi]
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg ht.le _), hAs, one_div,
        Real.rpow_inv_rpow ht.le hsne]
    have hdpos : 0 < phi' t :=
      mul_pos hA (mul_pos hp.1 (Real.rpow_pos_of_pos ht _))
    rw [abs_of_pos hdpos, smul_eq_mul,
      Real.rpowIntegrand₀₁_eq_pow_div hp ht.le zero_le_one]
    dsimp only [g, phi']
    rw [hphis]
    field_simp [hc.ne', hsne, ne_of_gt (add_pos ht0 zero_lt_one)]
    <;> ring
  have hi : IntegrableOn (fun t => A * Real.rpowIntegrand₀₁ (1 / s) t 1) (Ioi 0) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one).const_mul A
  have hsubst := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hder hinj g
  have hsubstI := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hder hinj g
  rw [hphi] at hsubst hsubstI
  have hi' : IntegrableOn (fun t => |phi' t| • g (phi t)) (Ioi (0 : ℝ)) :=
    IntegrableOn.congr_fun hi (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
  refine ⟨hsubstI.mpr hi', ?_⟩
  change (∫ u in Ioi (0 : ℝ), g u) = _
  rw [hsubst, setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.power_normalizer _ hp]
  dsimp only [A]
  rw [show Real.pi * (1 / s) = Real.pi / s by ring]
  ring

end Kernel

private lemma prime_counting_ratio :
    Tendsto (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / (t / log t))
      atTop (𝓝 1) := by
  have h :=
    D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder.pi_normalized
  change Tendsto (fun t : ℝ => log t * (Nat.primeCounting ⌊t⌋₊ : ℝ) / t)
    atTop (𝓝 1) at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  field_simp [(log_pos ht).ne']
  <;> ring

private def logWeight (s z t : ℝ) : ℝ := log (1 + z / t ^ s)

private def abelKernel (s z t : ℝ) : ℝ := s * z / (t * (t ^ s + z))

private lemma logWeight_deriv {s z t : ℝ} (hz : 0 < z) (ht : 0 < t) :
    HasDerivAt (logWeight s z) (-abelKernel s z t) t := by
  have hp : 0 < t ^ s := rpow_pos_of_pos ht _
  have hh : 0 < 1 + z / t ^ s := by positivity
  have h := ((hasDerivAt_const t z).div
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')) hp.ne').const_add 1
  convert h.log hh.ne' using 1
  · rfl
  · dsimp [abelKernel]
    rw [rpow_sub ht, rpow_one]
    field_simp
    <;> ring

private lemma abelKernel_continuousOn {s z a b : ℝ} (hz : 0 < z) (ha : 0 < a) :
    ContinuousOn (abelKernel s z) (Set.Icc a b) := by
  have hp : ContinuousOn (fun t : ℝ => t ^ s) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (ha.trans_le ht.1)))
  apply continuousOn_const.div (continuousOn_id.mul (hp.add continuousOn_const))
  intro t ht
  have ht0 := ha.trans_le ht.1
  exact mul_ne_zero ht0.ne' (add_pos (rpow_pos_of_pos ht0 _) hz).ne'

private lemma finite_prime_abel {s z a b : ℝ} (hz : 0 < z) (ha : 0 < a)
    (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, logWeight s z p) =
      logWeight s z b * (Nat.primeCounting ⌊b⌋₊ : ℝ) -
      logWeight s z a * (Nat.primeCounting ⌊a⌋₊ : ℝ) +
      ∫ t in Set.Ioc a b, abelKernel s z t *
        (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then 1 else 0
  have hc (t : ℝ) : (∑ p ∈ Icc 0 ⌊t⌋₊, c p) =
      (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    simp only [c, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [← Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_card_eq_primeCounting]
  have hint : IntegrableOn (deriv (logWeight s z)) (Set.Icc a b) := by
    have hi : IntegrableOn (fun t => -abelKernel s z t) (Set.Icc a b) :=
      (abelKernel_continuousOn hz ha).neg.integrableOn_Icc
    exact hi.congr_fun (fun t ht =>
      (logWeight_deriv hz (ha.trans_le ht.1)).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c ha.le hab
    (fun t ht => (logWeight_deriv hz (ha.trans_le ht.1)).differentiableAt) hint
  simp_rw [hc] at h
  have hs : (∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, logWeight s z p * c p) =
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, logWeight s z p := by
    simp [sum_filter, c, mul_ite]
  rw [hs] at h
  have hi : (∫ t in Set.Ioc a b, deriv (logWeight s z) t *
      (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
      -(∫ t in Set.Ioc a b, abelKernel s z t *
        (Nat.primeCounting ⌊t⌋₊ : ℝ)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(logWeight_deriv hz (ha.trans ht.1)).deriv]
    ring
  rw [hi, sub_neg_eq_add] at h
  exact h

private lemma finite_prime_abel_upper {s z a b K : ℝ} (hs : 0 < s) (hz : 0 < z)
    (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K)
    (hcount : ∀ t ∈ Set.Icc a b, (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ K * t)
    (hint : IntegrableOn (fun t : ℝ => s * z / (t ^ s + z)) (Set.Ioi 0)) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, logWeight s z p) ≤
      logWeight s z b * (Nat.primeCounting ⌊b⌋₊ : ℝ) +
      K * ∫ t in Set.Ioi (0 : ℝ), s * z / (t ^ s + z) := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then 1 else 0
  have hc (t : ℝ) : (∑ p ∈ Icc 0 ⌊t⌋₊, c p) =
      (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    simp only [c, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [← Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_card_eq_primeCounting]
  have hprod : IntegrableOn (fun t : ℝ => abelKernel s z t *
      (Nat.primeCounting ⌊t⌋₊ : ℝ)) (Set.Ioc a b) := by
    have hh : IntegrableOn (fun t : ℝ => abelKernel s z t *
        ∑ p ∈ Icc 0 ⌊t⌋₊, c p) (Set.Icc a b) :=
      integrableOn_mul_sum_Icc c ha.le
        (abelKernel_continuousOn hz ha).integrableOn_Icc (m := 0)
    simp_rw [hc] at hh
    exact hh.mono_set Set.Ioc_subset_Icc_self
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun t ht => ha.trans ht.1
  have hmajor : IntegrableOn (fun t : ℝ => K * (s * z / (t ^ s + z)))
      (Set.Ioc a b) := IntegrableOn.mono_set (hint.const_mul K) hsub
  have hbound := setIntegral_mono_on hprod hmajor measurableSet_Ioc
    (fun t ht => by
      have ht0 := ha.trans ht.1
      have hk : 0 ≤ abelKernel s z t := by
        dsimp [abelKernel]
        positivity
      have hh := mul_le_mul_of_nonneg_left
        (hcount t ⟨ht.1.le, ht.2⟩) hk
      convert hh using 1
      dsimp [abelKernel]
      field_simp
      <;> ring)
  have hwhole : (∫ t in Set.Ioc a b, s * z / (t ^ s + z)) ≤
      ∫ t in Set.Ioi (0 : ℝ), s * z / (t ^ s + z) := by
    apply setIntegral_mono_set hint _ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (mul_nonneg hs.le hz.le)
      (add_nonneg (rpow_nonneg ht.le _) hz.le)
  rw [integral_const_mul] at hbound
  have hnonneg : 0 ≤ logWeight s z a * (Nat.primeCounting ⌊a⌋₊ : ℝ) := by
    apply mul_nonneg _ (Nat.cast_nonneg _)
    dsimp [logWeight]
    apply log_nonneg
    have : 0 ≤ z / a ^ s := by positivity
    linarith
  rw [finite_prime_abel hz ha hab]
  have hscale := mul_le_mul_of_nonneg_left hwhole hK
  linarith

private lemma prime_counting_linear_above_power {alpha eta : ℝ}
    (halpha : 0 < alpha) (heta : 0 < eta) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, L ^ alpha ≤ t →
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (1 + eta) / (alpha * log L) * t := by
  have hratio := prime_counting_ratio.eventually_lt_const
    (lt_add_of_pos_right (1 : ℝ) heta)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hratio
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop halpha).eventually_ge_atTop A] with L hL hLA
  intro t ht
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hp : 0 < L ^ alpha := rpow_pos_of_pos hL0 _
  have ht0 : 0 < t := hp.trans_le ht
  have hlog : alpha * log L ≤ log t := by
    rw [← log_rpow hL0]
    exact log_le_log hp ht
  have hlogpos : 0 < alpha * log L := mul_pos halpha (log_pos hL)
  have hlogt : 0 < log t := hlogpos.trans_le hlog
  have hc := (div_le_iff₀ (div_pos ht0 hlogt)).mp
    ((hA t (hLA.trans ht)).le)
  have hdiv : t / log t ≤ t / (alpha * log L) :=
    div_le_div_of_nonneg_left ht0.le hlogpos hlog
  calc
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (1 + eta) * (t / log t) := hc
    _ ≤ (1 + eta) * (t / (alpha * log L)) :=
      mul_le_mul_of_nonneg_left hdiv (by linarith)
    _ = _ := by ring

private lemma prime_counting_le_endpoint {b : ℝ} (hb : 0 ≤ b) :
    (Nat.primeCounting ⌊b⌋₊ : ℝ) ≤ b := by
  have hc : Nat.primeCounting ⌊b⌋₊ ≤ ⌊b⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_zero]
    exact (card_filter_le _ _).trans (by simp)
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hb)

private lemma finite_prime_head {s z b : ℝ} (hs : 0 ≤ s) (hz : 0 < z)
    (hb : 0 ≤ b) :
    (∑ p ∈ Nat.primesLE ⌊b⌋₊, logWeight s z p) ≤ b * log (1 + z) := by
  have hsum : (∑ p ∈ Nat.primesLE ⌊b⌋₊, logWeight s z p) ≤
      (Nat.primeCounting ⌊b⌋₊ : ℝ) * log (1 + z) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    calc
      _ ≤ ∑ _p ∈ Nat.primesLE ⌊b⌋₊, log (1 + z) := by
        apply sum_le_sum
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
        have hpow : 1 ≤ (p : ℝ) ^ s := one_le_rpow hp1 hs
        dsimp [logWeight]
        apply log_le_log (by positivity)
        have hdiv : z / (p : ℝ) ^ s ≤ z :=
          (div_le_iff₀ (zero_lt_one.trans_le hpow)).mpr (by nlinarith)
        linarith
      _ = _ := by simp
  exact hsum.trans (mul_le_mul_of_nonneg_right (prime_counting_le_endpoint hb)
    (log_nonneg (by linarith)))

private lemma prime_weight_endpoint {s z b : ℝ} (hz : 0 < z) (hb : 0 < b) :
    logWeight s z b * (Nat.primeCounting ⌊b⌋₊ : ℝ) ≤ z * b / b ^ s := by
  have hlog : logWeight s z b ≤ z / b ^ s := by
    have h := log_le_sub_one_of_pos (show 0 < 1 + z / b ^ s by positivity)
    dsimp [logWeight]
    linarith
  calc
    _ ≤ (z / b ^ s) * (Nat.primeCounting ⌊b⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _)
    _ ≤ (z / b ^ s) * b :=
      mul_le_mul_of_nonneg_left (prime_counting_le_endpoint hb.le) (by positivity)
    _ = _ := by ring

private lemma finite_prime_weight_upper {s z a b K : ℝ} (hs : 0 < s) (hz : 0 < z)
    (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K)
    (hcount : ∀ t ∈ Set.Icc a b, (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ K * t)
    (hint : IntegrableOn (fun t : ℝ => s * z / (t ^ s + z)) (Set.Ioi 0)) :
    (∑ p ∈ Nat.primesLE ⌊b⌋₊, logWeight s z p) ≤
      a * log (1 + z) + z * b / b ^ s +
        K * ∫ t in Set.Ioi (0 : ℝ), s * z / (t ^ s + z) := by
  classical
  have hsplit : (∑ p ∈ Nat.primesLE ⌊b⌋₊, logWeight s z p) =
      (∑ p ∈ Nat.primesLE ⌊a⌋₊, logWeight s z p) +
        ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, logWeight s z p := by
    have hsubset := Nat.primesLE_mono (Nat.floor_le_floor hab)
    have hdiff : Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ =
        (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨hpb, hp⟩, hn⟩
        exact ⟨⟨by by_contra h; exact hn ⟨by omega, hp⟩, hpb⟩, hp⟩
      · rintro ⟨⟨hap, hpb⟩, hp⟩
        exact ⟨⟨hpb, hp⟩, by rintro ⟨hpa, _⟩; omega⟩
    rw [← hdiff, add_comm]
    exact (sum_sdiff hsubset).symm
  rw [hsplit]
  have hh := finite_prime_head hs.le hz ha.le
  have ht := finite_prime_abel_upper hs hz ha hab hK hcount hint
  have he := prime_weight_endpoint (s := s) hz (ha.trans_le hab)
  linarith

private lemma small_prime_head_limit {alpha s c : ℝ} (ha : alpha < 1)
    (hs : 0 < s) (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ alpha * log (1 + c * t ^ s) / (t / log t))
      atTop (𝓝 0) := by
  have h1 := (isLittleO_log_rpow_atTop (sub_pos.mpr ha)).tendsto_div_nhds_zero
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (sub_pos.mpr ha)).tendsto_div_nhds_zero
  have hm : Tendsto (fun t : ℝ =>
      log (1 + c) * (log t / t ^ (1 - alpha)) +
        s * (log t ^ (2 : ℕ) / t ^ (1 - alpha))) atTop (𝓝 0) := by
    simpa only [rpow_two, mul_zero, zero_add] using
      (h1.const_mul (log (1 + c))).add (h2.const_mul s)
  apply squeeze_zero' _ _ hm
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    exact div_nonneg (mul_nonneg (rpow_nonneg ht0 _) (log_nonneg (by
      have h := mul_nonneg hc.le (rpow_nonneg ht0 s)
      linarith)))
      (div_nonneg ht0 (log_pos ht).le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hp : 1 ≤ t ^ s := one_le_rpow ht.le hs.le
    have hlog : log (1 + c * t ^ s) ≤ log (1 + c) + s * log t := by
      calc
        _ ≤ log ((1 + c) * t ^ s) := log_le_log (by positivity) (by nlinarith)
        _ = _ := by rw [log_mul (by positivity) (rpow_pos_of_pos ht0 s).ne',
          log_rpow ht0]
    have hmul := mul_le_mul_of_nonneg_left hlog (rpow_nonneg ht0.le alpha)
    have hdiv := div_le_div_of_nonneg_right hmul (div_nonneg ht0.le (log_pos ht).le)
    convert hdiv using 1
    rw [rpow_sub ht0, rpow_one]
    field_simp
    <;> ring

private lemma prime_endpoint_limit {s : ℝ} (hs : 1 < s) (c : ℝ) :
    Tendsto (fun x : ℝ => c * log x ^ s / x ^ (s - 1)) atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using
    ((isLittleO_log_rpow_rpow_atTop s (sub_pos.mpr hs)).tendsto_div_nhds_zero.const_mul c)

private lemma prime_weight_upper {s c epsilon : ℝ} (hs : 1 < s) (hc : 0 < c)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1 + c * log x ^ s / (p : ℝ) ^ s)) ≤
        (π * c ^ (1 / s) / sin (π / s) + epsilon) * scale x := by
  let J : ℝ := π * c ^ (1 / s) / sin (π / s)
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hsin : 0 < sin (π / s) :=
    sin_pos_of_pos_of_lt_pi (div_pos pi_pos hs0) (div_lt_self pi_pos hs)
  have hJ : 0 < J := div_pos (mul_pos pi_pos (rpow_pos_of_pos hc _)) hsin
  let d : ℝ := epsilon / 4
  let alpha : ℝ := J / (J + d)
  let eta : ℝ := d / (J + d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hJd : 0 < J + d := add_pos hJ hd
  have halpha : 0 < alpha := div_pos hJ hJd
  have halpha1 : alpha < 1 := (div_lt_one hJd).mpr (by linarith)
  have heta : 0 < eta := div_pos hd hJd
  have hcoeff : (1 + eta) / alpha * J = J + epsilon / 2 := by
    dsimp [alpha, eta, d]
    field_simp
    <;> ring
  have hhead : Tendsto (fun x : ℝ =>
      log x ^ alpha * log (1 + c * log x ^ s) / scale x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, scale] using
      (small_prime_head_limit halpha1 hs0 hc).comp tendsto_log_atTop
  have hcount := tendsto_log_atTop.eventually (prime_counting_linear_above_power halpha heta)
  have hend := prime_endpoint_limit hs c
  filter_upwards [eventually_gt_atTop (exp 1), hcount,
    hhead.eventually_lt_const (show (0 : ℝ) < epsilon / 4 by positivity),
    hend.eventually_lt_const (show (0 : ℝ) < epsilon / 4 by positivity),
    scale_tendsto.eventually_ge_atTop 1] with x hx hcountx hheadx hendx hscale
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hL0 : 0 < log x := zero_lt_one.trans hL
  have hlog : 0 < log (log x) := log_pos hL
  have hscale0 := scale_pos hx
  have hz : 0 < c * log x ^ s := mul_pos hc (rpow_pos_of_pos hL0 _)
  have ha : 0 < log x ^ alpha := rpow_pos_of_pos hL0 _
  have hab : log x ^ alpha ≤ x :=
    (rpow_le_self_of_one_le hL.le halpha1.le).trans
      ((log_le_sub_one_of_pos hx0).trans (by linarith))
  have hK : 0 ≤ (1 + eta) / (alpha * log (log x)) := by positivity
  have hbound := finite_prime_weight_upper hs0 hz ha hab hK
    (fun t ht => hcountx t ht.1)
    (power_kernel_integral hs hz).1
  have hIntegral := (power_kernel_integral hs hz).2
  have hroot : (c * log x ^ s) ^ (1 / s) = c ^ (1 / s) * log x := by
    rw [mul_rpow hc.le (rpow_nonneg hL0.le s), ← rpow_mul hL0.le,
      mul_one_div_cancel hs0.ne', rpow_one]
  have hnormal : (1 + eta) / (alpha * log (log x)) *
      (∫ t in Set.Ioi (0 : ℝ), s * (c * log x ^ s) / (t ^ s + c * log x ^ s)) =
        (J + epsilon / 2) * scale x := by
    rw [hIntegral, hroot]
    calc
      _ = ((1 + eta) / alpha * J) * scale x := by
        dsimp [J, scale]
        ring
      _ = _ := by rw [hcoeff]
  rw [hnormal] at hbound
  have hheadbound : log x ^ alpha * log (1 + c * log x ^ s) ≤
      epsilon / 4 * scale x := (div_le_iff₀ hscale0).mp hheadx.le
  have hendpoint : c * log x ^ s * x / x ^ s ≤ epsilon / 4 * scale x := by
    have heq : c * log x ^ s * x / x ^ s = c * log x ^ s / x ^ (s - 1) := by
      rw [rpow_sub hx0, rpow_one]
      field_simp
    rw [heq]
    exact hendx.le.trans (le_mul_of_one_le_right (by positivity) hscale)
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, logWeight s (c * log x ^ s) p) ≤ _
  linarith


/-- The optimized Rankin upper bound for large distinct-prime counts. -/
theorem upper_bound (lambda : ℝ) (_hlambda : lambda ≤ 1) {s epsilon : ℝ}
    (hs : 1 < s) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      (tailCount lambda x : ℝ) ≤ exp ((rate lambda s + epsilon) * scale x) := by
  let c : ℝ := a s ^ s
  let C : ℝ := 1 + ∑' n : ℕ, (n : ℝ) ^ (-s)
  have hc : 0 < c := rpow_pos_of_pos (a_pos hs) s
  have hnorm := (rankin_log_limit lambda s hc).add
    (scale_tendsto.const_div_atTop (log C))
  simp only [add_zero] at hnorm
  have hfront := hnorm.eventually_lt_const
    (by linarith : -log c - s * lambda < -log c - s * lambda + epsilon / 2)
  have hzlim : Tendsto (fun x : ℝ => c * (log x) ^ s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr
      ((tendsto_rpow_atTop (zero_lt_one.trans hs)).comp tendsto_log_atTop)
  have hweight := prime_weight_upper hs hc (by linarith : 0 < epsilon / 2)
  have hopt : π * c ^ (1 / s) / sin (π / s) - log c - s * lambda =
      rate lambda s := optimized_coefficient hs lambda
  filter_upwards [hfront, hweight, hzlim.eventually_ge_atTop 1,
    eventually_gt_atTop (exp 1)] with x hfront hweight hz hxlarge
  have hx : 0 < x := (exp_pos 1).trans hxlarge
  have hy : 0 < scale x := scale_pos hxlarge
  have hfront' := hfront.le
  rw [← add_div] at hfront'
  have hprefix := (div_le_iff₀ hy).mp hfront'
  have hcut : (Icc 1 ⌊x⌋₊).filter Nat.Prime = Nat.primesLE ⌊x⌋₊ := by
    rw [Nat.primesLE_eq_filter_Ioc_zero]
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc, Nat.succ_le_iff]
  have hsum :
      (∑ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
        log (1 + (c * (log x) ^ s) * (p : ℝ) ^ (-s))) =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1 + c * (log x) ^ s / (p : ℝ) ^ s) := by
    rw [hcut]
    apply sum_congr rfl
    intro p _
    simp only [rpow_neg (Nat.cast_nonneg p), div_eq_mul_inv]
  have hE : s * log x - threshold lambda x * log (c * (log x) ^ s) + log C +
      (∑ p ∈ Icc 1 ⌊x⌋₊ with p.Prime,
        log (1 + (c * (log x) ^ s) * (p : ℝ) ^ (-s))) ≤
      (rate lambda s + epsilon) * scale x := by
    rw [hsum]
    calc
      _ ≤ (-log c - s * lambda + epsilon / 2) * scale x +
          (π * c ^ (1 / s) / sin (π / s) + epsilon / 2) * scale x :=
        add_le_add hprefix hweight
      _ = _ := by
        rw [← add_mul]
        congr 1
        linarith [hopt]
  exact (show (tailCount lambda x : ℝ) ≤ _ from
    rankin_exponential_bound (T := threshold lambda x) hs hz hx).trans
      (exp_le_exp.mpr hE)


/-- The second-order endpoint has a vanishing logarithmic counting rate. -/
theorem result :
    Tendsto (fun x : ℝ => log (1 + (tailCount 1 x : ℝ)) / scale x)
      atTop (𝓝 0) :=
  log_count_limit_of_upper (fun s hs epsilon hepsilon =>
    upper_bound 1 le_rfl hs hepsilon)

end D5.S3.Arith.Robin.Analytic.OmegaTailUpper

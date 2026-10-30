/- GID: D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   mirror-E: none
   anchors: [D5/S3/Analytic/XuYangMillsRemainder/Result]
   utility: none
   digest: Original Mills smoothness, origin asymptotic and signed exponential remainder multiplier orders.

This module is an unfrozen checkpoint for the general-parameter Mills
classification.  It keeps the original normalization from `Result.D` and
records both complete equivalence chains as a proposition.  The
general-parameter coefficient representation, weighted-moment comparison,
infinity asymptotic and classification proof remain open here.
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import D5.S3.Analytic.XuYangMillsRemainder.Result

/-! The original general-parameter target and its analytic proof obligations. -/

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
noncomputable section

namespace D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open D5.S3.Analytic.XuYangMillsRemainder.Result

/-! The original source normalization. -/

def F (n : ℕ) (a x : ℝ) : ℝ := (-1 : ℝ) ^ n * D n x a

def I (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, (1 + v ^ 2) ^ j

def B (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, v ^ 2 * (1 + v ^ 2) ^ j

def theta (j : ℕ) : ℝ := (1 - I j / B j) / 2

def globalNonnegative (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ F n a x

def globalNonpositive (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ -F n a x

def completelyMonotone (n : ℕ) (a : ℝ) : Prop :=
  CompletelyMonotoneOn (F n a)

def theorem21 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ,
    ((globalNonnegative n a ↔ completelyMonotone n a) ∧
      (completelyMonotone n a ↔ a ≤ theta (n - 2))) ∧
    ((globalNonpositive n a ↔ CompletelyMonotoneOn (fun x => -F n a x)) ∧
      (CompletelyMonotoneOn (fun x => -F n a x) ↔ a ≥ theta (n - 1)))

/-! Smoothness of the original Gaussian normalization, before any sign argument. -/

private theorem gaussian_integrable : Integrable (fun t : ℝ => exp (-t ^ 2 / 2)) := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ext t
  congr 1
  ring

private theorem mills_primitive (x : ℝ) :
    millsRatio x = exp (x ^ 2 / 2) *
      ((∫ t in Ioi (0 : ℝ), exp (-t ^ 2 / 2)) - ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2)) := by
  rw [millsRatio]
  congr 1
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (gaussian_integrable.integrableOn (s := Ioi (0 : ℝ)))
    (gaussian_integrable.integrableOn (s := Ioi x))
  linarith

private theorem mills_smooth : ContDiff ℝ ∞ millsRatio := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => exp (-t ^ 2 / 2)) := by fun_prop
  have hp : ContDiff ℝ ∞ (fun x : ℝ => ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2)) := by
    apply contDiff_infty_iff_deriv.mpr
    constructor
    · intro x
      exact (hg.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
    · convert hg using 1
      ext x
      exact hg.continuous.deriv_integral _ 0 x
  have hm : millsRatio = fun x : ℝ => exp (x ^ 2 / 2) *
      ((∫ t in Ioi (0 : ℝ), exp (-t ^ 2 / 2)) - ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2)) :=
    funext mills_primitive
  rw [hm]
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => exp (x ^ 2 / 2))).mul
    (contDiff_const.sub hp)

/-! The exact finite truncation has a removable singularity after rescaling. -/

private theorem rescaled_f (n : ℕ) (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    x ^ (2 * n) * F n a x = (-1 : ℝ) ^ n *
      (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k))) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      x ^ (2 * n) * ((-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) =
        (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)) := by
    have hn : 2 * n = 2 * k + 2 * (n - k) := by
      have := (Finset.mem_Icc.mp hk).2
      omega
    rw [hn, pow_add]
    field_simp
  have hsum : x ^ (2 * n) *
      (∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) =
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  unfold F D
  calc
    _ = (-1 : ℝ) ^ n * (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        x ^ (2 * n) *
          (∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k))) := by ring
    _ = _ := by rw [hsum]

private theorem zero_endpoint (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n) * F n a x) (𝓝[>] (0 : ℝ))
      (𝓝 (-u n a (a - 2))) := by
  let P : ℝ → ℝ := fun x => (-1 : ℝ) ^ n *
      (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)))
  have hY : Continuous (Y a (a - 2)) := by
    have hm := mills_smooth.continuous
    unfold Y
    fun_prop
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hz : P 0 = -u n a (a - 2) := by
    have hs : (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k * u k a (a - 2) * (0 : ℝ) ^ (2 * (n - k))) =
        (-1 : ℝ) ^ n * u n a (a - 2) := by
      calc
        _ = (-1 : ℝ) ^ n * u n a (a - 2) * (0 : ℝ) ^ (2 * (n - n)) := by
          apply Finset.sum_eq_single n
          · intro k hk hkn
            have hklt : k < n := lt_of_le_of_ne (Finset.mem_Icc.mp hk).2 hkn
            simp [zero_pow (by omega : 2 * (n - k) ≠ 0)]
          · intro h
            exact (h (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).elim
        _ = _ := by simp
    dsimp [P]
    rw [zero_pow (by omega : 2 * n ≠ 0), zero_mul, zero_sub, hs]
    have hsgn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination -u n a (a - 2) * hsgn
  rw [← hz]
  apply (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rescaled_f n a (ne_of_gt hx)).symm

private theorem regularity_and_origin (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    ContDiffOn ℝ ∞ (F n a) (Ioi 0) ∧
      Tendsto (fun x : ℝ => x ^ (2 * n) * F n a x) (𝓝[>] (0 : ℝ))
        (𝓝 (-u n a (a - 2))) := by
  refine ⟨?_, zero_endpoint n hn a⟩
  have hm := mills_smooth.contDiffOn (s := Ioi (0 : ℝ))
  unfold F D Y
  apply contDiffOn_const.mul
  apply ContDiffOn.sub
  · fun_prop
  · apply contDiffOn_const.add
    apply ContDiffOn.sum
    intro k _
    apply contDiffOn_const.div (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (ne_of_gt hx)

/-! A complete-monotonicity predicate contains the zeroth-order sign. -/

private theorem completelyMonotone_zero_sign {f : ℝ → ℝ}
    (hf : CompletelyMonotoneOn f) : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
  intro x hx
  have h := hf.2 0 x hx
  simpa using h

private theorem cm_sign_projections (n : ℕ) (a : ℝ) :
    completelyMonotone n a → globalNonnegative n a := by
  intro h
  exact completelyMonotone_zero_sign h

private theorem neg_cm_sign_projection (n : ℕ) (a : ℝ) :
    CompletelyMonotoneOn (fun x => -F n a x) → globalNonpositive n a := by
  intro h
  exact completelyMonotone_zero_sign h

/-! Endpoint signs forced by a finite one-sided asymptotic limit. -/

private theorem nonnegative_sign_forces_nonpositive_limit {f : ℝ → ℝ}
    {p : ℕ} {u : ℝ}
    (hlim : Tendsto (fun x : ℝ => x ^ p * f x) (𝓝[>] (0 : ℝ)) (𝓝 (-u)))
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ f x) :
    u ≤ 0 := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ p * f x ∈ Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (pow_nonneg hx.le p) (hpos x hx)
  have hclosed : -u ∈ Ici (0 : ℝ) := isClosed_Ici.mem_of_tendsto hlim hev
  change 0 ≤ -u at hclosed
  linarith

/-! Necessary coefficient signs for the actual Gaussian Mills remainder. -/

private theorem positive_sign_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : globalNonnegative n a) : u n a (a - 2) ≤ 0 :=
  nonnegative_sign_forces_nonpositive_limit (zero_endpoint n hn a) h

private theorem positive_cm_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : completelyMonotone n a) : u n a (a - 2) ≤ 0 :=
  positive_sign_necessary n hn a (cm_sign_projections n a h)

private theorem negative_sign_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : globalNonpositive n a) : 0 ≤ u n a (a - 2) := by
  have hl : Tendsto (fun x : ℝ => x ^ (2 * n) * (-F n a x)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(-u n a (a - 2)))) := by
    simpa only [neg_mul_eq_mul_neg, neg_neg] using (zero_endpoint n hn a).neg
  have hu := nonnegative_sign_forces_nonpositive_limit hl h
  linarith

private theorem negative_cm_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : CompletelyMonotoneOn (fun x => -F n a x)) : 0 ≤ u n a (a - 2) :=
  negative_sign_necessary n hn a (neg_cm_sign_projection n a h)

/-! Signed finite exponential remainders: the two required multiplier orders. -/

private theorem normalized_exp_remainder (r : ℕ) {y : ℝ} (hy : 0 < y) :
    (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
      y ^ (r + 1) =
      (∫ s in (0 : ℝ)..1, (1 - s) ^ r * exp (-s * y)) / r.factorial := by
  have hc : ContDiff ℝ (r + 1 : ℕ) exp := contDiff_exp.of_le (by exact_mod_cast le_top)
  have he (j : ℕ) : iteratedDeriv j exp = exp := by
    simpa using iteratedDeriv_exp_const_mul j 1
  have ht := taylor_integral_remainder (x := -y) (x₀ := 0) hc.contDiffOn
  have hpoly : taylorWithinEval exp r (uIcc 0 (-y)) 0 (-y) =
      ∑ j ∈ Finset.range (r + 1), (-y) ^ j / j.factorial := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by linarith : (0 : ℝ) ≠ -y))
      ((contDiff_exp : ContDiff ℝ ω exp).of_le (by exact_mod_cast le_top)).contDiffAt
      left_mem_uIcc]
    simp [he, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hpoly] at ht
  have hrepr : D5.S3.Analytic.ExpRemainderDifferences.R r (-y) =
      ∫ t in (0 : ℝ)..(-y), ((-y - t) ^ r / r.factorial) * exp t := by
    unfold D5.S3.Analytic.ExpRemainderDifferences.R
    rw [ht]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by linarith : (0 : ℝ) ≠ -y))
      hc.contDiffAt ht]
    simp [he, smul_eq_mul]
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => ((-y - t) ^ r / r.factorial) * exp t)
    (a := (0 : ℝ)) (b := 1) (-y)
  have hpoint (s : ℝ) : ((-y - s * -y) ^ r / r.factorial) * exp (s * -y) =
      ((-y) ^ r / r.factorial) * ((1 - s) ^ r * exp (-s * y)) := by
    rw [show -y - s * -y = -y * (1 - s) by ring, mul_pow,
      show s * -y = -s * y by ring]
    ring
  simp only [zero_mul, one_mul, smul_eq_mul, hpoint,
    intervalIntegral.integral_const_mul] at hsub
  rw [hrepr, ← hsub]
  have hsgn : (-1 : ℝ) ^ (r + 1) * (-y) ^ (r + 1) = y ^ (r + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have hy0 : y ≠ 0 := hy.ne'
  let J : ℝ := ∫ s in (0 : ℝ)..1, (1 - s) ^ r * exp (-s * y)
  change (-1 : ℝ) ^ (r + 1) * (-y * ((-y) ^ r / r.factorial * J)) /
    y ^ (r + 1) = J / r.factorial
  have hnum : (-1 : ℝ) ^ (r + 1) * (-y * ((-y) ^ r / r.factorial * J)) =
      y ^ (r + 1) * (J / r.factorial) := by
    calc
      _ = ((-1 : ℝ) ^ (r + 1) * (-y) ^ (r + 1)) * (J / r.factorial) := by
        rw [pow_succ (-y)]
        ring
      _ = _ := by rw [hsgn]
  rw [hnum, mul_div_cancel_left₀ _ (pow_ne_zero _ hy0)]

private theorem exp_remainder_ratio_strict_anti (r : ℕ) :
    StrictAntiOn (fun y : ℝ =>
      (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
        y ^ (r + 1)) (Ioi 0) := by
  intro y hy z hz hyz
  dsimp only
  rw [normalized_exp_remainder r hy, normalized_exp_remainder r hz]
  apply div_lt_div_of_pos_right _ (by positivity : (0 : ℝ) < r.factorial)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) (by fun_prop) (by fun_prop)
  · intro s hs
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [hs.2]) _)
    apply exp_le_exp.mpr
    nlinarith [hs.1]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    apply mul_lt_mul_of_pos_left _ (by positivity : (0 : ℝ) < (1 - 1 / 2) ^ r)
    apply exp_lt_exp.mpr
    linarith

private theorem lower_normalized_exp_remainder (r : ℕ) {y : ℝ} (hy : 0 < y) :
    (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
      y ^ r =
      (∫ q in (0 : ℝ)..y, (1 - q / y) ^ r * exp (-q)) / r.factorial := by
  have h := normalized_exp_remainder r hy
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (fun q : ℝ => (1 - q / y) ^ r * exp (-q))
    (a := (0 : ℝ)) (b := 1) y
  simp only [zero_mul, one_mul, smul_eq_mul, mul_div_cancel_right₀ _ hy.ne'] at hsub
  rw [← hsub]
  have hy0 : y ≠ 0 := hy.ne'
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp at h ⊢
  rw [pow_succ] at h
  linear_combination h

private theorem exp_remainder_ratio_strict_mono (r : ℕ) :
    StrictMonoOn (fun y : ℝ =>
      (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
        y ^ r) (Ioi 0) := by
  intro y hy z hz hyz
  dsimp only
  rw [lower_normalized_exp_remainder r hy, lower_normalized_exp_remainder r hz]
  apply div_lt_div_of_pos_right _ (by positivity : (0 : ℝ) < r.factorial)
  have hmono : (∫ q in (0 : ℝ)..y, (1 - q / y) ^ r * exp (-q)) ≤
      ∫ q in (0 : ℝ)..y, (1 - q / z) ^ r * exp (-q) := by
    apply intervalIntegral.integral_mono_on hy.le (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro q hq
    apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
    apply pow_le_pow_left₀
    · exact sub_nonneg.mpr ((div_le_one hy).mpr hq.2)
    · have hdiv : q / z ≤ q / y := div_le_div_of_nonneg_left hq.1 (by exact hy) hyz.le
      linarith
  have htail : 0 < ∫ q in y..z, (1 - q / z) ^ r * exp (-q) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ hyz
    intro q hq
    exact mul_pos (pow_pos (sub_pos.mpr ((div_lt_one hz).mpr hq.2)) _) (exp_pos _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (show IntervalIntegrable (fun q : ℝ => (1 - q / z) ^ r * exp (-q)) volume 0 y by
      apply Continuous.intervalIntegrable; fun_prop)
    (show IntervalIntegrable (fun q : ℝ => (1 - q / z) ^ r * exp (-q)) volume y z by
      apply Continuous.intervalIntegrable; fun_prop)
  linarith

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

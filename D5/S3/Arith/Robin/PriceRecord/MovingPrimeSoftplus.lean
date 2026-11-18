/- GID: D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none -/

import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! A uniform Abel comparison for a softplus centered at a real prime cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus

open Real Filter MeasureTheory Asymptotics Set Finset
open QuantitativePrimeAbel (primeInterval theta_error_log_power)
open scoped Topology

/-- Softplus applied to the negative scaled logarithmic distance from the real center. -/
def weight (P s t : ℝ) : ℝ :=
  log (1 + exp (-s * |log (t / P)|))

private def smoothWeight (P k t : ℝ) : ℝ :=
  log (1 + exp (k * log (t / P)))

private def smoothSlope (P k t : ℝ) : ℝ :=
  (k / t) * exp (k * log (t / P)) / (1 + exp (k * log (t / P)))

private theorem smooth_derivative {P k t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    HasDerivAt (smoothWeight P k) (smoothSlope P k t) t := by
  have hdiv := (hasDerivAt_id t).div_const P
  have hlog := hdiv.log (div_ne_zero ht.ne' hP.ne')
  have hexp := (hlog.const_mul k).exp
  convert (hexp.const_add 1).log (by positivity) using 1
  · rfl
  · simp only [smoothSlope, id_eq]
    have he : 1 / P / (t / P) = 1 / t := by
      field_simp
    rw [he]
    ring

private theorem continuousOn_smoothSlope (P k : ℝ) (hP : 0 < P) :
    ContinuousOn (smoothSlope P k) (Ioi 0) := by
  have hlog : ContinuousOn (fun t : ℝ => log (t / P)) (Ioi 0) :=
    (continuous_id.continuousOn.div_const P).log fun t ht =>
      div_ne_zero (mem_Ioi.mp ht).ne' hP.ne'
  have hexp : ContinuousOn (fun t : ℝ => exp (k * log (t / P))) (Ioi 0) :=
    continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)
  exact ((continuousOn_const.div continuousOn_id (fun t ht => (mem_Ioi.mp ht).ne')).mul
    hexp).div (continuousOn_const.add hexp) fun t _ => by positivity

private theorem weight_bounds (P t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ weight P s t ∧ weight P s t ≤ log 2 := by
  have he : exp (-s * |log (t / P)|) ≤ 1 := exp_le_one_iff.mpr (by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (abs_nonneg _))
  exact ⟨log_nonneg (le_add_of_nonneg_right (exp_pos _).le),
    log_le_log (by positivity) (by linarith)⟩

private theorem weight_eq_left {P s t : ℝ} (ht : 0 < t) (htP : t ≤ P) :
    weight P s t = smoothWeight P s t := by
  have hP := ht.trans_le htP
  have hlog := log_nonpos (div_nonneg ht.le hP.le) ((div_le_one hP).mpr htP)
  rw [weight, smoothWeight, abs_of_nonpos hlog]
  simp only [neg_mul_neg]

private theorem weight_eq_right {P s t : ℝ} (hP : 0 < P) (hPt : P ≤ t) :
    weight P s t = smoothWeight P (-s) t := by
  rw [weight, smoothWeight, abs_of_nonneg (log_nonneg ((le_div_iff₀ hP).mpr (by simpa)))]

private theorem smooth_theta_comparison {P k a b E : ℝ} (hP : 0 < P)
    (ha : 0 < a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hθ : ∀ t ∈ Icc a b, |Chebyshev.theta t - t| ≤ E)
    (hw : ∀ t ∈ Icc a b, 0 ≤ smoothWeight P k t ∧ smoothWeight P k t ≤ log 2) :
    |(∑ p ∈ primeInterval a b, smoothWeight P k p * log p) -
      ∫ t in a..b, smoothWeight P k t| ≤ 3 * log 2 * E := by
  let f := smoothWeight P k
  let g := smoothSlope P k
  let c : ℕ → ℝ := fun n => if n.Prime then log n else 0
  have htpos : ∀ t ∈ Icc a b, 0 < t := fun _ ht => ha.trans_le ht.1
  have hd : ∀ t ∈ Icc a b, HasDerivAt f (g t) t :=
    fun t ht => smooth_derivative hP (htpos t ht)
  have hfc : ContinuousOn f (Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) :=
    (continuousOn_smoothSlope P k hP).mono htpos
  have hgi := hgc.intervalIntegrable_of_Icc (μ := volume) hab
  have hd' : Set.EqOn (deriv f) g (Icc a b) := fun t ht => (hd t ht).deriv
  have hdi : IntegrableOn (deriv f) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hgi |>.congr_fun
      (fun t ht => (hd' ht).symm) measurableSet_Icc
  have hc (t : ℝ) : ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n = Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have hs : (∑ p ∈ primeInterval a b, f p * log p) =
      f b * Chebyshev.theta b - f a * Chebyshev.theta a -
        ∫ t in a..b, g t * Chebyshev.theta t := by
    have h := sum_mul_eq_sub_sub_integral_mul (c := c) ha.le hab
      (fun t ht => (hd t ht).differentiableAt) hdi
    simp only [hc, ← intervalIntegral.integral_of_le hab] at h
    have hInt : (∫ t in a..b, deriv f t * Chebyshev.theta t) =
        ∫ t in a..b, g t * Chebyshev.theta t :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [uIcc_of_le hab] at ht
        rw [hd' ht])
    rw [hInt] at h
    simpa only [primeInterval, Finset.sum_filter, c, mul_ite, mul_zero] using h
  have hi : (∫ t in a..b, f t) =
      f b * b - f a * a - ∫ t in a..b, g t * t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := f) (v := id) (u' := g) (v' := fun _ => 1)
      (by rwa [uIcc_of_le hab]) continuous_id.continuousOn
      (fun t ht => hd t (by
        rw [min_eq_left hab, max_eq_right hab] at ht
        exact Ioo_subset_Icc_self ht))
      (fun t _ => hasDerivAt_id t) hgi (intervalIntegrable_const)
    simpa only [id_eq, mul_one] using h
  have hm : IntervalIntegrable (fun t => g t * t) volume a b :=
    (hgc.mul continuous_id.continuousOn).intervalIntegrable_of_Icc hab
  have hmθ : IntervalIntegrable (fun t => g t * Chebyshev.theta t) volume a b := by
    have h := integrableOn_mul_sum_Icc c (m := 0) ha.le
      (g := g) ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hgi)
    simpa only [hc] using (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr h
  have hdiff : (∫ t in a..b, g t * Chebyshev.theta t) - (∫ t in a..b, g t * t) =
      ∫ t in a..b, g t * (Chebyshev.theta t - t) := by
    rw [← intervalIntegral.integral_sub hmθ hm]
    exact intervalIntegral.integral_congr fun t _ => (mul_sub _ _ _).symm
  have hvar : (∫ t in a..b, |g t|) ≤ log 2 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := f) (fun t ht => hd t (by rwa [uIcc_of_le hab] at ht)) hgi
    obtain hk | hk := le_total 0 k
    · rw [intervalIntegral.integral_congr (g := g) (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact abs_of_nonneg (by dsimp [g, smoothSlope]; have := htpos t ht; positivity)), hFTC]
      linarith [(hw a ⟨le_rfl, hab⟩).1, (hw b ⟨hab, le_rfl⟩).2]
    · rw [intervalIntegral.integral_congr (g := fun t => -g t) (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact abs_of_nonpos (by
          dsimp [g, smoothSlope]
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg
              (div_nonpos_of_nonpos_of_nonneg hk (htpos t ht).le) (exp_pos _).le)
            (by positivity))), intervalIntegral.integral_neg, hFTC]
      linarith [(hw b ⟨hab, le_rfl⟩).1, (hw a ⟨le_rfl, hab⟩).2]
  have herror :
      |∫ t in a..b, g t * (Chebyshev.theta t - t)| ≤ log 2 * E := by
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    apply le_trans _ (mul_le_mul_of_nonneg_right hvar hE)
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on hab ?_ (hgi.abs.mul_const E) ?_
    · have h := hmθ.sub hm
      simpa only [← mul_sub] using h.abs
    · intro t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hθ t ht) (abs_nonneg _)
  have hend (t : ℝ) (ht : t ∈ Icc a b) : |f t * (Chebyshev.theta t - t)| ≤ log 2 * E := by
    rw [abs_mul, abs_of_nonneg ((hw t ht).1)]
    exact mul_le_mul (hw t ht).2 (hθ t ht) (abs_nonneg _) (log_nonneg (by norm_num))
  rw [hs, hi, show
    f b * Chebyshev.theta b - f a * Chebyshev.theta a -
      (∫ t in a..b, g t * Chebyshev.theta t) -
      (f b * b - f a * a - ∫ t in a..b, g t * t) =
    (f b * (Chebyshev.theta b - b) - f a * (Chebyshev.theta a - a)) -
      ((∫ t in a..b, g t * Chebyshev.theta t) - (∫ t in a..b, g t * t)) by ring,
    hdiff]
  refine (abs_sub _ _).trans ?_
  have hends := (abs_sub (f b * (Chebyshev.theta b - b)) _).trans
    (add_le_add (hend b ⟨hab, le_rfl⟩) (hend a ⟨le_rfl, hab⟩))
  linarith only [hends, herror]

/-- The absolute error of the moving softplus sum against theta, compared to
its Lebesgue integral, is controlled by the uniform theta discrepancy. -/
theorem softplus_theta_window {P s E : ℝ} (hP : 0 < P) (hs : 0 ≤ s)
    (hE : 0 ≤ E) (hθ : ∀ t ∈ Icc (P / 2) (2 * P), |Chebyshev.theta t - t| ≤ E) :
    |(∑ p ∈ primeInterval (P / 2) (2 * P), weight P s p * log p) -
        ∫ t in P / 2..2 * P, weight P s t| ≤ 6 * log 2 * E := by
  have hhalf : 0 < P / 2 := by positivity
  have hleft : P / 2 ≤ P := by linarith
  have hright : P ≤ 2 * P := by linarith
  have hcompare (a b k : ℝ) (ha : 0 < a) (hab : a ≤ b)
      (hsub : Icc a b ⊆ Icc (P / 2) (2 * P))
      (heq : Set.EqOn (weight P s) (smoothWeight P k) (Icc a b)) :
      |(∑ p ∈ primeInterval a b, weight P s p * log p) -
        ∫ t in a..b, weight P s t| ≤ 3 * log 2 * E := by
    have h := smooth_theta_comparison (k := k) hP ha hab hE
      (fun t ht => hθ t (hsub ht)) (fun t ht => heq ht ▸ weight_bounds P t hs)
    have hsum : (∑ p ∈ primeInterval a b, weight P s p * log p) =
        ∑ p ∈ primeInterval a b, smoothWeight P k p * log p := by
      apply sum_congr rfl
      intro p hp
      simp only [primeInterval, Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [heq ⟨(Nat.floor_lt ha.le).mp hp.1.1 |>.le,
        (Nat.le_floor_iff (ha.le.trans hab)).mp hp.1.2⟩]
    rw [hsum, intervalIntegral.integral_congr (by rwa [uIcc_of_le hab])]
    exact h
  have hl := hcompare (P / 2) P s hhalf hleft (Icc_subset_Icc_right hright)
    (fun t ht => weight_eq_left (hhalf.trans_le ht.1) ht.2)
  have hr := hcompare P (2 * P) (-s) hP hright (Icc_subset_Icc_left hleft)
    (fun _ ht => weight_eq_right hP ht.1)
  have hC (a b : ℝ) (ha : 0 < a) : ContinuousOn (weight P s) (Icc a b) := by
    have hlog : ContinuousOn (fun t : ℝ => log (t / P)) (Icc a b) :=
      (continuous_id.continuousOn.div_const P).log fun t ht =>
        div_ne_zero (ha.trans_le ht.1).ne' hP.ne'
    have hexp : ContinuousOn (fun t : ℝ => exp (-s * |log (t / P)|)) (Icc a b) :=
      continuous_exp.comp_continuousOn (continuousOn_const.mul hlog.abs)
    unfold weight
    exact (continuousOn_const.add hexp).log
      (fun t _ => (add_pos_of_pos_of_nonneg zero_lt_one (exp_pos _).le).ne')
  have hint := intervalIntegral.integral_add_adjacent_intervals
    ((hC (P / 2) P hhalf).intervalIntegrable_of_Icc hleft)
    ((hC P (2 * P) hP).intervalIntegrable_of_Icc hright)
  have hsum : primeInterval (P / 2) (2 * P) =
      primeInterval (P / 2) P ∪ primeInterval P (2 * P) := by
    unfold primeInterval
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc
      (Nat.floor_le_floor hleft) (Nat.floor_le_floor hright)]
  have hdis : Disjoint (primeInterval (P / 2) P) (primeInterval P (2 * P)) := by
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    simp only [primeInterval, Finset.mem_filter, Finset.mem_Ioc] at hp hq
    exact (not_lt_of_ge hp.1.2) hq.1.1
  rw [hsum, Finset.sum_union hdis, ← hint]
  rw [show (∑ p ∈ primeInterval (P / 2) P, weight P s p * log p) +
        (∑ p ∈ primeInterval P (2 * P), weight P s p * log p) -
        ((∫ t in P / 2..P, weight P s t) + (∫ t in P..2 * P, weight P s t)) =
      ((∑ p ∈ primeInterval (P / 2) P, weight P s p * log p) -
        (∫ t in P / 2..P, weight P s t)) +
      ((∑ p ∈ primeInterval P (2 * P), weight P s p * log p) -
        (∫ t in P..2 * P, weight P s t)) by ring]
  exact (abs_add_le _ _).trans (by linarith)

end D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus

/- GID: D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none -/

import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import D5.S3.Weil.ZetaBridge.FermiMellin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SumIntegralComparisons

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
private theorem softplus_theta_window {P s E : ℝ} (hP : 0 < P) (hs : 0 ≤ s)
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
    ((hC (P / 2) P hhalf).intervalIntegrable_of_Icc (μ := volume) hleft)
    ((hC P (2 * P) hP).intervalIntegrable_of_Icc (μ := volume) hright)
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

private theorem log_window_lower {P t : ℝ} (hP : 4 ≤ P) (ht : P / 2 ≤ t) :
    log P / 2 ≤ log t := by
  have h0 : (0 : ℝ) < 2 := by norm_num
  have hlog := log_le_log (show 0 < P / 2 by linarith) ht
  have h4 : log (4 : ℝ) ≤ log P := log_le_log (by norm_num) hP
  have he : log (4 : ℝ) = log 2 + log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul h0.ne' h0.ne']
  rw [log_div (by linarith : P ≠ 0) h0.ne'] at hlog
  linarith

private theorem theta_window_log_bound (N : ℕ) :
    ∀ᶠ P : ℝ in atTop, ∀ t ∈ Icc (P / 2) (2 * P),
      |Chebyshev.theta t - t| ≤ 2 ^ (N + 1) * P / log P ^ N := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((theta_error_log_power N).bound
    (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (2 * T), eventually_ge_atTop (4 : ℝ)] with P hPT hP
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hlogP : 0 < log P := log_pos (by linarith)
  have hlogt : 0 < log t := log_pos (by linarith [ht.1])
  have hθ := hT t (by linarith [ht.1])
  simp only [Real.norm_eq_abs, one_mul, abs_of_pos (div_pos ht0 (pow_pos hlogt N))] at hθ
  calc
    _ ≤ t / log t ^ N := hθ
    _ ≤ (2 * P) / (log P / 2) ^ N := by
      exact div_le_div₀ (by linarith) ht.2 (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) (log_window_lower hP ht.1) N)
    _ = _ := by rw [div_pow, pow_succ, div_div_eq_mul_div]; ring

private theorem theta_comparison_tendsto {a C : ℝ} {s : ℝ → ℝ}
    (hs : ∀ᶠ P in atTop, 0 ≤ s P ∧ s P ≤ C * log P ^ a) (hC : 0 < C) :
    Tendsto (fun P : ℝ => (s P / P) *
      ((∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p * log p) -
        ∫ t in P / 2..2 * P, weight P (s P) t)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt a
  let K : ℝ := 6 * log 2 * 2 ^ (N + 1) * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlimit : Tendsto (fun P : ℝ => K * log P ^ (a - (N : ℝ))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hN)).comp tendsto_log_atTop).const_mul K
    simpa only [Function.comp_apply, neg_sub, mul_zero] using h
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlimit
  filter_upwards [theta_window_log_bound N, hs, eventually_gt_atTop (1 : ℝ)] with P hθ hsP hP
  have hP0 : 0 < P := by linarith
  have hlog : 0 < log P := log_pos hP
  have hbound := softplus_theta_window hP0 hsP.1
    (by positivity : 0 ≤ 2 ^ (N + 1) * P / log P ^ N) hθ
  simp only [Function.comp_apply, abs_mul, abs_of_nonneg (div_nonneg hsP.1 hP0.le)]
  calc
    _ ≤ (s P / P) * (6 * log 2 * (2 ^ (N + 1) * P / log P ^ N)) :=
      mul_le_mul_of_nonneg_left hbound (div_nonneg hsP.1 hP0.le)
    _ = (6 * log 2 * 2 ^ (N + 1)) * s P / log P ^ N := by
      field_simp [hP0.ne', hlog.ne']
    _ ≤ (6 * log 2 * 2 ^ (N + 1)) * (C * log P ^ a) / log P ^ N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsP.2 (by positivity))
        (pow_nonneg hlog.le _)
    _ = _ := by rw [rpow_sub hlog, rpow_natCast]; unfold K; ring

private def softplus (u : ℝ) : ℝ := log (1 + exp (-u))

private theorem softplus_continuous : Continuous softplus := by
  exact (continuous_const.add (continuous_exp.comp continuous_neg)).log
    (fun _ => (add_pos_of_pos_of_nonneg zero_lt_one (exp_pos _).le).ne')

private theorem softplus_nonneg (u : ℝ) : 0 ≤ softplus u :=
  log_nonneg (le_add_of_nonneg_right (exp_pos _).le)

private theorem softplus_le_exp (u : ℝ) : softplus u ≤ exp (-u) := by
  simpa only [softplus, add_sub_cancel_left] using
    log_le_sub_one_of_pos (show 0 < 1 + exp (-u) by positivity)

private theorem fermi_mass :
    (∫ u : ℝ in Ioi 0, softplus u) = π ^ 2 / 12 := by
  let f : ℝ → ℝ := fun u => u / (exp u + 1)
  let cf : ℝ → ℂ := fun u => (u : ℂ) ^ ((2 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)
  open D5.S3.Weil.ZetaBridge.FermiMellin in
  have hC : IntegrableOn cf (Ioi 0) :=
    fermi_mellin_integrable 1 one_pos 2 (by norm_num)
  have hcast (u : ℝ) : cf u = (f u : ℂ) := by
    unfold cf f
    norm_num [Complex.ofReal_div, Complex.ofReal_add]
  have hf : IntegrableOn f (Ioi 0) := by
    apply hC.re.congr
    exact Eventually.of_forall (fun u => by
      simp only [hcast, RCLike.re_eq_complex_re, Complex.ofReal_re])
  have hCmass : (∫ u in Ioi (0 : ℝ), cf u) = ((π ^ 2 / 12 : ℝ) : ℂ) := by
    open D5.S3.Weil.ZetaBridge.FermiMellin in
    have h := fermi_mellin_eq_of_ne_one 1 one_pos (2 : ℂ) (by norm_num) (by norm_num)
    change (∫ u in Ioi (0 : ℝ), cf u) = _ at h
    have hG : Complex.Gamma 2 = 1 := by simp
    rw [hG, riemannZeta_two, show (1 - (2 : ℂ)) = -1 by norm_num, Complex.cpow_neg_one] at h
    norm_num [Complex.ofReal_div, Complex.ofReal_pow] at h ⊢
    exact h.trans (by ring)
  have hmass : (∫ u in Ioi (0 : ℝ), f u) = π ^ 2 / 12 := by
    have h := (integral_re hC).trans (congrArg Complex.re hCmass)
    simpa only [hcast, RCLike.re_eq_complex_re, Complex.ofReal_re] using h
  have hi : IntegrableOn softplus (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).mono' softplus_continuous.aestronglyMeasurable ?_
    exact Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (softplus_nonneg u)]
      exact softplus_le_exp u)
  have hd (u : ℝ) : HasDerivAt softplus (-(exp u + 1)⁻¹) u := by
    have h := (((hasDerivAt_neg u).exp).const_add 1).log (by positivity)
    convert h using 1
    · rfl
    · rw [exp_neg]
      field_simp [(exp_pos u).ne', show exp u + 1 ≠ 0 by positivity]
  have hb0 : Tendsto (softplus * id) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Continuous (softplus * id) := softplus_continuous.mul continuous_id
    have ht := (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Pi.mul_apply, id_eq, mul_zero] using ht
  have hbTop : Tendsto (softplus * id) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun u => exp (-u) * u) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      exact mul_nonneg (softplus_nonneg u) hu
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      exact mul_le_mul_of_nonneg_right (softplus_le_exp u) hu
    · have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
      simpa only [rpow_one, neg_mul, one_mul, mul_neg, mul_one, mul_comm] using h
  have hi' : IntegrableOn (fun u => -(exp u + 1)⁻¹ * id u) (Ioi 0) := by
    convert hf.neg using 1
    funext u
    simp only [id_eq, f, Pi.neg_apply]
    ring
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := softplus) (v := id) (u' := fun u => -(exp u + 1)⁻¹) (v' := fun _ => 1)
    (fun u _ => hd u) (fun u _ => hasDerivAt_id u)
    (by
      have he : softplus * (fun _ : ℝ => (1 : ℝ)) = softplus := by
        funext u
        exact mul_one _
      rwa [he]) hi' hb0 hbTop
  simp only [mul_one, sub_zero, zero_sub, id_eq] at h
  rw [h, ← integral_neg]
  convert hmass using 2
  funext u
  dsimp [f]
  ring

private theorem softplus_continuum_tendsto {s : ℝ → ℝ} (hs : Tendsto s atTop atTop) :
    Tendsto (fun P : ℝ => (s P / P) *
      (∫ t in P / 2..2 * P, weight P (s P) t)) atTop (𝓝 (π ^ 2 / 6)) := by
  let g : ℝ → ℝ := fun u => softplus |u|
  have hg : Continuous g := softplus_continuous.comp continuous_abs
  let F : ℝ → ℝ → ℝ := fun P =>
    (Ioc (-s P * log 2) (s P * log 2)).indicator (fun u => g u * exp (u / s P))
  have hpos : ∀ᶠ P in atTop, 0 < s P := hs.eventually_gt_atTop 0
  have hmeas : ∀ᶠ P in atTop, AEStronglyMeasurable (F P) volume :=
    Eventually.of_forall fun P => by
      dsimp only [F]
      have h : Continuous (fun u : ℝ => g u * exp (u / s P)) :=
        hg.mul (continuous_exp.comp (continuous_id.div_const (s P)))
      exact h.aestronglyMeasurable.indicator measurableSet_Ioc
  have hmajor : Integrable (fun u : ℝ => 2 * exp (-|u|)) := by
    have hOn : IntegrableOn (fun u : ℝ => exp (-|u|)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).congr_fun (fun u hu => by
        rw [abs_of_nonneg (le_of_lt (mem_Ioi.mp hu))]) measurableSet_Ioi
    have hNeg : IntegrableOn (fun u : ℝ => exp (-|u|)) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun u : ℝ => -u :=
        (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hOn
    have h := hNeg.union hOn
    rw [Iic_union_Ioi, integrableOn_univ] at h
    exact h.const_mul 2
  have hbound : ∀ᶠ P in atTop, ∀ᵐ u ∂volume, ‖F P u‖ ≤ 2 * exp (-|u|) := by
    filter_upwards [hpos] with P hp
    apply Eventually.of_forall
    intro u
    dsimp only [F]
    by_cases hu : u ∈ Ioc (-s P * log 2) (s P * log 2)
    · rw [indicator_of_mem hu, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (softplus_nonneg _) (exp_pos _).le)]
      have he : exp (u / s P) ≤ 2 := by
        rw [← exp_log (show (0 : ℝ) < 2 by norm_num)]
        exact exp_le_exp.mpr ((div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hu.2))
      exact (mul_le_mul (softplus_le_exp _) he (exp_pos _).le (exp_pos _).le).trans_eq
        (mul_comm _ _)
    · rw [indicator_of_notMem hu, norm_zero]
      positivity
  have hpoint : ∀ᵐ u ∂volume, Tendsto (fun P => F P u) atTop (𝓝 (g u)) := by
    apply Eventually.of_forall
    intro u
    have hcut : Tendsto (fun P => s P * log 2) atTop atTop :=
      hs.atTop_mul_const (log_pos (by norm_num))
    have hsmall := hs.const_div_atTop u
    have he := (continuous_exp.continuousAt (x := (0 : ℝ))).tendsto.comp hsmall
    have h := he.const_mul (g u)
    change Tendsto (fun P : ℝ => g u * exp (u / s P)) atTop (𝓝 (g u * exp 0)) at h
    rw [exp_zero, mul_one] at h
    apply h.congr'
    filter_upwards [hcut.eventually_gt_atTop (|u|)] with P hP
    have hu : u ∈ Ioc (-s P * log 2) (s P * log 2) := by
      have hlow := neg_abs_le u
      have hhi := le_abs_self u
      exact ⟨by linarith, by linarith⟩
    exact (indicator_of_mem hu (fun v : ℝ => g v * exp (v / s P))).symm
  have hm := tendsto_integral_filter_of_dominated_convergence _ hmeas hbound hmajor hpoint
  have hmass : (∫ u, g u) = π ^ 2 / 6 := by
    dsimp [g]
    rw [integral_comp_abs, fermi_mass]
    ring
  rw [hmass] at hm
  apply hm.congr'
  filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with P hp hP
  let x : ℝ → ℝ := fun u => P * exp (u / s P)
  have hx (u : ℝ) : HasDerivAt x (P * exp (u / s P) / s P) u := by
    convert (((hasDerivAt_id u).div_const (s P)).exp).const_mul P using 1
    · rfl
    · simp only [id_eq]
      ring
  have hx' : Continuous (fun u : ℝ => P * exp (u / s P) / s P) :=
    (continuous_const.mul (continuous_exp.comp (continuous_id.div_const _))).div_const _
  have hcw : ContinuousOn (weight P (s P)) (Ioi 0) := by
    have hl : ContinuousOn (fun t : ℝ => log (t / P)) (Ioi 0) :=
      (continuous_id.continuousOn.div_const P).log
        (fun t ht => div_ne_zero (mem_Ioi.mp ht).ne' hP.ne')
    have he : ContinuousOn (fun t : ℝ => exp (-s P * |log (t / P)|)) (Ioi 0) :=
      continuous_exp.comp_continuousOn (continuousOn_const.mul hl.abs)
    unfold weight
    exact (continuousOn_const.add he).log
      (fun _ _ => (add_pos_of_pos_of_nonneg zero_lt_one (exp_pos _).le).ne')
  have hh := intervalIntegral.integral_comp_mul_deriv'
    (a := -s P * log 2) (b := s P * log 2)
    (f := x) (f' := fun u => P * exp (u / s P) / s P) (g := weight P (s P))
    (fun u _ => hx u) hx'.continuousOn
    (hcw.mono (by rintro _ ⟨u, _, rfl⟩; exact mul_pos hP (exp_pos _)))
  have hleft : x (-s P * log 2) = P / 2 := by
    dsimp [x]
    rw [show -s P * log 2 / s P = -log 2 by field_simp]
    rw [exp_neg, exp_log (by norm_num)]
    ring
  have hright : x (s P * log 2) = 2 * P := by
    dsimp [x]
    rw [show s P * log 2 / s P = log 2 by field_simp, exp_log (by norm_num), mul_comm]
  rw [hleft, hright] at hh
  have hw (u : ℝ) : weight P (s P) (x u) = g u := by
    unfold weight x g softplus
    rw [show P * exp (u / s P) / P = exp (u / s P) by field_simp, log_exp,
      abs_div, abs_of_pos hp]
    congr 2
    field_simp
  simp only [Function.comp_apply, hw] at hh
  have hrewrite (u : ℝ) :
      g u * (P * exp (u / s P) / s P) = (P / s P) * (g u * exp (u / s P)) := by ring
  simp_rw [hrewrite, intervalIntegral.integral_const_mul] at hh
  dsimp only [F]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le
    (show -s P * log 2 ≤ s P * log 2 by nlinarith [log_pos (show (1 : ℝ) < 2 by norm_num)]),
    ← hh]
  field_simp

private def primeWeight (P s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then weight P s n else 0

private theorem primeWeight_nonneg (P s : ℝ) (n : ℕ) : 0 ≤ primeWeight P s n := by
  unfold primeWeight
  split_ifs
  · simpa only [softplus, weight, neg_mul] using softplus_nonneg (s * |log ((n : ℝ) / P)|)
  · exact le_rfl

private theorem softplus_prime_tails {P s : ℝ} (hP : 2 ≤ P) (hs : 2 ≤ s) :
    Summable (primeWeight P s) ∧
      0 ≤ (∑' n, primeWeight P s n) - ∑ p ∈ primeInterval (P / 2) (2 * P), weight P s p ∧
      (∑' n, primeWeight P s n) - ∑ p ∈ primeInterval (P / 2) (2 * P), weight P s p ≤
        5 * P * exp (-s * log 2) := by
  let N := ⌊2 * P⌋₊
  let M := ⌊P / 2⌋₊
  let b := exp (-s * log 2)
  let g : ℝ → ℝ := fun t => t ^ (-2 : ℝ)
  have hp : 0 < P := by linarith
  have hN : P ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * P)
    push_cast at h
    dsimp only [N]
    linarith
  have hNp := hp.trans_le hN
  have hMN : M + 1 ≤ N + 1 := by
    exact Nat.succ_le_succ (Nat.floor_le_floor (by linarith))
  have hupper (n : ℕ) (hn : N < n) :
      primeWeight P s n ≤ (4 * P ^ 2 * b) * g n := by
    unfold primeWeight
    split_ifs with hnprime
    · have ht : 2 * P < (n : ℝ) := (Nat.floor_lt (by positivity)).mp hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hr : 2 ≤ (n : ℝ) / P := (le_div_iff₀ hp).mpr (by linarith)
      have hl := log_le_log (by norm_num : (0 : ℝ) < 2) hr
      have hlog : 0 ≤ log ((n : ℝ) / P) := (log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hl
      unfold weight
      rw [abs_of_nonneg hlog]
      have hw := softplus_le_exp (s * log ((n : ℝ) / P))
      simp only [softplus, ← neg_mul] at hw
      refine hw.trans ?_
      have splitExp : -s * log ((n : ℝ) / P) =
          -2 * log ((n : ℝ) / P) + (-(s - 2)) * log ((n : ℝ) / P) := by ring
      rw [splitExp, exp_add]
      have hexp : exp (-(s - 2) * log ((n : ℝ) / P)) ≤ exp (-(s - 2) * log 2) :=
        exp_le_exp.mpr (mul_le_mul_of_nonpos_left hl (by linarith))
      refine (mul_le_mul_of_nonneg_left hexp (exp_pos _).le).trans_eq ?_
      rw [show -(s - 2) * log 2 = -s * log 2 + 2 * log 2 by ring, exp_add]
      have hratioExp : exp ((-2 : ℝ) * log ((n : ℝ) / P)) = (((n : ℝ) / P) ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) * log ((n : ℝ) / P) = -(log ((n : ℝ) / P) * 2) by ring,
          exp_neg, exp_mul, exp_log (div_pos hn0 hp), rpow_two]
      have htwo : exp (2 * log 2) = 4 := by
        rw [mul_comm, exp_mul, exp_log (by norm_num : (0 : ℝ) < 2), rpow_two]
        norm_num
      rw [hratioExp, htwo]
      dsimp only [g, b]
      rw [rpow_neg hn0.le, rpow_two]
      field_simp
      <;> ring
    · exact mul_nonneg (by dsimp [b]; positivity) (rpow_nonneg (Nat.cast_nonneg _) _)
  have hbase : Summable (fun n : ℕ => (4 * P ^ 2 * b) * g n) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left _
  have hbaseShift := (summable_nat_add_iff (N + 1)).mpr hbase
  have hprimeShift : Summable (fun n : ℕ => primeWeight P s (n + (N + 1))) :=
    hbaseShift.of_nonneg_of_le (fun n => primeWeight_nonneg P s _)
      (fun n => hupper _ (by omega))
  have hprime := (summable_nat_add_iff (N + 1)).mp hprimeShift
  have hright : (∑' n : ℕ, primeWeight P s (n + (N + 1))) ≤ 4 * P * b := by
    have ha : AntitoneOn g (Ici (N : ℝ)) := by
      intro x hx y _ hxy
      exact rpow_le_rpow_of_nonpos (hNp.trans_le hx) hxy (by norm_num)
    have hi : IntegrableOn g (Ioi (N : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hNp
    have htest := ha.tsum_comp_add_le_integral N hi
      (fun t ht => rpow_nonneg (hNp.trans (mem_Ioi.mp ht)).le _)
    have hval : (∫ t in Ioi (N : ℝ), g t) = (N : ℝ)⁻¹ := by
      dsimp only [g]
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hNp]
      norm_num [rpow_neg_one]
    rw [hval] at htest
    calc
      _ ≤ ∑' n : ℕ, (4 * P ^ 2 * b) * g (n + (N + 1) : ℕ) :=
        hprimeShift.tsum_le_tsum (fun n => hupper _ (by omega)) hbaseShift
      _ = (4 * P ^ 2 * b) * ∑' n : ℕ, g (n + N + 1 : ℕ) := by
        rw [← tsum_mul_left]
        simp only [Nat.add_assoc]
      _ ≤ (4 * P ^ 2 * b) * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left htest (by dsimp [b]; positivity)
      _ ≤ 4 * P * b := by
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ hNp).mpr
        nlinarith [mul_nonneg (show 0 ≤ 4 * P * b by dsimp [b]; positivity)
          (sub_nonneg.mpr hN)]
  have hleft (n : ℕ) (hn : n ∈ Finset.range (M + 1)) : primeWeight P s n ≤ b := by
    unfold primeWeight
    split_ifs with hnprime
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hnprime.pos
      have ht : (n : ℝ) ≤ P / 2 := (Nat.le_floor_iff (by positivity)).mp
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
      have hlog : log ((n : ℝ) / P) ≤ -log 2 := by
        rw [← log_inv]
        exact log_le_log (div_pos hn0 hp) ((div_le_iff₀ hp).mpr (by linarith))
      have hlog0 := log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      have hw := softplus_le_exp (s * |log ((n : ℝ) / P)|)
      simp only [softplus, ← neg_mul] at hw
      refine hw.trans ?_
      dsimp only [b]
      rw [abs_of_nonpos (by linarith : log ((n : ℝ) / P) ≤ 0)]
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by linarith) (by linarith))
    · exact (exp_pos _).le
  have hsmall : ∑ n ∈ Finset.range (M + 1), primeWeight P s n ≤ P * b := by
    calc
      _ ≤ ∑ _ ∈ Finset.range (M + 1), b := Finset.sum_le_sum hleft
      _ = ((M : ℝ) + 1) * b := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        have h := Nat.floor_le (show 0 ≤ P / 2 by positivity)
        dsimp [M]
        linarith) (exp_pos _).le
  have hsplit : (∑ n ∈ Finset.range (M + 1), primeWeight P s n) +
      (∑ p ∈ primeInterval (P / 2) (2 * P), weight P s p) =
        ∑ n ∈ Finset.range (N + 1), primeWeight P s n := by
    have he : Finset.Ico (M + 1) (N + 1) = Finset.Ioc M N := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [← Finset.sum_range_add_sum_Ico (primeWeight P s) hMN, he]
    simp only [primeInterval, Finset.sum_filter, primeWeight, M, N]
  have ht := hprime.sum_add_tsum_nat_add (N + 1)
  rw [← hsplit] at ht
  refine ⟨hprime, ?_, ?_⟩
  · have hnonneg : 0 ≤ ∑ n ∈ Finset.range (M + 1), primeWeight P s n :=
      Finset.sum_nonneg (fun n _ => primeWeight_nonneg P s n)
    linarith only [ht, hnonneg,
      tsum_nonneg (fun n : ℕ => primeWeight_nonneg P s (n + (N + 1)))]
  · linarith only [ht, hsmall, hright]

private theorem remove_prime_logs {s : ℝ → ℝ}
    (hs : ∀ᶠ P in atTop, 0 ≤ s P)
    (hweighted : Tendsto (fun P : ℝ => (s P / P) *
      ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p * log p)
      atTop (𝓝 (π ^ 2 / 6))) :
    Tendsto (fun P : ℝ => (s P * log P / P) *
      ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p)
      atTop (𝓝 (π ^ 2 / 6)) := by
  let A : ℝ → ℝ := fun P => (s P / P) *
    ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p * log p
  let B : ℝ → ℝ := fun P => (s P * log P / P) *
    ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p
  have h := (tendsto_log_atTop.const_div_atTop (2 * log 2)).mul hweighted
  simp only [zero_mul] at h
  have herr : Tendsto (fun P => B P - A P) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    refine squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ h
    filter_upwards [eventually_ge_atTop (4 : ℝ), hs] with P hP hsP
    let S := primeInterval (P / 2) (2 * P)
    let w : ℕ → ℝ := fun p => weight P (s P) p
    have hP0 : 0 < P := by linarith
    have hlog : 0 < log P := log_pos (by linarith)
    have hcoef := div_nonneg hsP hP0.le
    have hdiff : B P - A P = (s P / P) * ∑ p ∈ S, w p * (log P - log p) := by
      dsimp only [A, B, S, w]
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    change |B P - A P| ≤ (2 * log 2 / log P) * A P
    rw [hdiff, abs_mul, abs_of_nonneg hcoef]
    have hpbound (p : ℕ) (hp : p ∈ S) : |log P - log p| ≤ (2 * log 2 / log P) * log p := by
      simp only [S, primeInterval, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hlow := (Nat.floor_lt (by positivity : 0 ≤ P / 2)).mp hp.1.1
      have hhi := (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).mp hp.1.2
      have hpos : 0 < (p : ℝ) := by linarith
      have hall := log_window_lower hP hlow.le
      have hlow' := log_le_log (show 0 < P / 2 by positivity) hlow.le
      have hhi' := log_le_log hpos hhi
      rw [log_div hP0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlow'
      rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne'] at hhi'
      refine (abs_le.mpr ⟨by linarith, by linarith⟩ : |log P - log p| ≤ log 2).trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
      nlinarith [mul_nonneg (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
        (sub_nonneg.mpr hall)]
    calc
      _ ≤ (s P / P) * ∑ p ∈ S, |w p * (log P - log p)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hcoef
      _ ≤ (s P / P) * ∑ p ∈ S, w p * ((2 * log 2 / log P) * log p) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        apply Finset.sum_le_sum
        intro p hp
        have hw : 0 ≤ w p := (weight_bounds P p hsP).1
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left (hpbound p hp) hw
      _ = _ := by
        dsimp only [A, S, w]
        simp_rw [show ∀ p : ℕ, weight P (s P) p * (2 * log 2 / log P * log p) =
          (2 * log 2 / log P) * (weight P (s P) p * log p) from fun _ => by ring,
          ← Finset.mul_sum]
        ring
  have hB := herr.add hweighted
  simp only [zero_add] at hB
  exact hB.congr (fun P => by change B P - A P + A P = B P; ring)

/-- The actual prime sum for a moving softplus is eventually absolutely
summable and has normalized limit `π^2 / 6` for every positive log power. -/
theorem prime_softplus_asymptotic {a C₁ C₂ : ℝ} (ha : 0 < a) (hC₁ : 0 < C₁)
    (hC : C₁ ≤ C₂) (s : ℝ → ℝ)
    (hs : ∀ᶠ P in atTop, C₁ * log P ^ a ≤ s P ∧ s P ≤ C₂ * log P ^ a) :
    (∀ᶠ P in atTop,
      Summable (fun p : ℕ => |if p.Prime then weight P (s P) p else 0|)) ∧
    Tendsto (fun P : ℝ =>
      (∑' p : ℕ, if p.Prime then weight P (s P) p else 0) /
        (P / (s P * log P))) atTop (𝓝 (π ^ 2 / 6)) := by
  have hC₂ := hC₁.trans_le hC
  have hlogpow : Tendsto (fun P : ℝ => log P ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_log_atTop
  have hsTop : Tendsto s atTop atTop :=
    tendsto_atTop_mono' _ (hs.mono fun _ h => h.1)
      ((tendsto_const_mul_atTop_of_pos hC₁).mpr hlogpow)
  have hn : ∀ᶠ P in atTop, 0 ≤ s P := (hsTop.eventually_ge_atTop 0)
  have hθ := theta_comparison_tendsto (hn.and (hs.mono fun _ h => h.2)) hC₂
  have hc := softplus_continuum_tendsto hsTop
  have hw := hθ.add hc
  rw [zero_add] at hw
  have hw' : Tendsto (fun P : ℝ => (s P / P) *
      ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p * log p)
      atTop (𝓝 (π ^ 2 / 6)) :=
    hw.congr (fun P => by ring)
  have hcenter := remove_prime_logs hn hw'
  have hfar : ∀ᶠ P : ℝ in atTop, Summable (primeWeight P (s P)) ∧
      0 ≤ (∑' n, primeWeight P (s P) n) -
        ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p ∧
      (∑' n, primeWeight P (s P) n) -
        ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p ≤
        5 * P * exp (-s P * log 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hsTop.eventually_ge_atTop 2] with P hP hsP
    exact softplus_prime_tails hP hsP
  constructor
  · filter_upwards [hfar] with P hP
    change Summable (fun p => |primeWeight P (s P) p|)
    simpa only [abs_of_nonneg (primeWeight_nonneg _ _ _)] using hP.1
  let K : ℝ := 5 * C₂
  let b : ℝ := C₁ * log 2
  have hb : 0 < b := mul_pos hC₁ (log_pos (by norm_num))
  have hdecay : Tendsto (fun P : ℝ =>
      K * (log P ^ (a + 1) * exp (-b * log P ^ a))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((a + 1) / a) b hb).comp
      hlogpow).const_mul K
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    simp only [Function.comp_apply]
    rw [← rpow_mul (log_pos hP).le, show a * ((a + 1) / a) = a + 1 by field_simp]
  have herr : Tendsto (fun P : ℝ => s P * log P / P *
      ((∑' n, primeWeight P (s P) n) -
        ∑ p ∈ primeInterval (P / 2) (2 * P), weight P (s P) p)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hdecay
    · filter_upwards [hfar, eventually_gt_atTop (1 : ℝ), hn] with P htail hP hsP
      exact mul_nonneg (by have := log_pos hP; positivity) htail.2.1
    · filter_upwards [hfar, hs, eventually_gt_atTop (1 : ℝ), hn] with P htail hscale hP hsP
      have hp : 0 < P := by linarith
      have hl : 0 < log P := log_pos hP
      have hexp : exp (-s P * log 2) ≤ exp (-b * log P ^ a) := by
        apply exp_le_exp.mpr
        dsimp [b]
        nlinarith [mul_nonneg (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
          (sub_nonneg.mpr hscale.1)]
      calc
        _ ≤ (s P * log P / P) * (5 * P * exp (-s P * log 2)) :=
          mul_le_mul_of_nonneg_left htail.2.2 (by positivity)
        _ = 5 * s P * log P * exp (-s P * log 2) := by field_simp
        _ ≤ (5 * (C₂ * log P ^ a) * log P) * exp (-b * log P ^ a) := by
          apply mul_le_mul _ hexp (exp_pos _).le (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hscale.2 (by norm_num)) hl.le
        _ = _ := by rw [rpow_add hl, rpow_one]; unfold K; ring
  have hfull := herr.add hcenter
  rw [zero_add] at hfull
  exact hfull.congr fun P => by
    simp only [primeWeight, div_div_eq_mul_div]
    ring

end D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus

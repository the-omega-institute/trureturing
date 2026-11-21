/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH the weighted prime-only window mass has a logarithmic main term. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHActualHSqrtBound
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import D5.S3.Weil.Mertens.Cryptids.Schoenfeld

/-! Prime powers supply the logarithmic main term of the weighted window mass.
At the critical line, nonzero ordinates give a bounded primitive of the zero series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (complete_chebyshev_tail_identity)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
open D5.S3.Arith.Robin.CompleteMertensPeak (U Q)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

private def normalizedZeroSeries (y : ℝ) : ℂ :=
  (Real.exp (-y / 2) : ℂ) * actualH y

private def frequency (k : ℕ) : ℂ := actualZero k - 1 / 2

private lemma frequency_real (hRH : RiemannHypothesis) (k : ℕ) :
    (frequency k).re = 0 := by
  have hline : (actualZero k).re = 1 / 2 := by
    simpa only [actualZero, D5.S3.Weil.Convention.criticalAbscissa] using
      zeroData_zero_on_critical_line_of_rh hRH actualData (actualOccurrenceEquiv k).1
  simp [frequency, Complex.sub_re, hline]

private lemma frequency_norm (k : ℕ) : 10 < ‖frequency k‖ := by
  have hz : IsNontrivialZero (actualZero k) :=
    actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
  have h := actual_height_gt_ten _ hz
  exact h.trans_le (by simpa [frequency, Complex.sub_im, Complex.div_im] using
    Complex.abs_im_le_norm (frequency k))

private lemma exp_mode_norm (hRH : RiemannHypothesis) (k : ℕ) (y : ℝ) :
    ‖Complex.exp (frequency k * y)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, frequency_real hRH k]

private lemma normalized_hasSum (y : ℝ) :
    HasSum (fun k : ℕ => actualCoeff k * Complex.exp (frequency k * y))
      (normalizedZeroSeries y) := by
  convert (actualH_summable y).hasSum.mul_left (Real.exp (-y / 2) : ℂ) using 1 <;> try rfl
  funext k
  rw [show (y : ℂ) * actualZero k = actualZero k * (y : ℂ) by ring,
    ← mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  congr 2
  unfold frequency
  ring

private lemma zero_series_window_bound (hRH : RiemannHypothesis) (a b : ℝ) :
    ‖∫ y in a..b, normalizedZeroSeries y‖ ≤ (∑' k : ℕ, ‖actualCoeff k‖) / 5 := by
  let term := fun k : ℕ => fun y : ℝ => actualCoeff k * Complex.exp (frequency k * y)
  have hs := actualCoeff_hasSum.summable.norm
  have hi : HasSum (fun k : ℕ => ∫ y in a..b, term k y)
      (∫ y in a..b, normalizedZeroSeries y) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k (_ : ℝ) => ‖actualCoeff k‖)
    · intro k
      exact (show Continuous (term k) by dsimp [term]; fun_prop).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun y => by simp [term, exp_mode_norm hRH]
    · exact ae_of_all _ fun _ _ => hs
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun y _ => normalized_hasSum y
  rw [← hi.tsum_eq, div_eq_mul_inv]
  apply tsum_of_norm_bounded (hs.hasSum.mul_right ((5 : ℝ)⁻¹))
  intro k
  have hn := frequency_norm k
  have hf : frequency k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [show (∫ y in a..b, term k y) = actualCoeff k *
      ((Complex.exp (frequency k * b) - Complex.exp (frequency k * a)) / frequency k) by
        rw [show term k = fun y : ℝ => actualCoeff k * Complex.exp (frequency k * y) from rfl,
          intervalIntegral.integral_const_mul, integral_exp_mul_complex hf],
    norm_mul, norm_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc
    _ ≤ (1 + 1) / ‖frequency k‖ := by
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      simpa only [exp_mode_norm hRH] using
        norm_sub_le (Complex.exp (frequency k * b)) (Complex.exp (frequency k * a))
    _ ≤ (5 : ℝ)⁻¹ := by rw [div_le_iff₀ (by linarith)]; nlinarith

private lemma prime_power_bias_error (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x| ≤
      (2 * (Real.log 4 + 4) + 1) * x ^ (5 / 12 : ℝ) := by
  let C := Real.log 4 + 4
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (s := (1 / 6 : ℝ)) (by norm_num)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (5000 : ℝ), hlog] with x hx hsx hlogx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have habs : |Chebyshev.psi (Real.sqrt x) - Real.sqrt x| ≤ x ^ (5 / 12 : ℝ) := by
    have hs :=
      ConjectureMachines.Semantics.Riemann.abs_psi_sub_self_le_seven_eighths_of_five_thousand_le
        hRH hsx
    change |Chebyshev.psi (Real.sqrt x) - Real.sqrt x| ≤
      (7 / 8 : ℝ) * Real.sqrt (Real.sqrt x) * (Real.log (Real.sqrt x)) ^ 2 at hs
    have hquarter : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      norm_num
    have hlog' : (Real.log x)^2 ≤ x ^ (1 / 6 : ℝ) := by
      simpa [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg, Real.log_nonneg hx,
        Real.rpow_nonneg hx0.le] using hlogx
    rw [hquarter, Real.log_sqrt hx0.le] at hs
    calc
      _ ≤ _ := hs
      _ ≤ x ^ (1 / 4 : ℝ) * (Real.log x)^2 := by
        nlinarith [Real.rpow_nonneg hx0.le (1 / 4 : ℝ), sq_nonneg (Real.log x)]
      _ ≤ x ^ (1 / 4 : ℝ) * x ^ (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog' (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have hu : Chebyshev.psi x - Chebyshev.theta x ≤
      Chebyshev.psi (Real.sqrt x) + Chebyshev.psi (x ^ (1 / 3 : ℝ)) +
        Chebyshev.psi (x ^ (1 / 5 : ℝ)) := by
    simpa only [Real.sqrt_eq_rpow, one_div] using
      Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hl : Chebyshev.psi (Real.sqrt x) ≤ Chebyshev.psi x - Chebyshev.theta x := by
    have h : Chebyshev.psi (Real.sqrt x) + Chebyshev.psi (x ^ (1 / 3 : ℝ)) +
        Chebyshev.psi (x ^ (1 / 7 : ℝ)) ≤ Chebyshev.psi x - Chebyshev.theta x := by
      simpa only [Real.sqrt_eq_rpow, one_div] using
        Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx0.le
    linarith [Chebyshev.psi_nonneg (x ^ (1 / 3 : ℝ)),
      Chebyshev.psi_nonneg (x ^ (1 / 7 : ℝ))]
  have hpower (r : ℝ) (hr : r ≤ 5 / 12) :
      Chebyshev.psi (x ^ r) ≤ C * x ^ (5 / 12 : ℝ) :=
    (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le r)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hr) hC.le)
  apply abs_le.mpr
  constructor
  · have hnonneg := mul_nonneg hC.le (Real.rpow_nonneg hx0.le (5 / 12 : ℝ))
    linarith [neg_abs_le (Chebyshev.psi (Real.sqrt x) - Real.sqrt x)]
  · linarith [le_abs_self (Chebyshev.psi (Real.sqrt x) - Real.sqrt x),
      hpower (1 / 3) (by norm_num), hpower (1 / 5) (by norm_num)]

private def bias (x : ℝ) : ℝ := Real.sqrt x * (Q x - primeTail x)

private lemma bias_decay (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, |bias x - 2| ≤
      ((2 * (Real.log 4 + 4) + 1) * (12 / 7)) * x ^ (-(1 / 12) : ℝ) := by
  let C := 2 * (Real.log 4 + 4) + 1
  obtain ⟨T, hT⟩ := eventually_atTop.mp (prime_power_bias_error hRH)
  filter_upwards [eventually_ge_atTop (max T 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right T 1).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hsx := Real.sqrt_pos.mpr hx0
  let F := fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t) / t ^ 2
  have hcent : Q x - primeTail x - 2 / Real.sqrt x = ∫ t in Ioi x, F t := by
    rw [tail_eq hx1, ← root_integral hx0,
      ← integral_sub (diff_integrable.mono_set (Ioi_subset_Ioi hx1)) (root_integrable hx0)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 - Real.sqrt t / t ^ 2 =
      (Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t) / t ^ 2
    ring
  have hb : |∫ t in Ioi x, F t| ≤ C * (x ^ (-(7 / 12) : ℝ) * (12 / 7)) := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ∫ t in Ioi x, C * t ^ (-(19 / 12) : ℝ) := by
        apply norm_integral_le_of_norm_le
          ((integrableOn_Ioi_rpow_of_lt (a := (-(19 / 12) : ℝ)) (by norm_num) hx0).const_mul C)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := hx0.trans ht
        have hpower := hT t ((le_max_left T 1).trans (hx.trans ht.le))
        calc
          ‖F t‖ = |Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t| / t ^ 2 := by
            simp only [F, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
          _ ≤ C * t ^ (5 / 12 : ℝ) / t ^ 2 :=
            div_le_div_of_nonneg_right hpower (sq_nonneg _)
          _ = _ := by
            rw [mul_div_assoc, ← Real.rpow_two, ← Real.rpow_sub ht0]
            norm_num
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx0]
        norm_num [div_eq_mul_inv]
  have hidentity : bias x - 2 =
      Real.sqrt x * (Q x - primeTail x - 2 / Real.sqrt x) := by
    dsimp [bias]
    field_simp
  rw [hidentity, hcent, abs_mul, abs_of_nonneg hsx.le]
  calc
    _ ≤ Real.sqrt x * (C * (x ^ (-(7 / 12) : ℝ) * (12 / 7))) :=
      mul_le_mul_of_nonneg_left hb hsx.le
    _ = _ := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ = (C * (12 / 7)) * (x ^ (1 / 2 : ℝ) * x ^ (-(7 / 12) : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hx0]; norm_num [C]

private def normalizedMass (y : ℝ) : ℝ :=
  max (Real.sqrt (Real.exp y) * (-primeTail (Real.exp y))) 0

private def windowError (y : ℝ) : ℝ :=
  normalizedMass y - (2 + (normalizedZeroSeries y).re)

private lemma normalizedZeroSeries_continuous : Continuous normalizedZeroSeries :=
  (Complex.continuous_ofReal.comp (by fun_prop : Continuous (fun y : ℝ => Real.exp (-y / 2)))).mul
    actualH_continuous

private lemma sqrt_exp_eq (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

private lemma normalizedZeroSeries_bound (hRH : RiemannHypothesis) (y : ℝ) :
    ‖normalizedZeroSeries y‖ ≤ 2 := by
  rw [normalizedZeroSeries, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hbound := actualH_sqrt_bound_of_rh_registered.2 hRH y
  calc
    _ ≤ Real.exp (-y / 2) * ((101 / 100 : ℝ) * firstLiMass * Real.exp (y / 2)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (101 / 100 : ℝ) * firstLiMass := by
      rw [mul_left_comm, ← Real.exp_add]
      rw [show -y / 2 + y / 2 = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ _ := by linarith [firstLiMass_lt_one]

private lemma normalizedMass_eq (y : ℝ) (hy : Real.log 2 ≤ y) :
    normalizedMass y =
      max (bias (Real.exp y) + (normalizedZeroSeries y).re +
        Real.exp (-y / 2) * (Real.log (2 * Real.pi) - trivialT y)) 0 := by
  have hx : 2 ≤ Real.exp y := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hy
  have hy0 : 0 < y := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hy
  have hQ := complete_chebyshev_tail_identity chebyshev_error_kernel_integrable hx
  change Q (Real.exp y) = _ at hQ
  have hU : U (Real.exp y) = -Q (Real.exp y) * Real.exp y := by
    rw [hQ, U]
    field_simp [(Real.exp_pos y).ne']
    ring
  have hmain : Real.exp (-y / 2) * U (Real.exp y) =
      (normalizedZeroSeries y).re + Real.exp (-y / 2) * (Real.log (2 * Real.pi) - trivialT y) := by
    simp only [normalizedZeroSeries, actual_integrated_explicit_formula hy0, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have hdamp : Real.exp (-y / 2) * Real.exp y = Real.sqrt (Real.exp y) := by
    rw [← Real.exp_add, sqrt_exp_eq]
    congr 1
    ring
  unfold normalizedMass bias
  congr 1
  rw [add_assoc, ← hmain, hU, mul_comm (-Q (Real.exp y)), ← mul_assoc, hdamp]
  ring

private lemma windowError_continuous : ContinuousOn windowError (Ici (Real.log 2)) := by
  have hp : ContinuousOn primeTail (Ici 1) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi
  have hcomp : ContinuousOn (fun y => primeTail (Real.exp y)) (Ici (Real.log 2)) :=
    hp.comp Real.continuous_exp.continuousOn (fun y hy => by
      have h : 2 ≤ Real.exp y := by
        simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hy
      exact (by norm_num : (1 : ℝ) ≤ 2).trans h)
  apply (((Real.continuous_sqrt.comp Real.continuous_exp).continuousOn.mul hcomp.neg).sup
    continuousOn_const).sub
  exact ((Complex.continuous_re.comp normalizedZeroSeries_continuous).const_add 2).continuousOn

private lemma windowError_integrable (hRH : RiemannHypothesis) :
    IntegrableOn windowError (Ioi (Real.log 2)) := by
  let C := (2 * (Real.log 4 + 4) + 1) * (12 / 7)
  let D := |Real.log (2 * Real.pi)| + (1 - Real.log 2)
  obtain ⟨S, hS⟩ := eventually_atTop.mp (Real.tendsto_exp_atTop.eventually (bias_decay hRH))
  let T := max S (Real.log 2)
  have hlog : Real.log 2 ≤ T := le_max_right _ _
  have hiTail : IntegrableOn windowError (Ioi T) := by
    have hi := ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 12 : ℝ) < 0) T).const_mul C).add
      ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) T).const_mul D)
    have hc : ContinuousOn windowError (Ioi T) :=
      windowError_continuous.mono (fun _ hy => hlog.trans (mem_Ioi.mp hy).le)
    refine hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyT : T < y := hy
    have hylog := hlog.trans hyT.le
    have hy0 : 0 ≤ y := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hylog
    have hpos : 0 ≤ 2 + (normalizedZeroSeries y).re := by
      linarith [Complex.abs_re_le_norm (normalizedZeroSeries y),
        neg_abs_le (normalizedZeroSeries y).re, normalizedZeroSeries_bound hRH y]
    change ‖windowError y‖ ≤ C * Real.exp (-(1 / 12 : ℝ) * y) +
      D * Real.exp (-(1 / 2 : ℝ) * y)
    rw [Real.norm_eq_abs, windowError, normalizedMass_eq y hylog, ← max_eq_left hpos]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have heq : bias (Real.exp y) + (normalizedZeroSeries y).re +
        Real.exp (-y / 2) * (Real.log (2 * Real.pi) - trivialT y) -
        (2 + (normalizedZeroSeries y).re) =
        (bias (Real.exp y) - 2) +
          Real.exp (-y / 2) * (Real.log (2 * Real.pi) - trivialT y) := by ring
    rw [heq]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · have hb := hS y ((le_max_left _ _).trans hyT.le)
      change |bias (Real.exp y) - 2| ≤ C * Real.exp y ^ (-(1 / 12) : ℝ) at hb
      rw [← Real.exp_mul, mul_comm y] at hb
      exact hb
    · have hr : |Real.log (2 * Real.pi) - trivialT y| ≤ D := by
        apply (abs_sub _ _).trans
        rw [abs_of_nonneg (trivialT_nonneg hy0)]
        exact add_le_add_right (trivialT_le_mass hy0) _
      rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm D,
         show -(1 / 2 : ℝ) * y = -y / 2 by ring]
      exact mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
  have hhead : IntegrableOn windowError (Ioc (Real.log 2) T) :=
    ((windowError_continuous.mono (fun _ hy => hy.1)).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [← Ioc_union_Ioi_eq_Ioi hlog]
  exact hhead.union hiTail

private lemma mass_log_substitution {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, max (-primeTail x) 0 / Real.sqrt x) =
      ∫ y in Real.log a..Real.log b, normalizedMass y := by
  have ha0 : 0 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hlog := Real.log_le_log ha0 hab
  have hmassCont : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Ici 1) := by
    have hprime : ContinuousOn primeTail (Ici 1) :=
      prime_integrable.continuousOn_Ici_primitive_Ioi
    exact (hprime.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (mem_Ici.mp hx))).ne')
  have hchange := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log a) (b := Real.log b) (f := Real.exp) (f' := Real.exp)
    (g := fun x => max (-primeTail x) 0 / Real.sqrt x) (fun y _ => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn (hmassCont.mono (by
      rintro _ ⟨y, hy, rfl⟩
      rw [uIcc_of_le hlog] at hy
      have h := Real.exp_le_exp.mpr hy.1
      rw [Real.exp_log ha0] at h
      exact (by norm_num : (1 : ℝ) ≤ 2).trans (ha.trans h)))
  rw [Real.exp_log ha0, Real.exp_log hb0] at hchange
  rw [← hchange]
  apply intervalIntegral.integral_congr
  intro y _
  have hs := Real.sqrt_pos.mpr (Real.exp_pos y)
  dsimp [normalizedMass, Function.comp_def]
  have hfactor : Real.exp y / Real.sqrt (Real.exp y) = Real.sqrt (Real.exp y) := by
    apply (div_eq_iff hs.ne').2
    rw [← pow_two, Real.sq_sqrt (Real.exp_nonneg y)]
  calc
    _ = (Real.exp y / Real.sqrt (Real.exp y)) * max (-primeTail (Real.exp y)) 0 := by ring
    _ = _ := by rw [hfactor, mul_max_of_nonneg _ _ hs.le, mul_zero]

/-- Under RH, prime powers give the main term of the prime-only negative mass.
The same bound on the remainder applies to every ordered pair of cutoffs. -/
theorem prime_tail_logarithmic_mass_of_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 2 ≤ a → a ≤ b →
      |(∫ x in a..b, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (b / a)| ≤ C := by
  let C := (∫ y in Ioi (Real.log 2), |windowError y|) + (∑' k : ℕ, ‖actualCoeff k‖) / 5
  refine ⟨C, add_nonneg (integral_nonneg fun y => abs_nonneg _) (by positivity), ?_⟩
  intro a b ha hab
  have ha0 : 0 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hlog := Real.log_le_log ha0 hab
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha
  let v := Real.log a
  let w := Real.log b
  have hiZ : IntervalIntegrable normalizedZeroSeries volume v w :=
    normalizedZeroSeries_continuous.intervalIntegrable _ _
  have hZ : |∫ y in v..w, (normalizedZeroSeries y).re| ≤
      (∑' k : ℕ, ‖actualCoeff k‖) / 5 := by
    have hre : (∫ y in v..w, (normalizedZeroSeries y).re) =
        (∫ y in v..w, normalizedZeroSeries y).re := by
      rw [intervalIntegral.integral_of_le hlog, intervalIntegral.integral_of_le hlog]
      exact integral_re hiZ.1
    rw [hre]
    exact (Complex.abs_re_le_norm _).trans (zero_series_window_bound hRH v w)
  have hsub : Ioc v w ⊆ Ioi (Real.log 2) := fun _ hy => hlo.trans_lt hy.1
  have hie := windowError_integrable hRH
  have hiE : IntervalIntegrable windowError volume v w :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlog).mpr (hie.mono_set hsub)
  have hE : |∫ y in v..w, windowError y| ≤ ∫ y in Ioi (Real.log 2), |windowError y| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hlog).trans ?_
    rw [intervalIntegral.integral_of_le hlog]
    exact setIntegral_mono_set hie.norm (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ hsub)
  have hiZreal : IntervalIntegrable (fun y => (normalizedZeroSeries y).re) volume v w :=
    (Complex.continuous_re.comp normalizedZeroSeries_continuous).intervalIntegrable _ _
  have hidentity : (∫ y in v..w, normalizedMass y) - 2 * (w - v) =
      (∫ y in v..w, windowError y) + ∫ y in v..w, (normalizedZeroSeries y).re := by
    have he : normalizedMass = fun y => windowError y + (2 + (normalizedZeroSeries y).re) := by
      funext y
      dsimp [windowError]
      ring
    rw [he, intervalIntegral.integral_add hiE (intervalIntegrable_const.add hiZreal),
      intervalIntegral.integral_add intervalIntegrable_const hiZreal,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [mass_log_substitution ha hab, Real.log_div hb0.ne' ha0.ne']
  change |(∫ y in v..w, normalizedMass y) - 2 * (w - v)| ≤ C
  rw [hidentity]
  exact (abs_add_le _ _).trans (add_le_add hE hZ)

end D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

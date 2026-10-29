/- GID: D5/S3/Arith/Robin/ThetaTailRobinWitness
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ThetaTailRobinWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual theta tail equals a Mertens error and yields a strict Robin witness. -/

import D5.S3.Arith.Robin.MertensCumulativePeak
import D5.S3.Weil.Mertens.ActualThetaTailLaplace

/-! Classical Abel summation and the Mertens correction connect the actual
Chebyshev theta tail to the prefix-lcm response. The finite Abel calculation
follows ThetaTailPartialSummation in MertensCumulativePeak; unconditional tail
integrability is supplied by ActualThetaTailLaplace. -/

noncomputable section
open Set Finset Real MeasureTheory Filter
open scoped BigOperators Interval Topology
namespace D5.S3.Arith.Robin.ThetaTailRobinWitness
open OriginalMovingWindowMoment (weight_continuous)
private abbrev I (u : ℝ) : ℝ :=
  (Chebyshev.theta u - u) / (u * log u) - Mertens.E₂p u
private abbrev k (u : ℝ) : ℝ := log (log u) - 1 / log u
private abbrev w := ActualRobinClockCovariance.activationDensity
private abbrev reciprocal := ActualRobinClockCovariance.g
private abbrev g (u : ℝ) : ℝ := (Chebyshev.theta u - u) * w u

private theorem theta_mul_integrable {a b : ℝ} (ha : 2 ≤ a)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
    IntegrableOn (fun t => f t * Chebyshev.theta t) (Icc a b) := by
  simpa only [Chebyshev.theta_eq_sum_Icc, sum_filter] using
    (integrableOn_mul_sum_Icc (fun n : ℕ => if n.Prime then log n else 0)
      (show 0 ≤ a by linarith) hf (m := 0))

private theorem reciprocal_deriv {t : ℝ} (ht : 2 ≤ t) :
    deriv reciprocal t = -w t :=
  (ActualRobinClockCovariance.g_has_deriv_at (by linarith : 1 < t)).deriv

private theorem theta_tail_representation {u : ℝ} (hu : 2 ≤ u) :
    I u = Mertens.M + k u - ∫ t in (2 : ℝ)..u, Chebyshev.theta t * w t := by
  let c : ℕ → ℝ := fun n => if n.Prime then log n else 0
  have hc (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = Chebyshev.theta t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hs : (∑ n ∈ Icc 0 ⌊u⌋₊, reciprocal n * c n) =
      ∑ p ∈ Ioc 0 ⌊u⌋₊ with p.Prime, (1 : ℝ) / p := by
    simp only [c, mul_ite, mul_zero]
    rw [← sum_filter]
    rw [PrimorialGlobalLaplaceEnvelope.prime_filter_Icc]
    apply sum_congr rfl
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    have hl0 : log (p : ℝ) ≠ 0 :=
      (log_pos (by exact_mod_cast hpp.one_lt : (1 : ℝ) < p)).ne'
    dsimp [reciprocal, ActualRobinClockCovariance.g]
    field_simp
  have hfi : IntegrableOn (deriv reciprocal) (Icc (2 : ℝ) u) := by
    refine ((weight_continuous (by norm_num : (1 : ℝ) < 2)).neg.integrableOn_Icc
      (μ := volume)).congr_fun
      (fun t ht => (reciprocal_deriv ht.1).symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_integral_mul₁ c (by simp [c]) (by simp [c]) u
    (fun t ht => (ActualRobinClockCovariance.g_has_deriv_at
      (by linarith [ht.1] : 1 < t)).differentiableAt) hfi
  rw [hs, hc] at ha
  have hi : (∫ t in Ioc (2 : ℝ) u, deriv reciprocal t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) =
      -(∫ t in (2 : ℝ)..u, Chebyshev.theta t * w t) := by
    rw [← intervalIntegral.integral_of_le hu, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le hu] at ht
    change deriv reciprocal t * (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = -(Chebyshev.theta t * w t)
    rw [hc, reciprocal_deriv ht.1]
    ring
  rw [hi] at ha
  dsimp [I, Mertens.E₂p, k, reciprocal, ActualRobinClockCovariance.g] at *
  have hu0 : u ≠ 0 := by linarith
  have hl0 : log u ≠ 0 := (log_pos (by linarith : 1 < u)).ne'
  rw [ha]
  field_simp; ring

private theorem k_hasDerivAt {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt k (t * w t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : log t ≠ 0 := (log_pos (by linarith : 1 < t)).ne'
  have hd := ((Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0)).sub
    ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log ht0) hl0)
  refine hd.congr_deriv ?_
  simp only [w, ActualRobinClockCovariance.activationDensity,
    one_mul, zero_mul, zero_sub]
  field_simp [ht0, hl0]; ring

private theorem theta_tail_finite {a u : ℝ} (ha : 2 ≤ a) (hau : a ≤ u) :
    I u = I a - ∫ t in a..u, g t := by
  have hu : 2 ≤ u := ha.trans hau
  have hkw : (∫ t in a..u, t * w t) = k u - k a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hau] at ht
      exact k_hasDerivAt (ha.trans ht.1)
    · exact (continuousOn_id.mul
        (weight_continuous (by linarith : 1 < a))).intervalIntegrable_of_Icc hau
  have htheta : IntervalIntegrable (fun t => Chebyshev.theta t * w t) volume (2 : ℝ) u := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hu]
    simpa only [mul_comm, MellinWeightedVariation.weight, w,
      ActualRobinClockCovariance.activationDensity] using
      theta_mul_integrable (by norm_num : (2 : ℝ) ≤ 2)
      ((weight_continuous (by norm_num : (1 : ℝ) < 2)).integrableOn_Icc (μ := volume))
  have htheta_a : IntervalIntegrable (fun t => Chebyshev.theta t * w t)
      volume (2 : ℝ) a := htheta.mono_set
    (by rw [uIcc_of_le hu, uIcc_of_le ha]; exact Icc_subset_Icc_right hau)
  have htheta_au : IntervalIntegrable (fun t => Chebyshev.theta t * w t) volume a u :=
    htheta.mono_set
    (by rw [uIcc_of_le hu, uIcc_of_le hau]; exact Icc_subset_Icc_left ha)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals htheta_a htheta_au
  have hg : (∫ t in a..u, g t) =
      (∫ t in a..u, Chebyshev.theta t * w t) - (k u - k a) := by
    have hiu : IntervalIntegrable (fun t : ℝ => t * w t) volume a u := by
      apply ContinuousOn.intervalIntegrable_of_Icc hau
      intro t ht
      exact continuousWithinAt_id.mul (weight_continuous (by linarith : 1 < a) t ht)
    rw [← hkw, ← intervalIntegral.integral_sub htheta_au hiu]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [g]
    ring
  rw [theta_tail_representation hu, theta_tail_representation ha, hg]
  linarith

private theorem normalized_error_tendsto : Tendsto I atTop (𝓝 0) := by
  have htheta : Tendsto (fun x : ℝ => (Chebyshev.theta x - x) / (x * log x))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := log 4 + 1)).div_atTop tendsto_log_atTop)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < log x := log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hx0 hl)]
    apply (div_le_iff₀ (mul_pos hx0 hl)).mpr
    have hab : |Chebyshev.theta x - x| ≤ (log 4 + 1) * x := by
      rw [abs_le]
      constructor
      · have := Chebyshev.theta_nonneg x
        have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
        nlinarith [mul_nonneg h4 hx0.le]
      · have := Chebyshev.theta_le_log4_mul_x hx0.le
        linarith
    calc
      _ ≤ (log 4 + 1) * x := hab
      _ = (log 4 + 1) / log x * (x * log x) := by field_simp
  have hE : Tendsto Mertens.E₂p atTop (𝓝 0) := by
    exact Mertens.E₂p.bound'.tendsto_zero_of_tendsto (tendsto_const_nhds (x := (1 : ℝ)))
  simpa only [I, sub_zero] using htheta.sub hE

private theorem kernel_integrable {x : ℝ} (hx : 2 ≤ x) : IntegrableOn g (Ioi x) := by
  have hx0 : 0 < x := by linarith
  have hlog : log 2 ≤ log x := log_le_log (by norm_num) hx
  have h := D5.S3.Weil.Mertens.ActualThetaTailLaplace.actual_theta_tail_laplace_ode.2.2.1
    (log x) hlog
  simpa only [Real.exp_log hx0] using h

private theorem actual_tail_identity {x : ℝ} (hx : 2 ≤ x) :
    -(∫ t in Ioi x, g t) = Mertens.E₂p x - (Chebyshev.theta x - x) / (x * log x) := by
  have hleft := intervalIntegral_tendsto_integral_Ioi x (kernel_integrable hx)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hright := (tendsto_const_nhds (x := I x)).sub normalized_error_tendsto
  have he : (fun u => ∫ t in x..u, g t) =ᶠ[atTop] (fun u => I x - I u) := by
    filter_upwards [eventually_ge_atTop x] with u hu
    linarith [theta_tail_finite hx hu]
  have hlim := tendsto_nhds_unique hleft (hright.congr' he.symm)
  dsimp only [I, id_eq] at hlim ⊢
  linarith

private theorem peak_response {x : ℝ} (hx : 10000 ≤ x)
    (hpeak : 7 / sqrt x < -(∫ t in Ioi x, g t)) :
    Mertens.E₃ x < -4 / sqrt x - (Chebyshev.psi x - x) / (x * log x) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 < sqrt x := sqrt_pos.mpr hx0
  have hid : Mertens.E₃ x + Mertens.E₂p x =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, Mertens.M_eq_summand n) - (Mertens.M - Mertens.γ) := by
    have hsum : (∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Prime, log (1 - (1 : ℝ) / n)) +
        (∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Prime, (1 : ℝ) / n) =
        ∑ n ∈ Ioc 0 ⌊x⌋₊, Mertens.M_eq_summand n := by
      rw [sum_filter, sum_filter, ← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      simp only [Mertens.M_eq_summand]
      split_ifs <;> ring
    unfold Mertens.E₃ Mertens.E₂p
    rw [Mertens.γ.eq_eulerMascheroni]
    linarith [hsum]
  have htail := (abs_le.mp (Mertens.sum_M_eq_summand_le' (by linarith : 2 ≤ x))).2
  have hgap : (Chebyshev.psi x - Chebyshev.theta x) / (x * log x) ≤ 2 / sqrt x := by
    apply (div_le_iff₀ (mul_pos hx0 hl)).mpr
    have hg := Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ x)
    have heq : 2 / sqrt x * (x * log x) = 2 * sqrt x * log x := by
      field_simp
      nlinarith [sq_sqrt hx0.le]
    rwa [heq]
  have hsmall : 4 / x ≤ 1 / sqrt x := by
    apply (div_le_div_iff₀ hx0 hs).mpr
    have hs100 : 100 ≤ sqrt x := by
      have h := sqrt_le_sqrt hx
      norm_num at h
      exact h
    nlinarith [sq_sqrt hx0.le]
  rw [actual_tail_identity (by linarith : 2 ≤ x)] at hpeak
  have hdecomp : (Chebyshev.psi x - x) / (x * log x) =
      (Chebyshev.theta x - x) / (x * log x) +
        (Chebyshev.psi x - Chebyshev.theta x) / (x * log x) := by ring
  rw [hdecomp]
  simp only [div_eq_mul_inv] at htail hgap hsmall hpeak ⊢
  linarith

/-- The actual weighted theta tail is integrable and equals the normalized second
Mertens error. A strict peak above seven square-root units produces the actual
prefix lcm, with its strict Robin violation, exact logarithm and size bound. -/
theorem theta_tail_mertens_robin (x : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      ActualRobinClockCovariance.activationDensity t) (Ioi x) ∧
    -(∫ t in Ioi x, (Chebyshev.theta t - t) *
      ActualRobinClockCovariance.activationDensity t) =
      Mertens.E₂p x - (Chebyshev.theta x - x) / (x * log x) ∧
    (10000 ≤ x → 7 / sqrt x < -(∫ t in Ioi x, (Chebyshev.theta t - t) *
      ActualRobinClockCovariance.activationDensity t) →
      let D := Nat.lcmUpto ⌊x⌋₊
      PrimeFiberPropagation.divisorRatio D > exp eulerMascheroniConstant * log (log D) ∧
        5040 < D ∧ log D = Chebyshev.psi x ∧ (D : ℝ) ≤ exp (x * log x)) := by
  refine ⟨kernel_integrable hx, actual_tail_identity hx, ?_⟩
  intro hlarge hpeak
  exact LcmRobinResponse.common_robin_response hlarge (peak_response hlarge hpeak)

#print axioms theta_tail_mertens_robin
end D5.S3.Arith.Robin.ThetaTailRobinWitness

/- GID: D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaGamma/MasslessTangentConeLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the massless tangent-cone limit of the Archimedean logarithmic tower. -/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

namespace D5.S3.Weil.ZetaGamma.MasslessTangentConeLimit

open Filter Set MeasureTheory Topology

noncomputable section

/-- The logarithmic Archimedean tower built from the evenly spaced positive scales
`sigma + 2m`. -/
noncomputable def archimedean_dispersion (sigma lambda : ℝ) : ℝ :=
  ∑' m : ℕ, Real.log (1 + lambda / (sigma + 2 * m) ^ 2)

/-- The coefficient space of a finite Fourier band. The ambient norm is the standard
finite-product norm; strong convergence below is therefore convergence of coefficient vectors. -/
abbrev FiniteFourierBand (n : ℕ) := Fin n → ℝ

private noncomputable def scalarMultiplier (a : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.lsmul ℝ ℝ a

/-- The diagonal multiplier with the prescribed symbol on a finite Fourier band. -/
noncomputable def finiteBandMultiplier {n : ℕ} (symbol : Fin n → ℝ) :
    FiniteFourierBand n →L[ℝ] FiniteFourierBand n :=
  ContinuousLinearMap.piMap fun mode => scalarMultiplier (symbol mode)

@[simp]
theorem finiteBandMultiplier_apply {n : ℕ} (symbol : Fin n → ℝ)
    (coefficients : FiniteFourierBand n) (mode : Fin n) :
    finiteBandMultiplier symbol coefficients mode = symbol mode * coefficients mode := by
  simp [finiteBandMultiplier, scalarMultiplier]

private theorem summable_majorant {sigma lambda : ℝ} (hsigma : 0 < sigma)
    (hlambda : 0 ≤ lambda) :
    Summable (fun m : ℕ => lambda / (sigma + 2 * m) ^ 2) := by
  rw [← summable_nat_add_iff 1]
  have hp : Summable (fun n : ℕ => lambda * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hp0 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have hp1 : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
      (summable_nat_add_iff 1).mpr hp0
    refine (hp1.mul_left lambda).congr ?_
    intro n
    push_cast
    simp only [one_div]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hp
  have hden : (n : ℝ) + 1 ≤ sigma + 2 * ((n + 1 : ℕ) : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    nlinarith
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hlambda
  simpa only [one_div] using
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hden 2)

private theorem summable_log_tower {sigma lambda : ℝ} (hsigma : 0 < sigma)
    (hlambda : 0 ≤ lambda) :
    Summable (fun m : ℕ => Real.log (1 + lambda / (sigma + 2 * m) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun m => Real.log_nonneg ?_) (fun m => ?_)
    (summable_majorant hsigma hlambda)
  · have : 0 ≤ lambda / (sigma + 2 * m) ^ 2 := by positivity
    linarith
  · have hpos : 0 < 1 + lambda / (sigma + 2 * m) ^ 2 := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    simpa using h

private theorem log_tower_term_nonneg {sigma lambda : ℝ} (hsigma : 0 < sigma)
    (hlambda : 0 ≤ lambda) (m : ℕ) :
    0 ≤ Real.log (1 + lambda / (sigma + 2 * m) ^ 2) := by
  apply Real.log_nonneg
  have : 0 ≤ lambda / (sigma + 2 * m) ^ 2 := by positivity
  linarith

private theorem log_tower_antitone {sigma a : ℝ} (hsigma : 0 < sigma) :
    AntitoneOn (fun x : ℝ => Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)) (Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  apply Real.strictMonoOn_log.monotoneOn
  · show 1 + a ^ 2 / (sigma + 2 * y) ^ 2 ∈ Ioi 0
    rw [mem_Ioi]
    positivity
  · show 1 + a ^ 2 / (sigma + 2 * x) ^ 2 ∈ Ioi 0
    rw [mem_Ioi]
    positivity
  · have hfrac : a ^ 2 / (sigma + 2 * y) ^ 2 ≤ a ^ 2 / (sigma + 2 * x) ^ 2 := by
      apply div_le_div_of_nonneg_left (sq_nonneg a) (by positivity)
      apply pow_le_pow_left₀ (by positivity) _ 2
      linarith
    linarith

private theorem log_tower_antiderivative {sigma a x : ℝ} (hsigma : 0 < sigma)
    (ha : 0 < a) (hx : 0 ≤ x) :
    HasDerivAt
      (fun y : ℝ =>
        ((sigma + 2 * y) / 2) * Real.log (1 + a ^ 2 / (sigma + 2 * y) ^ 2) +
          a * Real.arctan ((sigma + 2 * y) / a))
      (Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)) x := by
  let u : ℝ := sigma + 2 * x
  have hu : 0 < u := by dsimp [u]; linarith
  have huDeriv : HasDerivAt (fun y : ℝ => sigma + 2 * y) 2 x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul 2).const_add sigma
  have hsq : HasDerivAt (fun y : ℝ => (sigma + 2 * y) ^ 2) (4 * u) x := by
    refine (huDeriv.pow 2).congr_deriv ?_
    dsimp [u]
    ring
  have hquot : HasDerivAt (fun y : ℝ => a ^ 2 / (sigma + 2 * y) ^ 2)
      (-4 * a ^ 2 * u / u ^ 4) x := by
    have hraw := (hasDerivAt_const x (a ^ 2)).div hsq (pow_ne_zero 2 hu.ne')
    refine hraw.congr_deriv ?_
    dsimp only [u]
    field_simp [hu.ne']
    ring
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (1 + a ^ 2 / (sigma + 2 * y) ^ 2))
      ((1 + a ^ 2 / u ^ 2)⁻¹ * (-4 * a ^ 2 * u / u ^ 4)) x := by
    exact (Real.hasDerivAt_log (by positivity : 1 + a ^ 2 / u ^ 2 ≠ 0)).comp x
      (hquot.const_add 1)
  have hfirst := ((huDeriv.const_mul (1 / 2)).mul hlog)
  have harctan : HasDerivAt (fun y : ℝ => Real.arctan ((sigma + 2 * y) / a))
      ((1 / (1 + (u / a) ^ 2)) * (2 / a)) x := by
    exact (Real.hasDerivAt_arctan (u / a)).comp x (huDeriv.div_const a)
  have htotal := hfirst.add (harctan.const_mul a)
  have hfun :
      (fun y : ℝ =>
        ((sigma + 2 * y) / 2) * Real.log (1 + a ^ 2 / (sigma + 2 * y) ^ 2) +
          a * Real.arctan ((sigma + 2 * y) / a)) =
        (((fun y : ℝ => (1 / 2) * (sigma + 2 * y)) *
            fun y : ℝ => Real.log (1 + a ^ 2 / (sigma + 2 * y) ^ 2)) +
          fun y : ℝ => a * Real.arctan ((sigma + 2 * y) / a)) := by
    funext y
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [hfun]
  refine htotal.congr_deriv ?_
  dsimp only [u]
  field_simp [hu.ne', ha.ne']
  ring

private theorem integral_log_tower {sigma a : ℝ} (hsigma : 0 < sigma) (ha : 0 < a)
    (N : ℕ) :
    (∫ x : ℝ in 0..N, Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)) =
      (((sigma + 2 * N) / 2) * Real.log (1 + a ^ 2 / (sigma + 2 * N) ^ 2) +
          a * Real.arctan ((sigma + 2 * N) / a)) -
        ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) +
          a * Real.arctan (sigma / a)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ =>
      ((sigma + 2 * y) / 2) * Real.log (1 + a ^ 2 / (sigma + 2 * y) ^ 2) +
        a * Real.arctan ((sigma + 2 * y) / a))
    (f' := fun x : ℝ => Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2))
    (a := 0) (b := (N : ℝ))
    (fun x hx => by
      rw [uIcc_of_le (by positivity)] at hx
      exact log_tower_antiderivative hsigma ha hx.1)
    (by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [uIcc_of_le (by positivity)] at hx
      apply ContinuousAt.continuousWithinAt
      have hden : sigma + 2 * x ≠ 0 := by nlinarith [hx.1]
      have hlinearContinuous : ContinuousAt (fun y : ℝ => sigma + 2 * y) x := by
        fun_prop
      have hargumentContinuous :
          ContinuousAt (fun y : ℝ => 1 + a ^ 2 / (sigma + 2 * y) ^ 2) x :=
        continuousAt_const.add
          (continuousAt_const.div₀ (hlinearContinuous.pow 2) (pow_ne_zero 2 hden))
      exact hargumentContinuous.log (by positivity))
  simpa using h

private theorem tendsto_log_tower_antiderivative_atTop {sigma a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun x : ℝ =>
        ((sigma + 2 * x) / 2) * Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2) +
          a * Real.arctan ((sigma + 2 * x) / a))
      atTop (𝓝 (a * (Real.pi / 2))) := by
  have hlinear : Tendsto (fun x : ℝ => sigma + 2 * x) atTop atTop := by
    have htwo : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_id
    exact tendsto_atTop_add_const_left atTop sigma htwo
  have hsquare : Tendsto (fun u : ℝ => u ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hscaledLogBase :
      Tendsto (fun u : ℝ => u ^ 2 * Real.log (1 + a ^ 2 / u ^ 2)) atTop (𝓝 (a ^ 2)) := by
    convert (Real.tendsto_mul_log_one_add_div_atTop (a ^ 2)).comp hsquare using 1
    · funext u
      simp only [Function.comp_apply]
  have hscaledLog := hscaledLogBase.comp hlinear
  have hinv : Tendsto (fun x : ℝ => 1 / (2 * (sigma + 2 * x))) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num) hlinear)
  have hfirstRaw := hinv.mul hscaledLog
  have hfirst : Tendsto
      (fun x : ℝ => ((sigma + 2 * x) / 2) *
        Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)) atTop (𝓝 0) := by
    have hfirstRawZero : Tendsto
        (fun x : ℝ => 1 / (2 * (sigma + 2 * x)) *
          ((sigma + 2 * x) ^ 2 * Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, zero_mul] using hfirstRaw
    apply hfirstRawZero.congr'
    filter_upwards [eventually_gt_atTop (-(sigma / 2))] with x hx
    have hne : sigma + 2 * x ≠ 0 := by linarith
    field_simp [hne]
  have hargument : Tendsto (fun x : ℝ => (sigma + 2 * x) / a) atTop atTop := by
    have h := Tendsto.atTop_mul_const (inv_pos.mpr ha) hlinear
    simpa only [div_eq_mul_inv] using h
  have harctan : Tendsto (fun x : ℝ => Real.arctan ((sigma + 2 * x) / a))
      atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hargument
  convert hfirst.add (harctan.const_mul a) using 1
  all_goals ring

private theorem tendsto_integral_log_tower_nat {sigma a : ℝ} (hsigma : 0 < sigma)
    (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      ∫ x : ℝ in 0..N, Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)) atTop
      (𝓝 (a * (Real.pi / 2) -
        ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) +
          a * Real.arctan (sigma / a)))) := by
  have hF := (tendsto_log_tower_antiderivative_atTop (sigma := sigma) ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hF.sub_const
    ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) + a * Real.arctan (sigma / a))
  apply h.congr'
  filter_upwards with N
  exact (integral_log_tower hsigma ha N).symm

private theorem log_tower_bounds {sigma a : ℝ} (hsigma : 0 < sigma) (ha : 0 < a) :
    let integralLimit :=
      a * (Real.pi / 2) -
        ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) +
          a * Real.arctan (sigma / a))
    integralLimit ≤ archimedean_dispersion sigma (a ^ 2) ∧
      archimedean_dispersion sigma (a ^ 2) ≤
        Real.log (1 + a ^ 2 / sigma ^ 2) + integralLimit := by
  dsimp only
  let f : ℕ → ℝ := fun m => Real.log (1 + a ^ 2 / (sigma + 2 * m) ^ 2)
  let g : ℝ → ℝ := fun x => Real.log (1 + a ^ 2 / (sigma + 2 * x) ^ 2)
  let integralLimit : ℝ :=
    a * (Real.pi / 2) -
      ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) +
        a * Real.arctan (sigma / a))
  have hsum : Summable f := summable_log_tower hsigma (sq_nonneg a)
  have hnonneg (m : ℕ) : 0 ≤ f m := log_tower_term_nonneg hsigma (sq_nonneg a) m
  have hIntegral := tendsto_integral_log_tower_nat hsigma ha
  have hIntegral' : Tendsto (fun N : ℕ => ∫ x : ℝ in 0..N, g x) atTop
      (𝓝 integralLimit) := hIntegral
  have hlower : integralLimit ≤ ∑' m : ℕ, f m := by
    apply le_of_tendsto hIntegral'
    filter_upwards with N
    have hanti : AntitoneOn g (Icc 0 (0 + (N : ℝ))) :=
      (log_tower_antitone (a := a) hsigma).mono (fun _ hx => hx.1)
    have hint : (∫ x : ℝ in 0..N, g x) ≤ ∑ m ∈ Finset.range N, f m := by
      simpa [f, g] using hanti.integral_le_sum
    exact hint.trans (hsum.sum_le_tsum (Finset.range N) (fun m _ => hnonneg m))
  have hintegral_le (N : ℕ) : (∫ x : ℝ in 0..N, g x) ≤ integralLimit := by
    apply ge_of_tendsto hIntegral'
    filter_upwards [eventually_ge_atTop N] with M hNM
    apply intervalIntegral.integral_mono_interval le_rfl (Nat.cast_nonneg N)
      (by exact_mod_cast hNM)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 ≤ x := hx.1.le
      dsimp only [g]
      apply Real.log_nonneg
      have : 0 ≤ a ^ 2 / (sigma + 2 * x) ^ 2 := by positivity
      linarith
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [uIcc_of_le (Nat.cast_nonneg M)] at hx
      apply ContinuousAt.continuousWithinAt
      have hden : sigma + 2 * x ≠ 0 := by nlinarith [hx.1]
      have hlinearContinuous : ContinuousAt (fun y : ℝ => sigma + 2 * y) x := by
        fun_prop
      have hargumentContinuous :
          ContinuousAt (fun y : ℝ => 1 + a ^ 2 / (sigma + 2 * y) ^ 2) x :=
        continuousAt_const.add
          (continuousAt_const.div₀ (hlinearContinuous.pow 2) (pow_ne_zero 2 hden))
      exact hargumentContinuous.log (by positivity)
  have htail : ∑' n : ℕ, f (n + 1) ≤ integralLimit := by
    apply Real.tsum_le_of_sum_range_le (fun n => hnonneg (n + 1))
    intro N
    have hanti : AntitoneOn g (Icc 0 (0 + (N : ℝ))) :=
      (log_tower_antitone (a := a) hsigma).mono (fun _ hx => hx.1)
    have hcompare : ∑ n ∈ Finset.range N, f (n + 1) ≤ ∫ x : ℝ in 0..N, g x := by
      simpa [f, g] using hanti.sum_le_integral
    exact hcompare.trans (hintegral_le N)
  have hupper : ∑' m : ℕ, f m ≤ f 0 + integralLimit := by
    rw [← hsum.sum_add_tsum_nat_add 1, Finset.sum_range_one]
    gcongr
  constructor
  · simpa [archimedean_dispersion, f, integralLimit] using hlower
  · simpa [archimedean_dispersion, f, integralLimit] using hupper

private theorem tendsto_log_tower_boundary_div_atTop {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto (fun a : ℝ => Real.log (1 + a ^ 2 / sigma ^ 2) / a) atTop (𝓝 0) := by
  have hpow : Tendsto (fun a : ℝ => a ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinvPow : Tendsto (fun a : ℝ => 1 / a ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hinside : Tendsto (fun a : ℝ => 1 / a ^ 2 + 1 / sigma ^ 2) atTop
      (𝓝 (1 / sigma ^ 2)) := by
    simpa using hinvPow.add tendsto_const_nhds
  have hinsideLog : Tendsto (fun a : ℝ => Real.log (1 / a ^ 2 + 1 / sigma ^ 2))
      atTop (𝓝 (Real.log (1 / sigma ^ 2))) :=
    hinside.log (by positivity)
  have hinsideLogDiv : Tendsto
      (fun a : ℝ => Real.log (1 / a ^ 2 + 1 / sigma ^ 2) / a) atTop (𝓝 0) :=
    hinsideLog.div_atTop tendsto_id
  have hlogDiv : Tendsto (fun a : ℝ => Real.log a / a) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hsum := (hlogDiv.const_mul 2).add hinsideLogDiv
  have hsumZero : Tendsto
      (fun x : ℝ => 2 * (Real.log x / x) + Real.log (1 / x ^ 2 + 1 / sigma ^ 2) / x)
      atTop (𝓝 0) := by
    simpa using hsum
  apply hsumZero.congr'
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hfactor : 1 + a ^ 2 / sigma ^ 2 =
      a ^ 2 * (1 / a ^ 2 + 1 / sigma ^ 2) := by
    field_simp [ha.ne', hsigma.ne']
  rw [hfactor, Real.log_mul ha2.ne' (by positivity), Real.log_pow]
  ring

private theorem high_frequency_dispersion_limit {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto (fun a : ℝ => archimedean_dispersion sigma (a ^ 2) / a) atTop
      (𝓝 (Real.pi / 2)) := by
  have hlog := tendsto_log_tower_boundary_div_atTop hsigma
  have harg : Tendsto (fun a : ℝ => sigma / a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hatan : Tendsto (fun a : ℝ => Real.arctan (sigma / a)) atTop (𝓝 0) := by
    change Tendsto (Real.arctan ∘ fun a : ℝ => sigma / a) atTop (𝓝 0)
    simpa only [Real.arctan_zero] using (Real.continuous_arctan.tendsto 0).comp harg
  let lower : ℝ → ℝ := fun a =>
    (a * (Real.pi / 2) -
      ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) +
        a * Real.arctan (sigma / a))) / a
  let upper : ℝ → ℝ := fun a =>
    (Real.log (1 + a ^ 2 / sigma ^ 2) +
      (a * (Real.pi / 2) -
        ((sigma / 2) * Real.log (1 + a ^ 2 / sigma ^ 2) +
          a * Real.arctan (sigma / a)))) / a
  have hlower : Tendsto lower atTop (𝓝 (Real.pi / 2)) := by
    have hconst : Tendsto (fun _ : ℝ => Real.pi / 2) atTop (𝓝 (Real.pi / 2)) :=
      tendsto_const_nhds
    have hraw := (hconst.sub (hlog.const_mul (sigma / 2))).sub hatan
    have h : Tendsto
        (fun a : ℝ => Real.pi / 2 -
          (sigma / 2) * (Real.log (1 + a ^ 2 / sigma ^ 2) / a) -
          Real.arctan (sigma / a)) atTop (𝓝 (Real.pi / 2)) := by
      simpa using hraw
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with a ha
    dsimp only [lower]
    field_simp [ha.ne']
    ring
  have hupper : Tendsto upper atTop (𝓝 (Real.pi / 2)) := by
    have h := hlog.add hlower
    have h' : Tendsto
        (fun x : ℝ => Real.log (1 + x ^ 2 / sigma ^ 2) / x + lower x)
        atTop (𝓝 (Real.pi / 2)) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 0] with a ha
    dsimp only [lower, upper]
    field_simp [ha.ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop 0] with a ha
    dsimp only [lower]
    exact (div_le_div_iff_of_pos_right ha).mpr (log_tower_bounds hsigma ha).1
  · filter_upwards [eventually_gt_atTop 0] with a ha
    dsimp only [upper]
    exact (div_le_div_iff_of_pos_right ha).mpr (log_tower_bounds hsigma ha).2

private theorem scalar_massless_limit {sigma lambda : ℝ} (hsigma : 0 < sigma)
    (hlambda : 0 ≤ lambda) :
    Tendsto (fun epsilon : ℝ =>
      epsilon * archimedean_dispersion sigma (lambda / epsilon ^ 2)) (𝓝[>] 0)
      (𝓝 ((Real.pi / 2) * Real.sqrt lambda)) := by
  rcases hlambda.eq_or_lt with hlambdaZero | hlambdaPositive
  · subst lambda
    simp [archimedean_dispersion]
  · have hsqrt : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambdaPositive
    have hscale : Tendsto (fun epsilon : ℝ => Real.sqrt lambda / epsilon)
        (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using
        Tendsto.const_mul_atTop hsqrt tendsto_inv_nhdsGT_zero
    have hhigh := (high_frequency_dispersion_limit hsigma).comp hscale
    have hscaled := hhigh.const_mul (Real.sqrt lambda)
    have hscaled' : Tendsto
        (fun epsilon : ℝ => Real.sqrt lambda *
          (archimedean_dispersion sigma ((Real.sqrt lambda / epsilon) ^ 2) /
            (Real.sqrt lambda / epsilon))) (𝓝[>] 0)
        (𝓝 ((Real.pi / 2) * Real.sqrt lambda)) := by
      convert hscaled using 1
      · funext epsilon
        simp only [Function.comp_apply]
      · ring
    apply hscaled'.congr'
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    rw [mem_Ioi] at hepsilon
    have hsqrtSq : (Real.sqrt lambda) ^ 2 = lambda := Real.sq_sqrt hlambda
    rw [div_pow, hsqrtSq]
    field_simp [hsqrt.ne', hepsilon.ne']

/-- For every positive offset, the scaled logarithmic tower converges to the massless
symbol. The second conjunct is the operator clause: on every finite Fourier band, the
associated diagonal multipliers converge strongly to the massless multiplier. -/
theorem massless_tangent_cone_limit (sigma : ℝ) (hsigma : 0 < sigma) :
    (∀ lambda : ℝ, 0 ≤ lambda →
      Tendsto (fun epsilon : ℝ =>
        epsilon * archimedean_dispersion sigma (lambda / epsilon ^ 2)) (𝓝[>] 0)
        (𝓝 ((Real.pi / 2) * Real.sqrt lambda))) ∧
    (∀ (n : ℕ) (frequency : Fin n → ℝ) (coefficients : FiniteFourierBand n),
      Tendsto
        (fun epsilon : ℝ =>
          finiteBandMultiplier (fun mode =>
            epsilon * archimedean_dispersion sigma
              (frequency mode ^ 2 / epsilon ^ 2)) coefficients)
        (𝓝[>] 0)
        (𝓝 (finiteBandMultiplier (fun mode =>
          (Real.pi / 2) * |frequency mode|) coefficients))) := by
  constructor
  · intro lambda hlambda
    exact scalar_massless_limit hsigma hlambda
  · intro n frequency coefficients
    refine tendsto_pi_nhds.mpr fun mode => ?_
    have hmode := scalar_massless_limit hsigma (sq_nonneg (frequency mode))
    have hsymbol : Tendsto
        (fun epsilon : ℝ => epsilon * archimedean_dispersion sigma
          (frequency mode ^ 2 / epsilon ^ 2))
        (𝓝[>] 0) (𝓝 ((Real.pi / 2) * |frequency mode|)) := by
      simpa only [Real.sqrt_sq_eq_abs] using hmode
    simpa only [finiteBandMultiplier_apply] using
      hsymbol.mul_const (coefficients mode)

#print axioms archimedean_dispersion
#print axioms massless_tangent_cone_limit

end

end D5.S3.Weil.ZetaGamma.MasslessTangentConeLimit

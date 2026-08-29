/- GID: D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   digest: Recover Cayley moments from scaled Laguerre kernels and finite windows. -/

import D5.S3.Analytic.LiCausalTrichotomy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

open MeasureTheory Set
open D5.S3.Analytic.LiCausalTrichotomy

/-- The all-pass Cayley character at positive scale `a`. -/
noncomputable def cayleyCharacter (a xi : ℝ) : ℂ :=
  ((xi : ℂ) + Complex.I * a) / ((xi : ℂ) - Complex.I * a)

/-- The causal scaled Laguerre observation kernel. -/
noncomputable def laguerreKernel (n : ℕ) (a t : ℝ) : ℝ :=
  if 0 ≤ t then 2 * a * Real.exp (-a * t) * laguerreOne (n - 1) (2 * a * t) else 0

/-- The total mass of the finite resolvent-weighted spectral measure. -/
noncomputable def spectralMass (rho : Measure ℝ) : ℝ := rho.real Set.univ

/-- The positive-sign Fourier correlation of the resolvent-weighted measure. -/
noncomputable def resolventCorrelation (rho : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ xi : ℝ, Complex.exp (Complex.I * t * xi) ∂rho

/-- The Cayley pushforward moment, written on its source real-line measure. -/
noncomputable def cayleyMoment (rho : Measure ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  ∫ xi : ℝ, cayleyCharacter a xi ^ n ∂rho

/-- The Cayley moment estimator obtained from the correlation window `[0, 2L]`. -/
noncomputable def windowMoment (rho : Measure ℝ) (n : ℕ) (a L : ℝ) : ℂ :=
  (spectralMass rho : ℂ) -
    ∫ t : ℝ in Ioc 0 (2 * L),
      (laguerreKernel n a t : ℂ) * resolventCorrelation rho t

/-- The absolute Laguerre-kernel mass beyond the observation window. -/
noncomputable def laguerreTail (n : ℕ) (a L : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi (2 * L), |laguerreKernel n a t|

/-- The finite-window estimator associated with a local particular correlation and a budget. -/
noncomputable def budgetWindowMoment
    (n : ℕ) (a L : ℝ) (H0 : ℝ → ℝ) (R : ℝ) : ℝ :=
  R -
    ∫ t : ℝ in Ioc 0 (2 * L),
      laguerreKernel n a t * (H0 t + R * Real.cosh (a * t))

private theorem half_scale_cayley_laguerre_identity {n : ℕ} (hn : n ≠ 0) (gamma : ℝ) :
    cayley gamma ^ n =
      1 - ∫ t : ℝ in Ioi 0,
        ((Real.exp (-t / 2) * laguerreOne (n - 1) t : ℝ) : ℂ) *
          Complex.exp (-Complex.I * gamma * t) := by
  have hfourier := causalPacket_fourier (n := n) hn gamma
  rw [angularFourier] at hfourier
  dsimp only [causalPacket] at hfourier
  simp only [hn, if_false] at hfourier
  rw [show (fun u : ℝ =>
      (if u < 0 then
        ((-(Real.exp (u / 2) * laguerreOne (n - 1) (-u)) : ℝ) : ℂ)
      else 0) * Complex.exp (Complex.I * gamma * u)) =
      (Iio 0).indicator (fun u =>
        ((-(Real.exp (u / 2) * laguerreOne (n - 1) (-u)) : ℝ) : ℂ) *
          Complex.exp (Complex.I * gamma * u)) by
    funext u
    by_cases hu : u < 0 <;> simp [hu]] at hfourier
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio] at hfourier
  have hreflect := integral_comp_neg_Ioi 0 (fun t : ℝ =>
    ((-(Real.exp (t / 2) * laguerreOne (n - 1) (-t)) : ℝ) : ℂ) *
      Complex.exp (Complex.I * gamma * t))
  simp only [neg_zero] at hreflect
  rw [← hreflect] at hfourier
  simp only [neg_neg] at hfourier
  have hleft :
      (∫ t : ℝ in Ioi 0,
        ((-(Real.exp (-t / 2) * laguerreOne (n - 1) t) : ℝ) : ℂ) *
          Complex.exp (Complex.I * gamma * ((-t : ℝ) : ℂ))) =
        -(∫ t : ℝ in Ioi 0,
          ((Real.exp (-t / 2) * laguerreOne (n - 1) t : ℝ) : ℂ) *
            Complex.exp (-Complex.I * gamma * t)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    push_cast
    ring
  rw [hleft] at hfourier
  have hli : liSymbol n gamma = cayley gamma ^ n - 1 := by
    rw [liSymbol]
    push_cast
    rw [Complex.cpow_natCast]
  rw [hli] at hfourier
  calc
    cayley gamma ^ n = (cayley gamma ^ n - 1) + 1 := by ring
    _ = -(∫ t : ℝ in Ioi 0,
        ((Real.exp (-t / 2) * laguerreOne (n - 1) t : ℝ) : ℂ) *
          Complex.exp (-Complex.I * gamma * t)) + 1 := by rw [← hfourier]
    _ = 1 - ∫ t : ℝ in Ioi 0,
        ((Real.exp (-t / 2) * laguerreOne (n - 1) t : ℝ) : ℂ) *
          Complex.exp (-Complex.I * gamma * t) := by ring

/-- The scaled Laguerre kernel is the causal impulse response of a Cayley power. -/
theorem cayley_laguerre_identity {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (xi : ℝ) :
    cayleyCharacter a xi ^ n =
      1 - ∫ t : ℝ in Ioi 0,
        (laguerreKernel n a t : ℂ) * Complex.exp (-Complex.I * xi * t) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  let b : ℝ := 2 * a
  let gamma : ℝ := xi / b
  let g : ℝ → ℂ := fun u =>
    ((Real.exp (-u / 2) * laguerreOne (n - 1) u : ℝ) : ℂ) *
      Complex.exp (-Complex.I * gamma * u)
  have hb : 0 < b := by dsimp [b]; positivity
  have hscale := integral_comp_mul_left_Ioi g 0 hb
  have hkernel :
      (fun t : ℝ =>
        (laguerreKernel n a t : ℂ) * Complex.exp (-Complex.I * xi * t))
        =ᶠ[ae (volume.restrict (Ioi 0))]
      fun t => (b : ℂ) * g (b * t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    simp only [laguerreKernel, ht0, if_true, g, b, gamma]
    rw [show -a * t = -(2 * a * t) / 2 by ring]
    rw [show (-Complex.I * (xi : ℂ) * t) =
        -Complex.I * (xi / (2 * a) : ℝ) * (2 * a * t) by
      push_cast
      field_simp [ha.ne']]
    push_cast
    ring
  have hintegral :
      (∫ t : ℝ in Ioi 0,
          (laguerreKernel n a t : ℂ) * Complex.exp (-Complex.I * xi * t)) =
        ∫ u : ℝ in Ioi 0, g u := by
    rw [integral_congr_ae hkernel]
    calc
      (∫ t : ℝ in Ioi 0, (b : ℂ) * g (b * t)) =
          (b : ℂ) * ∫ t : ℝ in Ioi 0, g (b * t) := by
        exact MeasureTheory.integral_const_mul (μ := volume.restrict (Ioi 0))
          (b : ℂ) (fun t : ℝ => g (b * t))
      _ = (b : ℂ) * ((b⁻¹ : ℝ) • ∫ u : ℝ in Ioi 0, g u) := by
        rw [hscale]
        simp only [mul_zero]
      _ = ∫ u : ℝ in Ioi 0, g u := by
        rw [Complex.real_smul]
        push_cast
        field_simp [hb.ne']
  have hbase := half_scale_cayley_laguerre_identity hn0 gamma
  have hcayley : cayleyCharacter a xi = cayley gamma := by
    simp only [cayleyCharacter, cayley, gamma, b]
    have hleft : ((xi : ℂ) - Complex.I * a) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hright : ((xi / (2 * a) : ℝ) : ℂ) - Complex.I / 2 ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      have him := congrArg Complex.im h
      norm_num [Complex.div_im, Complex.normSq_apply] at him
    rw [div_eq_div_iff hleft hright]
    push_cast
    field_simp [ha.ne']
  rw [hintegral]
  calc
    cayleyCharacter a xi ^ n = cayley gamma ^ n := by rw [hcayley]
    _ = 1 - ∫ t : ℝ in Ioi 0,
        ((Real.exp (-t / 2) * laguerreOne (n - 1) t : ℝ) : ℂ) *
          Complex.exp (-Complex.I * gamma * t) := hbase
    _ = 1 - ∫ u : ℝ in Ioi 0, g u := by rfl

private theorem laguerreKernel_integrableOn {n : ℕ} {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (laguerreKernel n a t : ℂ)) (Ioi 0) := by
  have hmain : IntegrableOn (fun t : ℝ =>
      ((2 * a * Real.exp (-a * t) * laguerreOne (n - 1) (2 * a * t) : ℝ) : ℂ))
      (Ioi 0) := by
    simp only [laguerreOne]
    push_cast
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro j hj
    have hbase :=
      (integrableOn_complex_laplace_moment (a := (-a : ℂ)) (by simpa using ha) j).const_mul
        (((2 * a : ℝ) : ℂ) *
          (((-1 : ℝ) ^ j * Nat.choose (n - 1 + 1) (j + 1) / j.factorial : ℝ) : ℂ) *
          ((2 * a : ℝ) : ℂ) ^ j)
    apply hbase.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _ht
    rw [show Complex.exp ((-a : ℂ) * t) = (Real.exp (-a * t) : ℂ) by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      rfl]
    push_cast
    ring
  apply hmain.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  simp only [laguerreKernel, ht0, if_true]

private theorem norm_resolventCorrelation_le (rho : Measure ℝ) [IsFiniteMeasure rho] (t : ℝ) :
    ‖resolventCorrelation rho t‖ ≤ spectralMass rho := by
  rw [resolventCorrelation, spectralMass]
  simpa using (norm_integral_le_of_norm_le_const (μ := rho) (C := 1)
    (Filter.Eventually.of_forall fun xi => by
      simp [Complex.norm_exp, Complex.mul_re]))

private theorem negative_phase_eq_correlation (rho : Measure ℝ)
    (hEven : Measure.map (fun xi : ℝ => -xi) rho = rho) (t : ℝ) :
    (∫ xi : ℝ, Complex.exp (-Complex.I * t * xi) ∂rho) = resolventCorrelation rho t := by
  have hmap := MeasureTheory.integral_map (μ := rho) (φ := fun xi : ℝ => -xi)
    (f := fun xi : ℝ => Complex.exp (Complex.I * t * xi)) (by fun_prop) (by fun_prop)
  rw [hEven] at hmap
  rw [resolventCorrelation]
  calc
    (∫ xi : ℝ, Complex.exp (-Complex.I * t * xi) ∂rho) =
        ∫ xi : ℝ, Complex.exp (Complex.I * t * ((-xi : ℝ) : ℂ)) ∂rho := by
      apply integral_congr_ae
      filter_upwards with xi
      congr 1
      push_cast
      ring
    _ = ∫ xi : ℝ, Complex.exp (Complex.I * t * xi) ∂rho := hmap.symm

private theorem laguerre_moment_tomography_kernel
    (rho : Measure ℝ) [IsFiniteMeasure rho]
    (hEven : Measure.map (fun xi : ℝ => -xi) rho = rho)
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    cayleyMoment rho n a =
      (spectralMass rho : ℂ) - ∫ t : ℝ in Ioi 0,
        (laguerreKernel n a t : ℂ) * resolventCorrelation rho t := by
  have hk : IntegrableOn (fun t : ℝ => (laguerreKernel n a t : ℂ)) (Ioi 0) :=
    laguerreKernel_integrableOn ha
  have hone : Integrable (fun _ : ℝ => (1 : ℂ)) rho := integrable_const 1
  have hmodel := hk.mul_prod hone
  have hphase : StronglyMeasurable (fun z : ℝ × ℝ =>
      Complex.exp (-(Complex.I * z.2 * z.1))) := by
    fun_prop
  have hF : Integrable (Function.uncurry (fun t : ℝ => fun xi : ℝ =>
      (laguerreKernel n a t : ℂ) * Complex.exp (-(Complex.I * xi * t))))
      ((volume.restrict (Ioi 0)).prod rho) := by
    change Integrable (fun z : ℝ × ℝ =>
      (laguerreKernel n a z.1 : ℂ) * Complex.exp (-(Complex.I * z.2 * z.1)))
      ((volume.restrict (Ioi 0)).prod rho)
    refine hmodel.norm.mono' ?_ ?_
    · exact (hmodel.aestronglyMeasurable.mul hphase.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun z => by simp)
    · filter_upwards with z
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(Complex.I * (z.2 : ℂ) * (z.1 : ℂ))).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero]
      simp
  have hinner : Integrable (fun xi : ℝ => ∫ t : ℝ in Ioi 0,
      (laguerreKernel n a t : ℂ) * Complex.exp (-(Complex.I * xi * t))) rho := by
    simpa using hF.integral_prod_right
  have hpoint : (fun xi : ℝ => cayleyCharacter a xi ^ n) =ᵐ[rho]
      fun xi : ℝ => 1 - ∫ t : ℝ in Ioi 0,
        (laguerreKernel n a t : ℂ) * Complex.exp (-(Complex.I * xi * t)) := by
    filter_upwards with xi
    simpa only [neg_mul] using cayley_laguerre_identity hn ha xi
  rw [cayleyMoment]
  rw [integral_congr_ae hpoint]
  rw [integral_sub (integrable_const 1) hinner]
  rw [show (∫ _xi : ℝ, (1 : ℂ) ∂rho) = (spectralMass rho : ℂ) by
    simp [spectralMass]]
  rw [← integral_integral_swap hF]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [MeasureTheory.integral_const_mul]
  rw [show (fun xi : ℝ => Complex.exp (-(Complex.I * xi * t))) =
      fun xi : ℝ => Complex.exp (-Complex.I * t * xi) by
    funext xi
    congr 1
    ring]
  rw [negative_phase_eq_correlation rho hEven t]

/-- Every positive Cayley moment is a Laguerre coefficient of the even resolvent correlation. -/
theorem laguerre_moment_tomography
    (rho : Measure ℝ) [IsFiniteMeasure rho]
    (hEven : Measure.map (fun xi : ℝ => -xi) rho = rho)
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    (cayleyMoment rho n a =
      (spectralMass rho : ℂ) - ∫ t : ℝ in Ioi 0,
        (laguerreKernel n a t : ℂ) * resolventCorrelation rho t) ∧
    (cayleyMoment rho n a =
      (spectralMass rho : ℂ) - (2 * a : ℝ) * ∫ t : ℝ in Ioi 0,
        ((Real.exp (-a * t) * laguerreOne (n - 1) (2 * a * t) : ℝ) : ℂ) *
          resolventCorrelation rho t) := by
  have hkernel := laguerre_moment_tomography_kernel rho hEven hn ha
  refine ⟨hkernel, ?_⟩
  rw [hkernel]
  congr 1
  calc
    (∫ t : ℝ in Ioi 0,
        (laguerreKernel n a t : ℂ) * resolventCorrelation rho t) =
      ∫ t : ℝ in Ioi 0, (2 * a : ℝ) *
        (((Real.exp (-a * t) * laguerreOne (n - 1) (2 * a * t) : ℝ) : ℂ) *
          resolventCorrelation rho t) := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      simp only [laguerreKernel, ht0, if_true]
      push_cast
      ring
    _ = (2 * a : ℝ) * ∫ t : ℝ in Ioi 0,
        ((Real.exp (-a * t) * laguerreOne (n - 1) (2 * a * t) : ℝ) : ℂ) *
          resolventCorrelation rho t := by
      exact MeasureTheory.integral_const_mul (μ := volume.restrict (Ioi 0))
        ((2 * a : ℝ) : ℂ) (fun t : ℝ =>
          ((Real.exp (-a * t) * laguerreOne (n - 1) (2 * a * t) : ℝ) : ℂ) *
            resolventCorrelation rho t)

/-- Truncating the correlation window loses at most total mass times kernel tail mass. -/
theorem finite_window_moment_tube
    (rho : Measure ℝ) [IsFiniteMeasure rho]
    (hEven : Measure.map (fun xi : ℝ => -xi) rho = rho)
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) {L : ℝ} (hL : 0 ≤ L) :
    ‖cayleyMoment rho n a - windowMoment rho n a L‖ ≤
      spectralMass rho * laguerreTail n a L := by
  let f : ℝ → ℂ := fun t =>
    (laguerreKernel n a t : ℂ) * resolventCorrelation rho t
  have hphase : StronglyMeasurable (fun z : ℝ × ℝ =>
      Complex.exp (Complex.I * z.1 * z.2)) := by
    fun_prop
  have hcorrelation : StronglyMeasurable (resolventCorrelation rho) := by
    rw [show resolventCorrelation rho = fun t : ℝ =>
      ∫ xi : ℝ, Complex.exp (Complex.I * t * xi) ∂rho by rfl]
    exact hphase.integral_prod_right'
  have hk : IntegrableOn (fun t : ℝ => (laguerreKernel n a t : ℂ)) (Ioi 0) :=
    laguerreKernel_integrableOn ha
  have hmass : 0 ≤ spectralMass rho := by
    simp [spectralMass]
  have hf : IntegrableOn f (Ioi 0) := by
    have hdom := hk.norm.const_mul (spectralMass rho)
    refine hdom.mono' ?_ ?_
    · exact hk.aestronglyMeasurable.mul hcorrelation.aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul]
      have hbound := norm_resolventCorrelation_le rho t
      have hknorm : 0 ≤ ‖(laguerreKernel n a t : ℂ)‖ := norm_nonneg _
      simpa [f, abs_of_nonneg hmass, mul_comm] using
        mul_le_mul_of_nonneg_left hbound hknorm
  have htwoL : 0 ≤ 2 * L := by positivity
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hf htwoL
  rw [intervalIntegral.integral_of_le htwoL] at hsplit
  have htomography := laguerre_moment_tomography_kernel rho hEven hn ha
  have hdiff : cayleyMoment rho n a - windowMoment rho n a L =
      -(∫ t : ℝ in Ioi (2 * L), f t) := by
    rw [htomography, windowMoment]
    change (spectralMass rho : ℂ) - (∫ t : ℝ in Ioi 0, f t) -
        ((spectralMass rho : ℂ) - ∫ t : ℝ in Ioc 0 (2 * L), f t) = _
    rw [← hsplit]
    ring
  rw [hdiff, norm_neg]
  have hkTail : IntegrableOn (fun t : ℝ => |laguerreKernel n a t|) (Ioi (2 * L)) := by
    have hsubset : Ioi (2 * L) ⊆ Ioi 0 := fun _t ht => lt_of_le_of_lt htwoL ht
    simpa using IntegrableOn.mono_set hk.norm hsubset
  have hdom : IntegrableOn
      (fun t : ℝ => spectralMass rho * |laguerreKernel n a t|) (Ioi (2 * L)) :=
    hkTail.const_mul (spectralMass rho)
  calc
    ‖∫ t : ℝ in Ioi (2 * L), f t‖ ≤
        ∫ t : ℝ in Ioi (2 * L), spectralMass rho * |laguerreKernel n a t| := by
      apply norm_integral_le_of_norm_le hdom
      filter_upwards with t
      rw [norm_mul]
      have hbound := norm_resolventCorrelation_le rho t
      simpa [f, mul_comm] using
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = spectralMass rho * laguerreTail n a L := by
      rw [MeasureTheory.integral_const_mul]
      rfl

/-- A continuous local particular solution makes every finite-window moment affine in its budget. -/
theorem moment_affine_budget_law
    {n : ℕ} {a : ℝ} (ha : 0 < a) {L : ℝ} (H0 : ℝ → ℝ)
    (hH0 : ContinuousOn H0 (Icc 0 (2 * L))) (R : ℝ) :
    let A : ℝ := -∫ t : ℝ in Ioc 0 (2 * L), laguerreKernel n a t * H0 t
    let B : ℝ := 1 - ∫ t : ℝ in Ioc 0 (2 * L),
      laguerreKernel n a t * Real.cosh (a * t)
    budgetWindowMoment n a L H0 R = A + B * R := by
  have hkComplex : IntegrableOn
      (fun t : ℝ => (laguerreKernel n a t : ℂ)) (Ioi 0) :=
    laguerreKernel_integrableOn ha
  have hkIoi : IntegrableOn (fun t : ℝ => laguerreKernel n a t) (Ioi 0) := by
    change Integrable (fun t : ℝ => laguerreKernel n a t) (volume.restrict (Ioi 0))
    change Integrable (fun t : ℝ => (laguerreKernel n a t : ℂ))
      (volume.restrict (Ioi 0)) at hkComplex
    refine hkComplex.mono ?_ ?_
    · exact Complex.continuous_re.comp_aestronglyMeasurable hkComplex.aestronglyMeasurable
    · filter_upwards with t
      simp
  have hk : IntegrableOn
      (fun t : ℝ => laguerreKernel n a t) (Ioc 0 (2 * L)) :=
    IntegrableOn.mono_set hkIoi Ioc_subset_Ioi_self
  have hparticular : IntegrableOn
      (fun t : ℝ => laguerreKernel n a t * H0 t) (Ioc 0 (2 * L)) :=
    hk.mul_continuousOn_of_subset hH0 measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hcoshContinuous : ContinuousOn
      (fun t : ℝ => Real.cosh (a * t)) (Icc 0 (2 * L)) := by
    fun_prop
  have hcosh : IntegrableOn
      (fun t : ℝ => laguerreKernel n a t * Real.cosh (a * t)) (Ioc 0 (2 * L)) :=
    hk.mul_continuousOn_of_subset hcoshContinuous measurableSet_Ioc isCompact_Icc
      Ioc_subset_Icc_self
  dsimp only
  rw [budgetWindowMoment]
  rw [show (fun t : ℝ =>
      laguerreKernel n a t * (H0 t + R * Real.cosh (a * t))) =
      fun t : ℝ => laguerreKernel n a t * H0 t +
        R * (laguerreKernel n a t * Real.cosh (a * t)) by
    funext t
    ring]
  rw [integral_add hparticular (hcosh.const_mul R)]
  rw [MeasureTheory.integral_const_mul]
  ring

end D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

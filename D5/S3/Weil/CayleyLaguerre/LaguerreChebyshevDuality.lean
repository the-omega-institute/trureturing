/- GID: D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality
   generality: I
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Laguerre time tomography equals the Chebyshev derivative jet. -/

import D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/- Library-search audit trail (2026-08-30):
   * Body-shape searches found the established resolvent `withDensity`, finite
     Laguerre sum, and correlation constructions. The public theorem exposes
     those constructions as local terms instead of declaring sibling owners.
   * The time-axis identity is proved here from finite sums, complex Laplace
     moments, and product integration. `CayleyMomentTransport` supplies the
     stable scale-axis constituent. No frozen theorem states their common
     public equality.
   * Pinned Mathlib has no Laguerre--Chebyshev duality theorem. It supplies
     the integration and Gamma facts used in the direct time-axis proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport

namespace D5.S3.Weil.CayleyLaguerre.LaguerreChebyshevDuality

private lemma integrableOn_complex_laplace_moment
    {a : Complex} (ha : a.re < 0) (n : Nat) :
    IntegrableOn (fun x : Real => (x : Complex) ^ n * Complex.exp (a * x)) (Ioi 0) := by
  let r := -a.re
  have hr : 0 < r := neg_pos.mpr ha
  have hgamma : IntegrableOn
      (fun x : Real => Real.exp (-x) * x ^ n) (Ioi 0) := by
    simpa [Real.rpow_natCast] using
      (Real.GammaIntegral_convergent (s := (n + 1 : Nat)) (by positivity))
  have hscaled :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun x : Real => Real.exp (-x) * x ^ n) 0 hr).mpr (by
        simpa only [mul_zero] using hgamma)
  have hmodel : IntegrableOn
      (fun x : Real => Real.exp (-(r * x)) * x ^ n) (Ioi 0) := by
    apply (hscaled.const_mul (r ^ n)⁻¹).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x _hx
    rw [mul_pow]
    field_simp [hr.ne']
  refine hmodel.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable
    · fun_prop
    · exact measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [mem_Ioi] at hx
    simp only [norm_mul, norm_pow, Complex.norm_real,
      Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [show a.re * x = -(r * x) by simp [r]]
    rw [Real.norm_eq_abs, abs_of_pos hx, mul_comm]

private lemma integral_complex_laplace_moment
    {a : Complex} (ha : a.re < 0) (n : Nat) :
    (integral (volume.restrict (Ioi 0))
      (fun x : Real => (x : Complex) ^ n * Complex.exp (a * x))) =
      (-1 : Complex) ^ (n + 1) * n.factorial / a ^ (n + 1) := by
  induction n with
  | zero => simpa using integral_exp_mul_complex_Ioi ha 0
  | succ n ih =>
      have ha0 : a ≠ 0 := fun h => by simp [h] at ha
      let f : Real -> Complex := fun x => (x : Complex) ^ (n + 1)
      let f' : Real -> Complex := fun x => (n + 1 : Nat) * (x : Complex) ^ n
      let g : Real -> Complex := fun x => Complex.exp (a * x) / a
      let g' : Real -> Complex := fun x => Complex.exp (a * x)
      have hf : ∀ x ∈ Ioi (0 : Real), HasDerivAt f (f' x) x := by
        intro x _hx
        simpa [f, f'] using
          (Complex.ofRealCLM.hasFDerivAt.pow (n + 1)).hasDerivAt
      have hg : ∀ x ∈ Ioi (0 : Real), HasDerivAt g (g' x) x := by
        intro x _hx
        change HasDerivAt (fun y : Real => Complex.exp (a * y) / a)
          (Complex.exp (a * x)) x
        have hcomplex := (Complex.hasDerivAt_exp (a * (x : Complex))).comp
          (x : Complex) ((hasDerivAt_id (x : Complex)).const_mul a)
        have hreal := hcomplex.comp_ofReal
        simpa [div_eq_mul_inv, mul_assoc, ha0] using hreal.mul_const a⁻¹
      have hfg' : IntegrableOn (f * g') (Ioi (0 : Real)) := by
        change IntegrableOn
          (fun x : Real => (x : Complex) ^ (n + 1) * Complex.exp (a * x)) (Ioi 0)
        exact integrableOn_complex_laplace_moment ha (n + 1)
      have hf'g : IntegrableOn (f' * g) (Ioi (0 : Real)) := by
        have hbase := (integrableOn_complex_laplace_moment ha n).const_mul
          ((n + 1 : Nat) / a)
        apply hbase.congr
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x _hx
        simp only [f', g, Pi.mul_apply]
        field_simp [ha0]
      have hzero : Tendsto (f * g) (nhdsWithin (0 : Real) (Ioi 0)) (nhds 0) := by
        have hcont : ContinuousAt (f * g) 0 := by
          dsimp [f, g]
          fun_prop
        rw [show (0 : Complex) = (f * g) 0 by simp [f, g, Pi.mul_apply]]
        exact hcont.tendsto.mono_left inf_le_left
      have hinfty : Tendsto (f * g) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        let r := -a.re
        have hr : 0 < r := neg_pos.mpr ha
        have hmodel :=
          (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
            (n + 1 : Real) r hr).div_const ‖a‖
        simp only [zero_div] at hmodel
        refine hmodel.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
        simp only [f, g, Pi.mul_apply, norm_mul, norm_pow, Complex.norm_real,
          Complex.norm_div, Complex.norm_exp, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        rw [Real.norm_eq_abs, abs_of_pos hx,
          show (n : Real) + 1 = ((n + 1 : Nat) : Real) by norm_num,
          Real.rpow_natCast, show a.re * x = -(r * x) by simp [r]]
        ring_nf
      have hip := integral_Ioi_mul_deriv_eq_deriv_mul
        hf hg hfg' hf'g hzero hinfty
      simp only [f, f', g, g'] at hip
      have hint :
          (integral (volume.restrict (Ioi 0)) (fun x : Real =>
            (n + 1 : Nat) * (x : Complex) ^ n * (Complex.exp (a * x) / a))) =
            ((n + 1 : Nat) / a) *
              integral (volume.restrict (Ioi 0))
                (fun x : Real => (x : Complex) ^ n * Complex.exp (a * x)) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        field_simp [ha0]
      rw [hint, ih] at hip
      field_simp [ha0] at hip ⊢
      ring_nf at hip ⊢
      simpa [Nat.factorial_succ, Nat.cast_add, Nat.cast_one,
        add_comm, mul_comm] using hip

private lemma binomial_tail (n : Nat) (s : Complex) :
    (Finset.sum (Finset.range n) (fun j =>
      (-1 : Complex) ^ (j + 1) * Nat.choose n (j + 1) / s ^ (j + 1))) =
      (1 - 1 / s) ^ n - 1 := by
  rw [show (1 - 1 / s : Complex) = -1 / s + 1 by ring,
    (Commute.all (-1 / s) 1).add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [div_pow]
  ring

private lemma half_scale_laguerre_identity
    {n : Nat} (gamma : Real) :
    (((gamma : Complex) + Complex.I / 2) /
        ((gamma : Complex) - Complex.I / 2)) ^ n =
      1 - integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((Real.exp (-t / 2) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * t ^ j) : Real) :
            Complex) * Complex.exp (-Complex.I * gamma * t)) := by
  let s : Complex := 1 / 2 + Complex.I * gamma
  have hsre : (-s).re < 0 := by simp [s]
  have hnegative :
      (∫ t : Real in Ioi 0,
        ((-(Real.exp (-t / 2) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * t ^ j) : Real) :
            Complex) * Complex.exp (-Complex.I * gamma * t))) =
        (((gamma : Complex) + Complex.I / 2) /
          ((gamma : Complex) - Complex.I / 2)) ^ n - 1 := by
    push_cast
    simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
    rw [MeasureTheory.integral_finsetSum]
    · calc
        _ = Finset.sum (Finset.range n) (fun j =>
            ((-1 : Complex) ^ (j + 1) * Nat.choose n (j + 1) / j.factorial) *
              integral (volume.restrict (Ioi 0)) (fun t : Real =>
                (t : Complex) ^ j * Complex.exp (-s * t))) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [← MeasureTheory.integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _ht
          dsimp only
          rw [show Complex.exp (-s * t) =
              Complex.exp ((t : Complex) * (-1 / 2)) *
                Complex.exp (-((t : Complex) * Complex.I * gamma)) by
            rw [← Complex.exp_add]
            congr 1
            simp [s]
            ring]
          rw [pow_succ]
          ring
        _ = (((gamma : Complex) + Complex.I / 2) /
            ((gamma : Complex) - Complex.I / 2)) ^ n - 1 := by
          simp_rw [integral_complex_laplace_moment hsre]
          have hleft : ((gamma : Complex) - Complex.I / 2) ≠ 0 := by
            intro hz
            have him := congrArg Complex.im hz
            norm_num at him
          have hright : (1 / 2 : Complex) + Complex.I * gamma ≠ 0 := by
            intro hz
            have hre := congrArg Complex.re hz
            norm_num at hre
          rw [show ((gamma : Complex) + Complex.I / 2) /
              ((gamma : Complex) - Complex.I / 2) = 1 - 1 / s by
            dsimp only [s]
            rw [show 1 - 1 / ((1 / 2 : Complex) + Complex.I * gamma) =
                (((1 / 2 : Complex) + Complex.I * gamma) - 1) /
                  ((1 / 2 : Complex) + Complex.I * gamma) by
              apply (eq_div_iff hright).2
              rw [sub_mul, one_mul, div_mul_cancel₀ 1 hright]]
            apply (div_eq_div_iff hleft hright).2
            ring_nf
            simp [pow_two, Complex.I_mul_I]]
          rw [← binomial_tail n s]
          apply Finset.sum_congr rfl
          intro j _hj
          field_simp
          have hfac : (j.factorial : Complex) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero j
          have hs0 : s ≠ 0 := by
            intro hs
            have hre := congrArg Complex.re hs
            simp [s] at hre
          rw [neg_pow]
          field_simp [hfac, hs0]
          rw [neg_pow]
          simp only [one_pow, mul_one]
          ring
    · intro j _hj
      convert (integrableOn_complex_laplace_moment hsre j).const_mul
        (-((-1 : Complex) ^ j * Nat.choose n (j + 1) / j.factorial)) using 1
      ext t
      rw [show Complex.exp (-s * t) =
          (Real.exp (-t / 2) : Complex) * Complex.exp (-Complex.I * gamma * t) by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        simp [s]
        ring]
      push_cast
      ring
  have hpositive :
      integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((-(Real.exp (-t / 2) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * t ^ j) : Real) :
            Complex) * Complex.exp (-Complex.I * gamma * t))) =
        -integral (volume.restrict (Ioi 0)) (fun t : Real =>
          ((Real.exp (-t / 2) *
            Finset.sum (Finset.range n) (fun j =>
              (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * t ^ j) : Real) :
              Complex) * Complex.exp (-Complex.I * gamma * t)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    push_cast
    ring
  calc
    (((gamma : Complex) + Complex.I / 2) /
        ((gamma : Complex) - Complex.I / 2)) ^ n =
        ((((gamma : Complex) + Complex.I / 2) /
          ((gamma : Complex) - Complex.I / 2)) ^ n - 1) + 1 := by ring
    _ = integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((-(Real.exp (-t / 2) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * t ^ j) : Real) :
            Complex) * Complex.exp (-Complex.I * gamma * t))) + 1 := by rw [hnegative]
    _ = 1 - integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((Real.exp (-t / 2) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * t ^ j) : Real) :
            Complex) * Complex.exp (-Complex.I * gamma * t)) := by rw [hpositive]; ring

private lemma scaled_laguerre_identity
    {n : Nat} {a : Real} (ha : 0 < a) (xi : Real) :
    (((xi : Complex) + Complex.I * a) /
        ((xi : Complex) - Complex.I * a)) ^ n =
      1 - integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((2 * a * Real.exp (-a * t) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
              (2 * a * t) ^ j) : Real) : Complex) *
            Complex.exp (-Complex.I * xi * t)) := by
  let b : Real := 2 * a
  let gamma : Real := xi / b
  let g : Real -> Complex := fun u =>
    ((Real.exp (-u / 2) *
      Finset.sum (Finset.range n) (fun j =>
        (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial * u ^ j) : Real) :
      Complex) * Complex.exp (-Complex.I * gamma * u)
  have hb : 0 < b := by dsimp [b]; positivity
  have hscale := integral_comp_mul_left_Ioi g 0 hb
  have hkernel :
      (fun t : Real =>
        ((2 * a * Real.exp (-a * t) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
              (2 * a * t) ^ j) : Real) : Complex) *
            Complex.exp (-Complex.I * xi * t)) =ᶠ[ae (volume.restrict (Ioi 0))]
      fun t => (b : Complex) * g (b * t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _ht
    simp only [g, b, gamma]
    rw [show -a * t = -(2 * a * t) / 2 by ring]
    rw [show (-Complex.I * (xi : Complex) * t) =
        -Complex.I * (xi / (2 * a) : Real) * (2 * a * t) by
      push_cast
      field_simp [ha.ne']]
    push_cast
    ring
  have hintegral :
      integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((2 * a * Real.exp (-a * t) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
              (2 * a * t) ^ j) : Real) : Complex) *
            Complex.exp (-Complex.I * xi * t)) =
        integral (volume.restrict (Ioi 0)) g := by
    rw [integral_congr_ae hkernel]
    calc
      integral (volume.restrict (Ioi 0)) (fun t : Real =>
          (b : Complex) * g (b * t)) =
          (b : Complex) * integral (volume.restrict (Ioi 0)) (fun t : Real =>
            g (b * t)) := by
        exact MeasureTheory.integral_const_mul (μ := volume.restrict (Ioi 0))
          (b : Complex) (fun t : Real => g (b * t))
      _ = (b : Complex) * ((b⁻¹ : Real) • integral (volume.restrict (Ioi 0)) g) := by
        rw [hscale]
        simp only [mul_zero]
      _ = integral (volume.restrict (Ioi 0)) g := by
        rw [Complex.real_smul]
        push_cast
        field_simp [hb.ne']
  have hbase := half_scale_laguerre_identity (n := n) gamma
  have hcayley :
      ((xi : Complex) + Complex.I * a) / ((xi : Complex) - Complex.I * a) =
        ((gamma : Complex) + Complex.I / 2) /
          ((gamma : Complex) - Complex.I / 2) := by
    simp only [gamma, b]
    have hleft : ((xi : Complex) - Complex.I * a) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hright : ((xi / (2 * a) : Real) : Complex) - Complex.I / 2 ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      have him := congrArg Complex.im h
      norm_num [Complex.div_im, Complex.normSq_apply] at him
    rw [div_eq_div_iff hleft hright]
    push_cast
    field_simp [ha.ne']
  rw [hintegral, hcayley]
  exact hbase

private lemma laguerre_moment_tomography
    (rho : Measure Real) [IsFiniteMeasure rho]
    (hEven : Measure.map (fun xi : Real => -xi) rho = rho)
    {n : Nat} {a : Real} (ha : 0 < a) :
    integral rho (fun xi : Real =>
        (((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a)) ^ n) =
      (rho.real Set.univ : Complex) - (2 * a : Real) *
        integral (volume.restrict (Ioi 0)) (fun t : Real =>
          ((Real.exp (-a * t) *
            Finset.sum (Finset.range n) (fun j =>
              (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
                (2 * a * t) ^ j) : Real) : Complex) *
            integral rho (fun xi : Real => Complex.exp (Complex.I * t * xi))) := by
  have hk : IntegrableOn (fun t : Real =>
      ((2 * a * Real.exp (-a * t) *
        Finset.sum (Finset.range n) (fun j =>
          (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
            (2 * a * t) ^ j) : Real) : Complex)) (Ioi 0) := by
    push_cast
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro j _hj
    have hbase :=
      (integrableOn_complex_laplace_moment (a := (-a : Complex))
        (by simpa using ha) j).const_mul
        (((2 * a : Real) : Complex) *
          (((-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial : Real) : Complex) *
          ((2 * a : Real) : Complex) ^ j)
    apply hbase.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _ht
    rw [show Complex.exp ((-a : Complex) * t) = (Real.exp (-a * t) : Complex) by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      rfl]
    push_cast
    ring
  have hone : Integrable (fun _ : Real => (1 : Complex)) rho := integrable_const 1
  have hmodel := hk.mul_prod hone
  have hphase : StronglyMeasurable (fun z : Real × Real =>
      Complex.exp (-(Complex.I * z.2 * z.1))) := by
    fun_prop
  have hF : Integrable (Function.uncurry (fun t : Real => fun xi : Real =>
      ((2 * a * Real.exp (-a * t) *
        Finset.sum (Finset.range n) (fun j =>
          (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
            (2 * a * t) ^ j) : Real) : Complex) *
        Complex.exp (-(Complex.I * xi * t))))
      ((volume.restrict (Ioi 0)).prod rho) := by
    change Integrable (fun z : Real × Real =>
      ((2 * a * Real.exp (-a * z.1) *
        Finset.sum (Finset.range n) (fun j =>
          (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
            (2 * a * z.1) ^ j) : Real) : Complex) *
        Complex.exp (-(Complex.I * z.2 * z.1)))
      ((volume.restrict (Ioi 0)).prod rho)
    refine hmodel.norm.mono' ?_ ?_
    · exact (hmodel.aestronglyMeasurable.mul hphase.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun z => by simp)
    · filter_upwards with z
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(Complex.I * (z.2 : Complex) * (z.1 : Complex))).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero]
      simp
  have hinner : Integrable (fun xi : Real =>
      integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((2 * a * Real.exp (-a * t) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
              (2 * a * t) ^ j) : Real) : Complex) *
          Complex.exp (-(Complex.I * xi * t)))) rho := by
    simpa using hF.integral_prod_right
  have hpoint :
      (fun xi : Real =>
        (((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a)) ^ n) =ᵐ[rho]
      fun xi : Real => 1 - integral (volume.restrict (Ioi 0)) (fun t : Real =>
        ((2 * a * Real.exp (-a * t) *
          Finset.sum (Finset.range n) (fun j =>
            (-1 : Real) ^ j * Nat.choose n (j + 1) / j.factorial *
              (2 * a * t) ^ j) : Real) : Complex) *
            Complex.exp (-(Complex.I * xi * t))) := by
    filter_upwards with xi
    simpa only [neg_mul] using scaled_laguerre_identity (n := n) ha xi
  rw [integral_congr_ae hpoint]
  rw [integral_sub (integrable_const 1) hinner]
  rw [show integral rho (fun _xi : Real => (1 : Complex)) =
      (rho.real Set.univ : Complex) by simp]
  rw [← integral_integral_swap hF]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [MeasureTheory.integral_const_mul]
  have hmap := MeasureTheory.integral_map (μ := rho) (φ := fun xi : Real => -xi)
    (f := fun xi : Real => Complex.exp (Complex.I * t * xi)) (by fun_prop) (by fun_prop)
  rw [hEven] at hmap
  have hnegative :
      integral rho (fun xi : Real => Complex.exp (-Complex.I * t * xi)) =
        integral rho (fun xi : Real => Complex.exp (Complex.I * t * xi)) := by
    calc
      integral rho (fun xi : Real => Complex.exp (-Complex.I * t * xi)) =
          integral rho (fun xi : Real =>
            Complex.exp (Complex.I * t * ((-xi : Real) : Complex))) := by
        apply integral_congr_ae
        filter_upwards with xi
        congr 1
        push_cast
        ring
      _ = integral rho (fun xi : Real => Complex.exp (Complex.I * t * xi)) := hmap.symm
  rw [show (fun xi : Real => Complex.exp (-(Complex.I * xi * t))) =
      fun xi : Real => Complex.exp (-Complex.I * t * xi) by
    funext xi
    congr 1
    ring]
  rw [hnegative]
  push_cast
  ring

/-- The Laguerre observation of an even resolvent correlation is the same
Cayley moment as the derivative jet of its Stieltjes budget curve. -/
theorem laguerre_chebyshev_duality
    (nu : Measure Real) (n : Nat) (u : Real)
    (p : Fin (n + 1) -> Real)
    (hEven : Measure.map (fun xi : Real => -xi) nu = nu)
    (hn : 1 <= n) (uPositive : 0 < u)
    (coefficientExpansion : forall x : Real,
      (Polynomial.Chebyshev.T Real (n : Int)).eval (1 - 2 * x) =
        Finset.univ.sum (fun k => p k * x ^ (k : Nat)))
    (budgetIntegrable :
      Integrable (fun xi : Real => 1 / (xi ^ 2 + u)) nu) :
    let scale := Real.sqrt u
    let laguerreOne : Nat -> Real -> Real := fun m x =>
      Finset.sum (Finset.range (m + 1)) (fun j =>
        (-1 : Real) ^ j * Nat.choose (m + 1) (j + 1) / j.factorial * x ^ j)
    let weighted := nu.withDensity (fun xi : Real =>
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹))
    let correlation : Real -> Complex := fun t =>
      integral weighted (fun xi : Real => Complex.exp (Complex.I * t * xi))
    let budget : Real -> Real := fun v =>
      integral nu (fun xi : Real => 1 / (xi ^ 2 + v))
    (budget u : Complex) - (2 * scale : Real) *
        integral (volume.restrict (Ioi 0)) (fun t : Real =>
          ((Real.exp (-scale * t) *
            laguerreOne (n - 1) (2 * scale * t) : Real) : Complex) *
            correlation t) =
      Complex.ofReal (Finset.univ.sum (fun k : Fin (n + 1) =>
        p k * u ^ (k : Nat) *
          ((-1 : Real) ^ (k : Nat) / ((k : Nat).factorial : Real)) *
            iteratedDeriv (k : Nat) budget u)) := by
  dsimp only
  let scale : Real := Real.sqrt u
  let weighted : Measure Real := nu.withDensity (fun xi : Real =>
    ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹))
  have scalePositive : 0 < scale := Real.sqrt_pos.2 uPositive
  have scaleSquare : scale ^ 2 = u := by
    exact Real.sq_sqrt uPositive.le
  have weightedIntegrable :
      Integrable (fun xi : Real => (xi ^ 2 + scale ^ 2)⁻¹) nu := by
    simpa only [one_div, scaleSquare] using budgetIntegrable
  letI : IsFiniteMeasure weighted := by
    dsimp only [weighted]
    exact isFiniteMeasure_withDensity_ofReal weightedIntegrable.hasFiniteIntegral
  have mapWithDensityEq
      (mu : Measure Real) (f : Real -> Real) (g : Real -> ENNReal)
      (hf : Measurable f) (hg : Measurable g) :
      (Measure.map f mu).withDensity g =
        Measure.map f (mu.withDensity (g ∘ f)) := by
    ext s hs
    rw [withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hg hf]
    rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs)]
    rfl
  have weightedEven : Measure.map (fun xi : Real => -xi) weighted = weighted := by
    let density : Real -> ENNReal := fun xi =>
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)
    have densityMeasurable : Measurable density := by
      dsimp only [density]
      fun_prop
    have densityNeg : density ∘ (fun xi : Real => -xi) = density := by
      funext xi
      simp only [density, Function.comp_apply, neg_sq]
    have mappedDensity := mapWithDensityEq nu (fun xi : Real => -xi) density
      measurable_neg densityMeasurable
    dsimp only [weighted]
    change Measure.map (fun xi : Real => -xi) (nu.withDensity density) =
      nu.withDensity density
    calc
      Measure.map (fun xi : Real => -xi) (nu.withDensity density) =
          (Measure.map (fun xi : Real => -xi) nu).withDensity density := by
        simpa only [densityNeg] using mappedDensity.symm
      _ = nu.withDensity density := by rw [hEven]
  have densityMeasurable : Measurable fun xi : Real =>
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹) := by
    fun_prop
  have densityFinite : forall xi : Real,
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹) < (⊤ : ENNReal) := by
    intro xi
    exact ENNReal.ofReal_lt_top
  have massIdentity : weighted.real Set.univ =
      integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) := by
    calc
      weighted.real Set.univ = integral weighted (fun _xi : Real => (1 : Real)) := by
        simp only [integral_const, Measure.real, smul_eq_mul, mul_one]
      _ = integral nu (fun xi : Real =>
          (ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)).toReal • (1 : Real)) := by
        dsimp only [weighted]
        exact integral_withDensity_eq_integral_toReal_smul densityMeasurable
          (Filter.Eventually.of_forall densityFinite) _
      _ = integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) := by
        apply integral_congr_ae
        filter_upwards with xi
        rw [ENNReal.toReal_ofReal (by positivity)]
        simp only [smul_eq_mul, mul_one, one_div, scaleSquare]
  have momentIdentity : integral weighted (fun xi : Real =>
      (((xi : Complex) + Complex.I * scale) /
        ((xi : Complex) - Complex.I * scale)) ^ n) =
      integral nu (fun xi : Real =>
        (((xi : Complex) + Complex.I * scale) /
          ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) := by
    dsimp only [weighted]
    rw [integral_withDensity_eq_integral_toReal_smul densityMeasurable
      (Filter.Eventually.of_forall densityFinite)]
    apply integral_congr_ae
    filter_upwards with xi
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [Complex.real_smul, scaleSquare]
    push_cast
    ring
  have timeTomography :=
    laguerre_moment_tomography (n := n) weighted weightedEven scalePositive
  have scaleTomography := chebyshev_stieltjes_jet nu n u p hEven uPositive
    coefficientExpansion budgetIntegrable
  change integral nu (fun xi : Real =>
      (((xi : Complex) + Complex.I * scale) /
        ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) = _
    at scaleTomography
  calc
    ((integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) : Real) : Complex) -
        (2 * scale : Real) * integral (volume.restrict (Ioi 0))
          (fun t : Real =>
            ((Real.exp (-scale * t) *
              Finset.sum (Finset.range (n - 1 + 1)) (fun j =>
                (-1 : Real) ^ j * Nat.choose (n - 1 + 1) (j + 1) /
                  j.factorial * (2 * scale * t) ^ j) : Real) : Complex) *
              integral weighted (fun xi : Real =>
                Complex.exp (Complex.I * t * xi))) =
        integral weighted (fun xi : Real =>
          (((xi : Complex) + Complex.I * scale) /
            ((xi : Complex) - Complex.I * scale)) ^ n) := by
      simpa only [Nat.sub_add_cancel hn, massIdentity] using timeTomography.symm
    _ = integral nu (fun xi : Real =>
        (((xi : Complex) + Complex.I * scale) /
          ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) :=
      momentIdentity
    _ = Complex.ofReal (Finset.univ.sum (fun k : Fin (n + 1) =>
        p k * u ^ (k : Nat) *
          ((-1 : Real) ^ (k : Nat) / ((k : Nat).factorial : Real)) *
            iteratedDeriv (k : Nat)
              (fun v : Real => integral nu
                (fun xi : Real => 1 / (xi ^ 2 + v))) u)) := scaleTomography

#print axioms laguerre_chebyshev_duality

end D5.S3.Weil.CayleyLaguerre.LaguerreChebyshevDuality

/- GID: D5/S3/Analytic/GauntBesselTail/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/GauntBesselTail/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: none
   digest: Squared-order convexity supplies the kernel comparison for Gaunt's Bessel tail bound. -/

/-
The utility classification is none: the statements concern arbitrary real
parameters and analytic integrals, rather than finite computations or instances.
The intended settlement is open-problem-resolution (#22457; Proved).
No settlement theorem is asserted by the definitions alone.
-/

import D5.S3.Analytic.GammaGammaNBU.Result
import D5.S3.Zeros.Jensen.FactorialJensenKernelBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Set MeasureTheory Filter
open scoped Topology Asymptotics
noncomputable section
namespace D5.S3.Analytic.GauntBesselTail.Result
open D5.S3.Analytic.GammaGammaNBU.Result (besselK)

def alpha (ν n : ℝ) : ℝ := ν+n-sqrt ((ν+n)^2-2*ν-1)
def alphaPrime (ν n : ℝ) : ℝ := ν+n+sqrt ((ν+n)^2-2*ν-1)
def tail (ν p x : ℝ) : ℝ := ∫ t in Ioi x, t^(-ν) * besselK p t

def claim : Prop :=
  (∀ n ν : ℝ, n < 1 → 1-n+sqrt (2*(1-n)) ≤ ν → ∀ x : ℝ, 0 < x →
    x^(-ν) * besselK (ν+n-alpha ν n) x < tail ν (ν+n) x) ∧
  (∀ n ν : ℝ, n < 1 → 1-n+sqrt (2*(1-n)) ≤ ν → ∀ β : ℝ,
    β ∉ ({alpha ν n, alphaPrime ν n} : Set ℝ) →
    (∀ x : ℝ, 0 < x → x^(-ν) * besselK (ν+n-β) x <
      x^(-ν) * besselK (ν+n-alpha ν n) x) ∨
    (∃ y : ℝ, 0 < y ∧ tail ν (ν+n) y < y^(-ν) * besselK (ν+n-β) y)) ∧
  (∀ ν x : ℝ, 0 < x → tail ν (ν+1) x = x^(-ν) * besselK ν x)

private lemma sinh_gap_pos {v : ℝ} (hv : 0 < v) :
    0 < v * cosh v - sinh v := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y * cosh y - sinh y)
      (x * sinh x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x) using 1 <;> first | rfl | (try dsimp; ring)
  have hm : StrictMonoOn (fun y : ℝ => y * cosh y - sinh y) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    exact mul_pos hx (sinh_pos_iff.mpr hx)
  simpa using hm (show 0 ∈ Ici (0 : ℝ) by simp) hv.le hv

private lemma cosh_sqrt_deriv (u s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => cosh (u * sqrt s))
      (u / (2 * sqrt s) * sinh (u * sqrt s)) s := by
  convert (hasDerivAt_cosh (u * sqrt s)).comp s
    ((hasDerivAt_sqrt hs.ne').const_mul u) using 1
  · rfl
  · ring

private lemma cosh_sqrt_deriv2 (u s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => u / (2 * sqrt s) * sinh (u * sqrt s))
      (u / (4 * (sqrt s)^3) * (u * sqrt s * cosh (u * sqrt s) - sinh (u * sqrt s))) s := by
  have hn := (sqrt_pos_of_pos hs).ne'
  convert ((hasDerivAt_const s u).div ((hasDerivAt_sqrt hs.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hn)).mul
    ((hasDerivAt_sinh (u * sqrt s)).comp s ((hasDerivAt_sqrt hs.ne').const_mul u)) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma squared_order_strictConvex {u : ℝ} (hu : 0 < u) :
    StrictConvexOn ℝ (Ici 0) (fun s : ℝ => cosh (u * sqrt s)) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) (by fun_prop)
  intro s hs
  rw [interior_Ici] at hs
  have he : deriv (fun s : ℝ => cosh (u * sqrt s)) =ᶠ[𝓝 s]
      (fun s => u / (2 * sqrt s) * sinh (u * sqrt s)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (cosh_sqrt_deriv u t ht).deriv
  rw [Function.iterate_succ_apply', Function.iterate_one, he.deriv_eq]
  rw [(cosh_sqrt_deriv2 u s hs).deriv]
  have hsqrt := sqrt_pos_of_pos hs
  exact mul_pos (div_pos hu (by positivity))
    (sinh_gap_pos (mul_pos hu (sqrt_pos_of_pos hs)))

private lemma cosh_sqrt_sq (u a : ℝ) (hu : 0 ≤ u) :
    cosh (u * sqrt (a^2)) = cosh (a*u) := by
  calc
    _ = cosh |u*a| := by rw [sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hu]
    _ = _ := by rw [cosh_abs, mul_comm]

private lemma positive_order_kernel {u p q ν : ℝ} (hu : 0 < u)
    (hq : 0 < q) (hν : q < ν) (he : p^2 = q^2 + 2*ν + 1) :
    cosh (q*u) * cosh u + ν/q * sinh (q*u) * sinh u < cosh (p*u) := by
  have hab : (q-1)^2 < (q+1)^2 := by nlinarith
  have hbc : (q+1)^2 < p^2 := by nlinarith
  have hc := (squared_order_strictConvex hu).slope_strict_mono_adjacent
    (sq_nonneg (q-1)) (sq_nonneg p) hab hbc
  rw [cosh_sqrt_sq u (q+1) hu.le, cosh_sqrt_sq u (q-1) hu.le,
    cosh_sqrt_sq u p hu.le] at hc
  rw [add_mul, sub_mul, one_mul, cosh_add, cosh_sub] at hc
  have hc' := (div_lt_div_iff₀ (sub_pos.mpr hab) (sub_pos.mpr hbc)).mp hc
  rw [he] at hc'
  ring_nf at hc'
  apply (mul_lt_mul_iff_right₀ hq).mp
  field_simp
  nlinarith [hc']

private lemma zero_order_kernel {u p ν : ℝ} (hu : 0 < u) (hν : 0 < ν)
    (he : p^2 = 2*ν+1) :
    cosh u + ν*u*sinh u < cosh (p*u) := by
  have hc := (squared_order_strictConvex hu).lt_slope_of_hasDerivAt
    (show (1 : ℝ) ∈ Ici 0 by norm_num) (sq_nonneg p)
    (show 1 < p^2 by linarith) (cosh_sqrt_deriv u 1 (by norm_num))
  simp only [sqrt_one, mul_one, slope_def_field] at hc
  rw [cosh_sqrt_sq u p hu.le] at hc
  have hc' := (lt_div_iff₀ (show 0 < p^2-1 by linarith)).mp hc
  rw [he] at hc'
  ring_nf at hc' ⊢
  linarith

private lemma parameters {ν n : ℝ} (hn : n < 1)
    (hν : 1-n+sqrt (2*(1-n)) ≤ ν) :
    0 ≤ (ν+n)^2-2*ν-1 ∧
    sqrt ((ν+n)^2-2*ν-1) < ν ∧
    sqrt ((ν+n)^2-2*ν-1)+1 < ν+n := by
  have hd : 0 < 2*(1-n) := by linarith
  have hs := sqrt_pos_of_pos hd
  have hss := sq_sqrt hd.le
  have hv : sqrt (2*(1-n)) ≤ ν+n-1 := by linarith
  have hv0 : 0 < ν+n-1 := lt_of_lt_of_le hs hv
  have hdisc : 0 ≤ (ν+n)^2-2*ν-1 := by nlinarith
  have hq := sqrt_nonneg ((ν+n)^2-2*ν-1)
  have hq2 := sq_sqrt hdisc
  have hb : sqrt ((ν+n)^2-2*ν-1) < ν+n-1 := by nlinarith
  exact ⟨hdisc, by linarith, by linarith⟩


private lemma cosh_quadratic (u : ℝ) : 1+u^2/2 ≤ cosh u := by
  have h := D5.S3.Zeros.Jensen.FactorialJensenKernelBound.even_sum_le_cosh
    2 (u^2) (sq_nonneg u)
  rw [sqrt_sq_eq_abs, cosh_abs] at h
  norm_num [D5.S3.Zeros.Jensen.FactorialJensenKernelBound.evenFactorialSum,
    Fin.sum_univ_two] at h
  exact h

private lemma exponential_kernel_integrable (z A : ℝ) (hz : 0 < z) :
    Integrable (fun u : ℝ => exp (-z*cosh u+A*u)) := by
  have hi := (integrable_cexp_quadratic (b := ((z/2 : ℝ) : ℂ))
    (by simpa using half_pos hz) (A : ℂ) 0).norm
  have hg : Integrable (fun u : ℝ => exp (-(z/2)*u^2+A*u)) := by
    convert hi using 1
    ext u
    simp [Complex.norm_exp, Complex.mul_re, pow_two]
  apply hg.mono' (by fun_prop)
  filter_upwards with u
  rw [Real.norm_of_nonneg (exp_nonneg _)]
  apply exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (cosh_quadratic u) hz.le
  nlinarith

private lemma bessel_kernel_integrable (r z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => exp (-z*cosh u)*cosh (r*u)) (Ioi 0) := by
  have hi := ((exponential_kernel_integrable z r hz).add
    (exponential_kernel_integrable z (-r) hz)).div_const 2
  apply hi.integrableOn.congr
  filter_upwards with u
  dsimp
  simp only [cosh_eq, exp_add, neg_mul]
  ring

private lemma bessel_cosh_integrable (r z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => exp (-z*cosh u)*cosh u*cosh (r*u)) (Ioi 0) := by
  have hi := ((bessel_kernel_integrable (r+1) z hz).add
    (bessel_kernel_integrable (r-1) z hz)).div_const 2
  apply hi.congr
  filter_upwards with u
  dsimp
  rw [add_mul, sub_mul, one_mul, cosh_add, cosh_sub]
  ring

private lemma bessel_hasDerivAt (r : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (besselK r)
      (-(∫ u in Ioi 0, exp (-z*cosh u)*cosh u*cosh (r*u))) z := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun z u : ℝ => exp (-z*cosh u)*cosh (r*u))
    (F' := fun z u : ℝ => -(exp (-z*cosh u)*cosh u*cosh (r*u)))
    (s := Ioi (z/2)) (bound := fun u => exp (-(z/2)*cosh u)*cosh u*cosh (r*u))
    (Ioi_mem_nhds (by linarith : z/2 < z))
    (Eventually.of_forall (fun _ => by fun_prop)) (bessel_kernel_integrable r z hz)
    (by fun_prop) ?_ (bessel_cosh_integrable r (z/2) (half_pos hz)) ?_
  · unfold besselK
    simpa only [integral_neg] using hd.2
  · filter_upwards with u
    intro t ht
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact ht.le
  · filter_upwards with u
    intro t _
    convert (((hasDerivAt_id t).neg.mul_const (cosh u)).exp).mul_const (cosh (r*u)) using 1
    · rfl
    · dsimp
      ring

private lemma integral_decay (f : ℝ → ℝ) (hf : ∀ u ∈ Ioi 0, 0 ≤ f u)
    (hi : ∀ z : ℝ, 0 < z → IntegrableOn (fun u => exp (-z*cosh u)*f u) (Ioi 0))
    {t : ℝ} (ht : 1 ≤ t) :
    |∫ u in Ioi 0, exp (-t*cosh u)*f u| ≤
      exp (-t/2)*(∫ u in Ioi 0, exp (-(1/2:ℝ)*cosh u)*f u) := by
  have hn : 0 ≤ ∫ u in Ioi 0, exp (-t*cosh u)*f u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (exp_nonneg _) (hf u hu)
  rw [abs_of_nonneg hn, ← integral_const_mul]
  apply integral_mono_ae (hi t (by linarith)) ((hi (1/2) (by norm_num)).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [← mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_right _ (hf u hu)
  apply exp_le_exp.mpr
  have hc := one_le_cosh u
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hc)]

private lemma bessel_bigO (r : ℝ) :
    (besselK r) =O[atTop] (fun t : ℝ => exp (-t/2)) := by
  apply Asymptotics.IsBigO.of_bound (besselK r (1/2))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _), besselK, mul_comm] using
    integral_decay (fun u => cosh (r*u)) (fun _ _ => (cosh_pos _).le)
      (fun z hz => bessel_kernel_integrable r z hz) ht

private lemma weighted_decay {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0))
    (hb : F =O[atTop] (fun t : ℝ => exp (-t/2))) (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t^(-ν)*F t) (Ioi x) ∧
    Tendsto (fun t => t^(-ν)*F t) atTop (𝓝 0) := by
  have h := (isLittleO_rpow_exp_pos_mul_atTop (-ν) (by norm_num : 0 < (1/4:ℝ))).mul_isBigO hb
  have ho : (fun t => t^(-ν)*F t) =o[atTop] (fun t : ℝ => exp (-(1/4:ℝ)*t)) := by
    convert h using 1
    ext t
    rw [← exp_add]
    congr 1
    ring
  have hc : ContinuousOn (fun t => t^(-ν)*F t) (Ici x) := by
    apply (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hx ht)))).mul
    exact hF.mono (fun t ht => lt_of_lt_of_le hx ht)
  refine ⟨integrable_of_isBigO_exp_neg (by norm_num : 0 < (1/4:ℝ)) hc ho.isBigO, ?_⟩
  apply ho.tendsto_zero_of_tendsto
  exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/4:ℝ) < 0))

private lemma tail_integrable (ν r : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t^(-ν)*besselK r t) (Ioi x) :=
  (weighted_decay (fun _ ht => (bessel_hasDerivAt r ht).continuousAt.continuousWithinAt)
    (bessel_bigO r) ν hx).1

private lemma weighted_bessel_tendsto (ν r : ℝ) :
    Tendsto (fun t => t^(-ν)*besselK r t) atTop (𝓝 0) :=
  (weighted_decay (fun _ ht => (bessel_hasDerivAt r ht).continuousAt.continuousWithinAt)
    (bessel_bigO r) ν (show (0:ℝ) < 1 by norm_num)).2

private lemma abs_sinh_le_cosh (u : ℝ) : |sinh u| ≤ cosh u := by
  apply abs_le.mpr
  constructor
  · simpa only [sinh_neg, cosh_neg, neg_le_neg_iff] using (sinh_lt_cosh (x := -u)).le
  · exact (sinh_lt_cosh (x := u)).le

private lemma bessel_sinh_integrable (r z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => exp (-z*cosh u)*sinh (r*u)*sinh u) (Ioi 0) := by
  apply (bessel_cosh_integrable r z hz).mono' (by fun_prop)
  filter_upwards with u
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_of_nonneg (exp_nonneg _)]
  calc
    _ ≤ exp (-z*cosh u)*cosh (r*u)*cosh u := by
      gcongr <;> apply abs_sinh_le_cosh
    _ = _ := by ring

end D5.S3.Analytic.GauntBesselTail.Result

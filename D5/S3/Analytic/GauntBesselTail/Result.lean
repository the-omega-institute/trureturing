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
  · have h := (sinh_lt_cosh (x := -u)).le
    simp only [sinh_neg, cosh_neg] at h
    linarith
  · exact (sinh_lt_cosh (x := u)).le

private lemma bessel_sinh_integrable (r z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => exp (-z*cosh u)*sinh (r*u)*sinh u) (Ioi 0) := by
  apply (bessel_cosh_integrable r z hz).mono' (by fun_prop)
  filter_upwards with u
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp (-z*cosh u)*cosh (r*u)*cosh u := by
      gcongr <;> apply abs_sinh_le_cosh
    _ = _ := by ring

private lemma exponential_kernel_tendsto (z A : ℝ) (hz : 0 < z) :
    Tendsto (fun u : ℝ => exp (-z*cosh u+A*u)) atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℝ => (z/2*u-A)*u) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-A) (tendsto_id.const_mul_atTop (half_pos hz))).atTop_mul_atTop₀ tendsto_id
  have ht : Tendsto (fun u : ℝ => exp (-(z/2)*u^2+A*u)) atTop (𝓝 0) := by
    convert tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp) using 1
    ext u
    congr 1
    dsimp
    ring
  apply squeeze_zero_norm (fun u => ?_) ht
  rw [Real.norm_of_nonneg (exp_nonneg _)]
  apply exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (cosh_quadratic u) hz.le]

private lemma u_exponential_integrable (z A : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => u*exp (-z*cosh u+A*u)) (Ioi 0) := by
  apply (exponential_kernel_integrable z (A+1) hz).integrableOn.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, Real.norm_of_nonneg hu.le, Real.norm_of_nonneg (exp_nonneg _)]
  calc
    _ ≤ exp u*exp (-z*cosh u+A*u) := by
      gcongr
      linarith [add_one_le_exp u]
    _ = _ := by rw [← exp_add]; congr 1; ring

private lemma u_exponential_tendsto (z : ℝ) (hz : 0 < z) :
    Tendsto (fun u : ℝ => u*exp (-z*cosh u)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_ge_atTop (0 : ℝ) |>.mono fun u hu => ?_)
    (exponential_kernel_tendsto z 1 hz)
  rw [norm_mul, Real.norm_of_nonneg hu, Real.norm_of_nonneg (exp_nonneg _)]
  calc
    _ ≤ exp u*exp (-z*cosh u) := by
      gcongr
      linarith [add_one_le_exp u]
    _ = _ := by rw [← exp_add]; congr 1; ring

private def S (r u : ℝ) : ℝ := if r = 0 then u else sinh (r*u)/r

private lemma S_deriv (r u : ℝ) : HasDerivAt (S r) (cosh (r*u)) u := by
  by_cases hr : r = 0
  · subst r
    simp only [zero_mul, cosh_zero]
    convert hasDerivAt_id u using 1
    ext v
    simp [S]
  · unfold S
    simp only [if_neg hr]
    convert (((hasDerivAt_id u).const_mul r).sinh).div_const r using 1
    · rfl
    · dsimp
      field_simp

private lemma S_sinh_integrable (r z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u => exp (-z*cosh u)*S r u*sinh u) (Ioi 0) := by
  by_cases hr : r = 0
  · subst r
    have hi := ((u_exponential_integrable z 1 hz).sub
      (u_exponential_integrable z (-1) hz)).div_const 2
    apply hi.congr
    filter_upwards with u
    simp only [Pi.sub_apply, S, ite_true, sinh_eq, exp_add, neg_mul]
    ring
  · apply ((bessel_sinh_integrable r z hz).div_const r).congr
    filter_upwards with u
    simp only [S, if_neg hr]
    ring

private lemma S_kernel_tendsto (r z : ℝ) (hz : 0 < z) :
    Tendsto (fun u => exp (-z*cosh u)*S r u) atTop (𝓝 0) := by
  by_cases hr : r = 0
  · subst r
    simpa [S, mul_comm] using u_exponential_tendsto z hz
  · have h := (((exponential_kernel_tendsto z r hz).sub
      (exponential_kernel_tendsto z (-r) hz)).div_const 2).div_const r
    convert h using 1
    · ext u
      simp only [Pi.sub_apply, S, if_neg hr, sinh_eq, exp_add, neg_mul]
      ring
    · simp

private lemma bessel_ibp (r : ℝ) {z : ℝ} (hz : 0 < z) :
    besselK r z = z*(∫ u in Ioi 0, exp (-z*cosh u)*S r u*sinh u) := by
  have hd (u : ℝ) : HasDerivAt (fun u => exp (-z*cosh u)*S r u)
      (exp (-z*cosh u)*cosh (r*u)-z*(exp (-z*cosh u)*S r u*sinh u)) u := by
    convert (((hasDerivAt_cosh u).const_mul (-z)).exp).mul (S_deriv r u) using 1
    <;> first | rfl | ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0:ℝ)) (fun u _ => hd u)
    ((bessel_kernel_integrable r z hz).sub ((S_sinh_integrable r z hz).const_mul z))
    (S_kernel_tendsto r z hz)
  rw [integral_sub (bessel_kernel_integrable r z hz)
    ((S_sinh_integrable r z hz).const_mul z), integral_const_mul] at h
  simpa [besselK, S] using (sub_eq_zero.mp (by simpa [S] using h))

private def H (ν p r u : ℝ) : ℝ :=
  cosh (p*u)-cosh (r*u)*cosh u-ν*S r u*sinh u

private def J (ν p r t : ℝ) : ℝ := ∫ u in Ioi 0, exp (-t*cosh u)*H ν p r u

private lemma H_integrable (ν p r : ℝ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => exp (-t*cosh u)*H ν p r u) (Ioi 0) := by
  apply ((bessel_kernel_integrable p t ht).sub
    ((bessel_cosh_integrable r t ht).add ((S_sinh_integrable r t ht).const_mul ν))).congr
  filter_upwards with u
  dsimp [H]
  ring

private lemma J_eq (ν p r : ℝ) {t : ℝ} (ht : 0 < t) :
    J ν p r t = besselK p t - (besselK (r+1) t+besselK (r-1) t)/2 - ν/t*besselK r t := by
  have hc : (∫ u in Ioi 0, exp (-t*cosh u)*cosh u*cosh (r*u)) =
      (besselK (r+1) t+besselK (r-1) t)/2 := by
    unfold besselK
    rw [← integral_add (bessel_kernel_integrable (r+1) t ht)
      (bessel_kernel_integrable (r-1) t ht), ← integral_div]
    apply integral_congr_ae
    filter_upwards with u
    rw [add_mul, sub_mul, one_mul, cosh_add, cosh_sub]
    ring
  have he : (fun u => exp (-t*cosh u)*H ν p r u) =
      (fun u => exp (-t*cosh u)*cosh (p*u)) -
      (fun u => exp (-t*cosh u)*cosh u*cosh (r*u)) -
      (fun u => ν*(exp (-t*cosh u)*S r u*sinh u)) := by ext u; dsimp [H]; ring
  rw [J, he]
  change (∫ u in Ioi 0, (exp (-t*cosh u)*cosh (p*u)-exp (-t*cosh u)*cosh u*cosh (r*u))-ν*(exp (-t*cosh u)*S r u*sinh u)) = _
  have h1 := integral_sub ((bessel_kernel_integrable p t ht).sub
    (bessel_cosh_integrable r t ht)) ((S_sinh_integrable r t ht).const_mul ν)
  simp only [Pi.sub_apply] at h1
  rw [h1, integral_sub (bessel_kernel_integrable p t ht) (bessel_cosh_integrable r t ht),
    integral_const_mul, hc]
  rw [bessel_ibp r ht]
  dsimp [besselK]
  field_simp

private lemma weighted_J_integrable (ν p r : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t^(-ν)*J ν p r t) (Ioi x) := by
  apply ((tail_integrable ν p hx).sub
    (((tail_integrable ν (r+1) hx).add (tail_integrable ν (r-1) hx)).div_const 2) |>.sub
    ((tail_integrable (ν+1) r hx).const_mul ν)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 := lt_trans hx ht
  change t^(-ν)*besselK p t-(t^(-ν)*besselK (r+1) t+t^(-ν)*besselK (r-1) t)/2-ν*(t^(-(ν+1))*besselK r t) = _
  rw [J_eq ν p r ht0, show -(ν+1) = -ν-1 by ring, rpow_sub ht0,
    rpow_one]
  ring

private lemma tail_identity (ν p r : ℝ) {x : ℝ} (hx : 0 < x) :
    tail ν p x - x^(-ν)*besselK r x = ∫ t in Ioi x, t^(-ν)*J ν p r t := by
  have he (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t : ℝ => t^(-ν)*besselK r t)
        (t^(-ν)*J ν p r t-t^(-ν)*besselK p t) t := by
    have hc : (∫ u in Ioi 0, exp (-t*cosh u)*cosh u*cosh (r*u)) =
        (besselK (r+1) t+besselK (r-1) t)/2 := by
      unfold besselK
      rw [← integral_add (bessel_kernel_integrable (r+1) t ht)
        (bessel_kernel_integrable (r-1) t ht), ← integral_div]
      apply integral_congr_ae
      filter_upwards with u
      rw [add_mul, sub_mul, one_mul, cosh_add, cosh_sub]
      ring
    convert (hasDerivAt_rpow_const (p := -ν) (Or.inl ht.ne')).mul
      (bessel_hasDerivAt r ht) using 1
    rw [J_eq ν p r ht, hc, rpow_sub ht, rpow_one]
    ring
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x)
    (fun t ht => he t (lt_of_lt_of_le hx ht))
    ((weighted_J_integrable ν p r hx).sub (tail_integrable ν p hx))
    (weighted_bessel_tendsto ν r)
  rw [integral_sub (weighted_J_integrable ν p r hx) (tail_integrable ν p hx)] at hf
  dsimp [tail]
  linarith

private lemma integral_Ioi_pos {f : ℝ → ℝ} {a : ℝ}
    (hi : IntegrableOn f (Ioi a)) (hp : ∀ u ∈ Ioi a, 0 < f u) :
    0 < ∫ u in Ioi a, f u := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).mpr
  · have hs : Function.support f ∩ Ioi a = Ioi a := by
      ext u
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      exact ⟨And.right, fun hu => ⟨(hp u hu).ne', hu⟩⟩
    rw [hs]
    simp only [Real.volume_Ioi, ENNReal.zero_lt_top]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hp u hu).le

private lemma strict_tail {ν p q : ℝ} (hq : 0 ≤ q) (hν : q < ν)
    (he : p^2 = q^2+2*ν+1) {x : ℝ} (hx : 0 < x) :
    x^(-ν)*besselK q x < tail ν p x := by
  have hh (u : ℝ) (hu : 0 < u) : 0 < H ν p q u := by
    rcases eq_or_lt_of_le hq with hq0 | hq0
    · subst q
      have h := zero_order_kernel hu hν (by simpa using he)
      simp only [H, S, zero_mul, cosh_zero, one_mul, ite_true]
      linarith
    · have h := positive_order_kernel hu hq0 hν he
      dsimp [H, S]
      rw [if_neg hq0.ne']
      have heq : ν*(sinh (q*u)/q)*sinh u = ν/q*sinh (q*u)*sinh u := by ring
      rw [heq]
      linarith
  have hj (t : ℝ) (ht : 0 < t) : 0 < J ν p q t :=
    integral_Ioi_pos (H_integrable ν p q ht) (fun u hu => mul_pos (exp_pos _) (hh u hu))
  have h := integral_Ioi_pos (weighted_J_integrable ν p q hx)
    (fun t ht => mul_pos (rpow_pos_of_pos (lt_trans hx ht) _) (hj t (lt_trans hx ht)))
  rw [← tail_identity ν p q hx] at h
  linarith

private lemma n_one_identity (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    tail ν (ν+1) x = x^(-ν)*besselK ν x := by
  have hh (u : ℝ) : H ν (ν+1) ν u = 0 := by
    dsimp [H, S]
    rw [add_mul, one_mul, cosh_add]
    split_ifs with h
    · subst ν; simp
    · field_simp
      ring
  have hj (t : ℝ) : J ν (ν+1) ν t = 0 := by simp [J, hh]
  have h := tail_identity ν (ν+1) ν hx
  simp only [hj, mul_zero, integral_zero] at h
  exact sub_eq_zero.mp h

end D5.S3.Analytic.GauntBesselTail.Result

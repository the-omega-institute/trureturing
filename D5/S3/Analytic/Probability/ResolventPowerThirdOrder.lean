/- GID: D5/S3/Analytic/Probability/ResolventPowerThirdOrder
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/ResolventPowerThirdOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ParametricIntegral, mathlib/module/Mathlib.Probability.Moments.Variance]
   utility: none
   digest: Third order bounds for real powers of normalized probability Stieltjes transforms. -/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

/-! Actual derivatives of probability Stieltjes transforms and their real powers. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace D5.S3.Analytic.Probability.ResolventPowerThirdOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The normalized Stieltjes transform of a real random variable. -/
def stieltjes (μ : Measure Ω) (R : Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, (1 + R ω * s)⁻¹ ∂μ

/-- The actual real power curve, defined by the integral rather than a formal jet. -/
def powerCurve (μ : Measure Ω) (R : Ω → ℝ) (a q s : ℝ) : ℝ :=
  (1 + a * s) ^ (q + 1) * (stieltjes μ R s) ^ q

private def kernel (n : ℕ) (s r : ℝ) : ℝ :=
  (-1 : ℝ)^n * (n.factorial : ℝ) * r^n * ((1 + r * s)⁻¹)^(n + 1)

private lemma denominator_bound {s r : ℝ} (hs : s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hr : r ∈ Icc (0 : ℝ) 1) : (1 / 2 : ℝ) ≤ 1 + r * s := by
  have := mul_nonneg hr.1 (show 0 ≤ s + 1 / 2 by linarith [hs.1])
  nlinarith [hr.2]

private lemma kernel_bound (n : ℕ) {s r : ℝ}
    (hs : s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖kernel n s r‖ ≤ (n.factorial : ℝ) * 2^(n + 1) := by
  have hd := denominator_bound hs hr
  have hi : 0 ≤ (1 + r * s)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi2 : (1 + r * s)⁻¹ ≤ 2 := (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by norm_num; linarith)
  have hrn : r^n ≤ 1 := pow_le_one₀ hr.1 hr.2
  have hin : ((1 + r * s)⁻¹)^(n + 1) ≤ 2^(n + 1) := pow_le_pow_left₀ hi hi2 _
  simp only [kernel, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Real.norm_eq_abs, abs_of_nonneg hr.1, abs_of_nonneg hi,
    abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) by positivity)]
  calc
    (n.factorial : ℝ) * r^n * ((1 + r * s)⁻¹)^(n + 1)
      ≤ (n.factorial : ℝ) * 1 * 2^(n + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrn (by positivity)) hin (by positivity)
          (by positivity)
    _ = _ := by ring

private lemma kernel_derivative (n : ℕ) {s r : ℝ} (hd : 1 + r * s ≠ 0) :
    HasDerivAt (fun t => kernel n t r) (kernel (n + 1) s r) s := by
  have hbase : HasDerivAt (fun t : ℝ => 1 + r * t) r s := by
    convert (hasDerivAt_const s 1).add ((hasDerivAt_id s).const_mul r) using 1 <;> (try funext t) <;> simp
  refine (((hbase.fun_inv hd).fun_pow (n + 1)).const_mul
    ((-1 : ℝ)^n * (n.factorial : ℝ) * r^n)).congr_deriv ?_
  simp only [kernel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel, inv_pow]
  simp only [pow_succ]
  field_simp [hd]

private def transform (μ : Measure Ω) (R : Ω → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∫ ω, kernel n s (R ω) ∂μ

private lemma kernel_integrable {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) (n : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : Integrable (fun ω => kernel n s (R ω)) μ := by
  apply (integrable_const ((n.factorial : ℝ) * 2^(n + 1))).mono'
  · unfold kernel
    fun_prop
  · exact hbound.mono fun ω hω => kernel_bound n hs hω

private lemma transform_derivative {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) (n : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (transform μ R n) (transform μ R (n + 1) s) s := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t ω => kernel n t (R ω)) (F' := fun t ω => kernel (n + 1) t (R ω))
    (bound := fun _ => ((n + 1).factorial : ℝ) * 2^(n + 2))
    (Ioo_mem_nhds hs.1 hs.2) _ (kernel_integrable hR hbound n hs) _ _
    (integrable_const _) _).2
  · exact Eventually.of_forall fun t => by unfold kernel; fun_prop
  · unfold kernel; fun_prop
  · exact hbound.mono fun ω hω t ht => kernel_bound (n + 1) ht hω
  · exact hbound.mono fun ω hω t ht =>
      kernel_derivative n (ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_bound ht hω)))

private lemma transform_zero (R : Ω → ℝ) (n : ℕ) :
    transform μ R n 0 = (-1 : ℝ)^n * (n.factorial : ℝ) * ∫ ω, R ω^n ∂μ := by
  simp [transform, kernel, integral_const_mul]

private lemma transform_zero_eq (R : Ω → ℝ) : transform μ R 0 = stieltjes μ R := by
  funext s
  simp [transform, kernel, stieltjes]

private structure Chain (f : ℝ → ℝ) where
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  d3 : ℝ → ℝ
  h0 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt f (d1 s) s
  h1 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt d1 (d2 s) s
  h2 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt d2 (d3 s) s

private lemma Chain.actual {f : ℝ → ℝ} (c : Chain f) :
    iteratedDeriv 2 f 0 = c.d2 0 ∧ iteratedDeriv 3 f 0 = c.d3 0 := by
  have he1 : deriv f =ᶠ[𝓝 (0 : ℝ)] c.d1 := c.h0.mono fun _ h => h.deriv
  have he2 : deriv (deriv f) =ᶠ[𝓝 (0 : ℝ)] c.d2 :=
    he1.deriv.trans (c.h1.mono fun _ h => h.deriv)
  constructor
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he2.eq_of_nhds
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      he2.deriv_eq.trans c.h2.self_of_nhds.deriv

private def Chain.mul {f g : ℝ → ℝ} (c : Chain f) (d : Chain g) :
    Chain (fun s => f s * g s) where
  d1 := fun s => c.d1 s * g s + f s * d.d1 s
  d2 := fun s => c.d2 s * g s + 2 * c.d1 s * d.d1 s + f s * d.d2 s
  d3 := fun s => c.d3 s * g s + 3 * c.d2 s * d.d1 s + 3 * c.d1 s * d.d2 s + f s * d.d3 s
  h0 := by
    filter_upwards [c.h0,d.h0] with s hc hd
    exact hc.mul hd
  h1 := by
    filter_upwards [c.h0,c.h1,d.h0,d.h1] with s hc0 hc1 hd0 hd1
    convert (hc1.mul hd0).add (hc0.mul hd1) using 1 <;> (try dsimp) <;> ring
  h2 := by
    filter_upwards [c.h0,c.h1,c.h2,d.h0,d.h1,d.h2] with s hc0 hc1 hc2 hd0 hd1 hd2
    convert ((hc2.mul hd0).add (((hc1.const_mul 2).mul hd1))).add
      (hc0.mul hd2) using 1 <;> (try dsimp) <;> ring

private def Chain.rpow {f : ℝ → ℝ} (c : Chain f) (p : ℝ)
    (hn : ∀ᶠ s in 𝓝 (0 : ℝ), f s ≠ 0) : Chain (fun s => (f s)^p) where
  d1 := fun s => p * (f s)^(p - 1) * c.d1 s
  d2 := fun s => p * (p - 1) * (f s)^(p - 2) * (c.d1 s)^2 + p * (f s)^(p - 1) * c.d2 s
  d3 := fun s => p * (p - 1) * (p - 2) * (f s)^(p - 3) * (c.d1 s)^3 +
    3 * p * (p - 1) * (f s)^(p - 2) * c.d1 s * c.d2 s + p * (f s)^(p - 1) * c.d3 s
  h0 := by
    filter_upwards [c.h0,hn] with s hc hs
    convert hc.rpow_const (p := p) (Or.inl hs) using 1 <;> (try dsimp) <;> ring
  h1 := by
    filter_upwards [c.h0,c.h1,hn] with s hc0 hc1 hs
    convert (((hc0.rpow_const (p := p - 1) (Or.inl hs)).const_mul p).mul hc1) using 1
    try dsimp
    rw [show p - 1 - 1 = p - 2 by ring]
    ring
  h2 := by
    filter_upwards [c.h0,c.h1,c.h2,hn] with s hc0 hc1 hc2 hs
    have hl := ((hc0.rpow_const (p := p - 2) (Or.inl hs)).const_mul (p * (p - 1))).mul (hc1.pow 2)
    have hr := ((hc0.rpow_const (p := p - 1) (Or.inl hs)).const_mul p).mul hc2
    convert hl.add hr using 1
    try dsimp
    rw [show p - 2 - 1 = p - 3 by ring, show p - 1 - 1 = p - 2 by ring]
    ring

private def affineChain (a : ℝ) : Chain (fun s : ℝ => 1 + a * s) where
  d1 := fun _ => a
  d2 := fun _ => 0
  d3 := fun _ => 0
  h0 := Eventually.of_forall fun s => by
    convert (hasDerivAt_const s 1).add ((hasDerivAt_id s).const_mul a) using 1 <;> (try funext t) <;> simp
  h1 := Eventually.of_forall fun s => hasDerivAt_const s a
  h2 := Eventually.of_forall fun s => hasDerivAt_const s 0

private def transformChain {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) : Chain (stieltjes μ R) where
  d1 := transform μ R 1
  d2 := transform μ R 2
  d3 := transform μ R 3
  h0 := by
    have h := (Ioo_mem_nhds (show -(1 / 2 : ℝ)<0 by norm_num) (show (0 : ℝ)<1 / 2 by norm_num))
    filter_upwards [h] with s hs
    simpa only [← transform_zero_eq R] using transform_derivative hR hbound 0 hs
  h1 := by
    filter_upwards [Ioo_mem_nhds (show -(1 / 2 : ℝ)<0 by norm_num) (show (0 : ℝ)<1 / 2 by norm_num)] with s hs
    exact transform_derivative hR hbound 1 hs
  h2 := by
    filter_upwards [Ioo_mem_nhds (show -(1 / 2 : ℝ)<0 by norm_num) (show (0 : ℝ)<1 / 2 by norm_num)] with s hs
    exact transform_derivative hR hbound 2 hs

/-- The actual second and third derivatives at zero, in terms of the first three moments. -/
theorem powerCurve_derivatives {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) (a q : ℝ) :
    iteratedDeriv 2 (powerCurve μ R a q) 0 =
      q * (q + 1) * (a - (∫ ω, R ω ∂μ))^2 +
        2 * q * ((∫ ω, R ω^2 ∂μ) - (∫ ω, R ω ∂μ)^2) ∧
    iteratedDeriv 3 (powerCurve μ R a q) 0 =
      q * ((q + 1) * (a - (∫ ω, R ω ∂μ))^2 * ((q - 1) * (a - (∫ ω, R ω ∂μ)) - 3 * (∫ ω, R ω ∂μ)) +
        6 * ((q + 1) * (a - (∫ ω, R ω ∂μ)) - (∫ ω, R ω ∂μ))*
          ((∫ ω, R ω^2 ∂μ) - (∫ ω, R ω ∂μ)^2) -
        6 * ((∫ ω, R ω^3 ∂μ) - 3 * (∫ ω, R ω ∂μ) * (∫ ω, R ω^2 ∂μ) + 2 * (∫ ω, R ω ∂μ)^3)) := by
  let c := affineChain a
  let d := transformChain hR hbound
  have hnA : ∀ᶠ s in 𝓝 (0 : ℝ), (1 + a * s : ℝ) ≠ 0 :=
    c.h0.self_of_nhds.continuousAt.eventually_ne (by simp)
  have hK : stieltjes μ R 0 = 1 := by simp [stieltjes]
  have hnK : ∀ᶠ s in 𝓝 (0 : ℝ), stieltjes μ R s ≠ 0 :=
    d.h0.self_of_nhds.continuousAt.eventually_ne (by rw [hK]; norm_num)
  have hh := ((c.rpow (q + 1) hnA).mul (d.rpow q hnK)).actual
  dsimp [Chain.mul, Chain.rpow, c, d, affineChain, transformChain] at hh
  simp only [mul_zero, add_zero, hK, Real.one_rpow, transform_zero,
    pow_one, one_mul, Nat.factorial] at hh
  change iteratedDeriv 2 (powerCurve μ R a q) 0 = _ ∧
    iteratedDeriv 3 (powerCurve μ R a q) 0 = _ at hh
  constructor
  · rw [hh.1]
    norm_num
    ring
  · rw [hh.2]
    norm_num
    ring

private lemma moment_integrable {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun ω => R ω^n) μ := by
  apply (integrable_const (1 : ℝ)).mono' (hR.pow_const n).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg hω.1] using pow_le_one₀ hω.1 hω.2

private lemma weighted_square {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) (x y : ℝ) :
    0 ≤ x^2 * (∫ ω, R ω^3 ∂μ) - 2 * x * y * (∫ ω, R ω^2 ∂μ) + y^2 * (∫ ω, R ω ∂μ) := by
  have hp := moment_integrable hR hbound
  have h1 : Integrable R μ := by simpa using hp 1
  have he : (∫ ω, R ω * (x * R ω - y)^2 ∂μ) =
      x^2 * (∫ ω, R ω^3 ∂μ) - 2 * x * y * (∫ ω, R ω^2 ∂μ) + y^2 * (∫ ω, R ω ∂μ) := by
    calc
      _ = ∫ ω, x^2 * R ω^3 - (2 * x * y) * R ω^2 + y^2 * R ω ∂μ :=
        integral_congr_ae (ae_of_all μ fun ω => by ring)
      _ = _ := by
        have hsum := integral_add (((hp 3).const_mul (x^2)).sub ((hp 2).const_mul (2 * x * y)))
          (h1.const_mul (y^2))
        have hdiff := integral_sub ((hp 3).const_mul (x^2)) ((hp 2).const_mul (2 * x * y))
        simp only [Pi.sub_apply, integral_const_mul] at hsum hdiff
        rw [hsum,hdiff]
  rw [← he]
  exact integral_nonneg_of_ae (hbound.mono fun ω hω => mul_nonneg hω.1 (sq_nonneg _))

private lemma moment_bounds {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) :
    0 ≤ (∫ ω, R ω ∂μ) ∧ (∫ ω, R ω ∂μ) ≤ 1 ∧
    0 ≤ (∫ ω, R ω^2 ∂μ) - (∫ ω, R ω ∂μ)^2 ∧
    (∫ ω, R ω^2 ∂μ) - (∫ ω, R ω ∂μ)^2 ≤
      (∫ ω, R ω ∂μ) * (1 - (∫ ω, R ω ∂μ)) := by
  have hvar := ProbabilityTheory.variance_eq_sub (memLp_of_bounded hbound hR.aestronglyMeasurable 2)
  have hv0 := ProbabilityTheory.variance_nonneg R μ
  have hv1 := ProbabilityTheory.variance_le_sub_mul_sub hbound hR.aemeasurable
  have hi : Integrable R μ := by simpa using moment_integrable hR hbound 1
  refine ⟨integral_nonneg_of_ae (hbound.mono fun _ h => h.1), ?_, ?_, ?_⟩
  · calc
      (∫ ω, R ω ∂μ) ≤ ∫ _, (1 : ℝ) ∂μ := integral_mono_ae hi (integrable_const _) (hbound.mono fun _ h => h.2)
      _ = 1 := by simp
  · simpa only [hvar, Pi.pow_apply] using hv0
  · simpa only [hvar, Pi.pow_apply, sub_zero, mul_comm] using hv1

private lemma supercritical_algebra {a q m v z : ℝ}
    (ha1 : a ≤ 1) (hq : 1 ≤ q) (hm0 : 0 ≤ m)
    (hv0 : 0 ≤ v) (hv1 : v ≤ m * (1 - m))
    (hw : 0 ≤ z - 2 * a * (v + m^2) + a^2 * m) :
    q * ((q + 1) * (a - m)^2 * ((q - 1) * (a - m) - 3 * m) +
      6 * ((q + 1) * (a - m) - m) * v - 6 * (z - 3 * m * (v + m^2) + 2 * m^3)) ≤
      (q - 1) * (q * (q + 1) * (a - m)^2 + 2 * q * v) := by
  let d := a - m
  let b := 1 - a
  let T := d^2 * (2 * b + 5 * m) + 2 * (1 - 3 * d) * v
  have hd : d + m + b=1 := by dsimp [d,b]; ring
  have hb : 0 ≤ b := sub_nonneg.mpr ha1
  have ht : 0 ≤ T := by
    by_cases hc : d ≤ 1 / 3
    · exact add_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
        (mul_nonneg (by linarith) hv0)
    · have hc' : 0 < d := by linarith
      have hc2 : 2 * (1 - 3 * d) ≤ 0 := by linarith
      have hlow := mul_le_mul_of_nonpos_left hv1 hc2
      have he : d^2 * (2 * b + 5 * m) + 2 * (1 - 3 * d) * (m * (1 - m)) =
          2 * b * (d - m)^2 + 2 * b * d * m + m * d^2 + 2 * d * m^2 + 2 * m * b^2 := by
        dsimp [b,d]; ring
      dsimp [T]
      rw [← add_le_add_iff_left (d^2 * (2 * b + 5 * m)), he] at hlow
      exact le_trans (by positivity) hlow
  have he : (q - 1) * (q * (q + 1) * (a - m)^2 + 2 * q * v) -
      q * ((q + 1) * (a - m)^2 * ((q - 1) * (a - m) - 3 * m) +
        6 * ((q + 1) * (a - m) - m) * v - 6 * (z - 3 * m * (v + m^2) + 2 * m^3)) =
      q * (6 * (z - 2 * a * (v + m^2) + a^2 * m) + (q - 1) * T + (q - 1)^2 * d^2 * (1 - a + m)) := by
    dsimp [T,d,b]; ring
  have hn : 0 ≤ q * (6 * (z - 2 * a * (v + m^2) + a^2 * m) + (q - 1) * T + (q - 1)^2 * d^2 * (1 - a + m)) := by
    apply mul_nonneg (by linarith)
    exact add_nonneg (add_nonneg (by positivity) (mul_nonneg (by linarith) ht))
      (mul_nonneg (by positivity) (by linarith))
  linarith

private lemma subcritical_algebra {a q m v z : ℝ}
    (ha : 0 ≤ a) (hq0 : 0 < q) (hq1 : q ≤ 1) (hm : 0 ≤ m)
    (hv0 : 0 ≤ v) (hv1 : v ≤ m * (1 - m)) (hz : 0 ≤ z)
    (hminor : 0 ≤ m * (m * z - (v + m^2)^2)) :
    q * ((q + 1) * (a - m)^2 * ((q - 1) * (a - m) - 3 * m) +
      6 * ((q + 1) * (a - m) - m) * v - 6 * (z - 3 * m * (v + m^2) + 2 * m^3)) ≤ 0 := by
  by_cases hm0 : m=0
  · have hv : v=0 := by rw [hm0] at hv1; nlinarith
    rw [hm0,hv]
    simp only [sub_zero, mul_zero, zero_mul, zero_pow (by decide : 3≠0), add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hq0.le
      (sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) ha)) (by positivity)))
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hmin : 0 ≤ m * z - (v + m^2)^2 := nonneg_of_mul_nonneg_right hminor hmpos
  let d := a - m
  let tau := z - 3 * m * (v + m^2) + 2 * m^3
  have htau : 0 ≤ m * tau - v^2 + m^2 * v := by dsimp [tau]; nlinarith [hmin]
  have he : m * ((q + 1) * d^2 * ((q - 1) * d - 3 * m) + 6 * ((q + 1) * d - m) * v - 6 * tau) =
      m * (q^2 - 1) * d^2 * (a + m / 2) - 6 * (v - (q + 1) * m * d / 2)^2 - 6 * (m * tau - v^2 + m^2 * v) := by
    dsimp [d,tau]; ring
  have hq : q^2 - 1 ≤ 0 := by nlinarith
  have hh : m * ((q + 1) * d^2 * ((q - 1) * d - 3 * m) + 6 * ((q + 1) * d - m) * v - 6 * tau) ≤ 0 := by
    rw [he]
    have hfirst : m * (q^2 - 1) * d^2 * (a + m / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hm hq) (sq_nonneg _))
        (by positivity)
    nlinarith [sq_nonneg (v - (q + 1) * m * d / 2)]
  exact mul_nonpos_of_nonneg_of_nonpos hq0.le (nonpos_of_mul_nonpos_right hh hmpos)

/-- Sharp one-sided third-order bounds for every probability law on the unit interval.
No differentiability premise or exclusion of endpoint atoms is required. -/
theorem powerCurve_third_order {R : Ω → ℝ} (hR : Measurable R)
    (hbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (0 : ℝ) 1) {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : 0 < q) :
    0 ≤ iteratedDeriv 2 (powerCurve μ R a q) 0 ∧
    (1 ≤ q → iteratedDeriv 3 (powerCurve μ R a q) 0 ≤
      (q - 1) * iteratedDeriv 2 (powerCurve μ R a q) 0) ∧
    (q ≤ 1 → iteratedDeriv 3 (powerCurve μ R a q) 0 ≤ 0) := by
  let m := ∫ ω, R ω ∂μ
  let v := (∫ ω, R ω^2 ∂μ) - m^2
  let z := ∫ ω, R ω^3 ∂μ
  obtain ⟨hm0,_hm1,hv0,hv1⟩ := moment_bounds hR hbound
  have hw : 0 ≤ z - 2 * a * (v + m^2) + a^2 * m := by
    convert weighted_square hR hbound 1 a using 1 <;> dsimp [m,v,z] <;> ring
  have hminor : 0 ≤ m * (m * z - (v + m^2)^2) := by
    convert weighted_square hR hbound m (∫ ω, R ω^2 ∂μ) using 1 <;> dsimp [m,v,z] <;> ring
  have hz : 0 ≤ z := integral_nonneg_of_ae (hbound.mono fun ω hω => pow_nonneg hω.1 3)
  obtain ⟨hd2,hd3⟩ := powerCurve_derivatives hR hbound a q
  rw [hd2,hd3]
  refine ⟨?_,?_,?_⟩
  · exact add_nonneg (mul_nonneg (mul_nonneg hq.le (by linarith)) (sq_nonneg _))
      (mul_nonneg (by positivity) hv0)
  · intro hq1
    simpa only [v, m, z, sub_add_cancel] using
      supercritical_algebra ha1 hq1 hm0 hv0 hv1 hw
  · intro hq1
    simpa only [v, m, z, sub_add_cancel] using
      subcritical_algebra ha0 hq hq1 hm0 hv0 hv1 hz hminor

end D5.S3.Analytic.Probability.ResolventPowerThirdOrder

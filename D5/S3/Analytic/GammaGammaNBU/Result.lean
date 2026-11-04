/- GID: D5/S3/Analytic/GammaGammaNBU/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/GammaGammaNBU/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.Analysis.SumIntegralComparisons]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/GammaGammaNBU/Result.claim; result=D5/S3/Analytic/GammaGammaNBU/Result.result; claim=D5/S3/Analytic/GammaGammaNBU/Result.claim
   digest: Bessel integral substitution and rational quadrature refute gamma-gamma NBU. -/

/-
admission_basis: open-problem-resolution (BPV Question 8; Refuted).
escape_witness: none.
The only public theorem is result, the exact negation of claim.
All rows are bind-only after inlining same-delivery helpers. The analytic
steps instantiate exponential change of variables, integral_comp_abs,
integrable_prod_iff, integral_integral_swap, sum_Ico_le_integral_of_le
and integral_le_sum_Ico_of_le after scaling the grid. The upper comparison
changes only the zero endpoint, preserving the integral. Exponent comparisons are algebraic
normalization; exponential bounds instantiate Real.exp_bound and monotonicity
of natural powers. Finite tables and sums use exact rational normalization.
No row claims an escape witness. No D5 module is imported, so every row has
frozen D5 dependencies: none (no declaration identity to list).
Per declaration: name | proof_shape | consumers | frozen dependencies.
  besselK | bind-only (definition) | bessel_mix, density, density_one, survival_mix | none
  density | bind-only (definition) | density_one, survival, survival_mix | none
  survival | bind-only (definition) | claim, result, survival_mix, witness_lower, witness_upper | none
  claim | bind-only (definition) | result | none
  kernel | bind-only (definition) | bessel_mix, grid_integral_lower, grid_integral_upper, kernel_dec, kernel_inc, kernel_integrable, kernel_lower, lower_cell, mix_integrable_inner, mix_integral_inner, peak_upper, result, survival_mix, upper_cell, witness_lower, witness_upper | none
  kernel_integrable | bind-only | grid_integral_lower, grid_integral_upper, survival_mix, witness_lower, witness_upper | none
  density_one | bind-only | survival_mix | none
  bessel_mix | bind-only | survival_mix | none
  mix_integrable_inner | bind-only | survival_mix | none
  mix_integral_inner | bind-only | survival_mix | none
  survival_mix | bind-only | result, witness_lower, witness_upper | none
  kernel_inc | bind-only | kernel_lower, upper_cell | none
  kernel_dec | bind-only | kernel_lower, upper_cell | none
  kernel_lower | bind-only | lower_cell | none
  poly | bind-only (definition) | exp_lower_cert, exp_scaled_bounds, exp_upper_cert, lowerCert0, lowerCert104, lowerCert112, lowerCert120, lowerCert128, lowerCert136, lowerCert144, lowerCert152, lowerCert16, lowerCert160, lowerCert168, lowerCert176, lowerCert184, lowerCert192, lowerCert24, lowerCert32, lowerCert40, lowerCert48, lowerCert56, lowerCert64, lowerCert72, lowerCert8, lowerCert80, lowerCert88, lowerCert96, peak_upper, upperCert0, upperCert16, upperCert24, upperCert32, upperCert40, upperCert48, upperCert56, upperCert64, upperCert72, upperCert8, upperCert80, upperCert88, witness_upper | none
  err | bind-only (definition) | exp_lower_cert, exp_scaled_bounds, exp_upper_cert, lowerCert0, lowerCert104, lowerCert112, lowerCert120, lowerCert128, lowerCert136, lowerCert144, lowerCert152, lowerCert16, lowerCert160, lowerCert168, lowerCert176, lowerCert184, lowerCert192, lowerCert24, lowerCert32, lowerCert40, lowerCert48, lowerCert56, lowerCert64, lowerCert72, lowerCert8, lowerCert80, lowerCert88, lowerCert96, peak_upper, upperCert0, upperCert16, upperCert24, upperCert32, upperCert40, upperCert48, upperCert56, upperCert64, upperCert72, upperCert8, upperCert80, upperCert88, witness_upper | none
  exp_scaled_bounds | bind-only | exp_lower_cert, exp_upper_cert | none
  exp_lower_cert | bind-only | lowerCert0, lowerCert104, lowerCert112, lowerCert120, lowerCert128, lowerCert136, lowerCert144, lowerCert152, lowerCert16, lowerCert160, lowerCert168, lowerCert176, lowerCert184, lowerCert192, lowerCert24, lowerCert32, lowerCert40, lowerCert48, lowerCert56, lowerCert64, lowerCert72, lowerCert8, lowerCert80, lowerCert88, lowerCert96 | none
  exp_upper_cert | bind-only | peak_upper, upperCert0, upperCert16, upperCert24, upperCert32, upperCert40, upperCert48, upperCert56, upperCert64, upperCert72, upperCert8, upperCert80, upperCert88, witness_upper | none
  grid_integral_lower | bind-only | witness_lower | none
  grid_integral_upper | bind-only | witness_upper | none
  lowerData | bind-only (definition) | lowerCert0, lowerCert104, lowerCert112, lowerCert120, lowerCert128, lowerCert136, lowerCert144, lowerCert152, lowerCert16, lowerCert160, lowerCert168, lowerCert176, lowerCert184, lowerCert192, lowerCert24, lowerCert32, lowerCert40, lowerCert48, lowerCert56, lowerCert64, lowerCert72, lowerCert8, lowerCert80, lowerCert88, lowerCert96, lowerSum0, lowerSum104, lowerSum112, lowerSum120, lowerSum128, lowerSum136, lowerSum144, lowerSum152, lowerSum16, lowerSum160, lowerSum168, lowerSum176, lowerSum184, lowerSum192, lowerSum24, lowerSum32, lowerSum40, lowerSum48, lowerSum56, lowerSum64, lowerSum72, lowerSum8, lowerSum80, lowerSum88, lowerSum96, lower_cell, lower_certificate, lower_sum, witness_lower | none
  upperData | bind-only (definition) | upperCert0, upperCert16, upperCert24, upperCert32, upperCert40, upperCert48, upperCert56, upperCert64, upperCert72, upperCert8, upperCert80, upperCert88, upper_cell, upper_certificate, witness_upper | none
  lowerY | bind-only (definition) | lowerCert0, lowerCert104, lowerCert112, lowerCert120, lowerCert128, lowerCert136, lowerCert144, lowerCert152, lowerCert16, lowerCert160, lowerCert168, lowerCert176, lowerCert184, lowerCert192, lowerCert24, lowerCert32, lowerCert40, lowerCert48, lowerCert56, lowerCert64, lowerCert72, lowerCert8, lowerCert80, lowerCert88, lowerCert96, lower_cell, lower_certificate | none
  upperY | bind-only (definition) | upperCert0, upperCert16, upperCert24, upperCert32, upperCert40, upperCert48, upperCert56, upperCert64, upperCert72, upperCert8, upperCert80, upperCert88, upper_cell, upper_certificate | none
  lowerCert0 | bind-only | lower_certificate | none
  lowerCert8 | bind-only | lower_certificate | none
  lowerCert16 | bind-only | lower_certificate | none
  lowerCert24 | bind-only | lower_certificate | none
  lowerCert32 | bind-only | lower_certificate | none
  lowerCert40 | bind-only | lower_certificate | none
  lowerCert48 | bind-only | lower_certificate | none
  lowerCert56 | bind-only | lower_certificate | none
  lowerCert64 | bind-only | lower_certificate | none
  lowerCert72 | bind-only | lower_certificate | none
  lowerCert80 | bind-only | lower_certificate | none
  lowerCert88 | bind-only | lower_certificate | none
  lowerCert96 | bind-only | lower_certificate | none
  lowerCert104 | bind-only | lower_certificate | none
  lowerCert112 | bind-only | lower_certificate | none
  lowerCert120 | bind-only | lower_certificate | none
  lowerCert128 | bind-only | lower_certificate | none
  lowerCert136 | bind-only | lower_certificate | none
  lowerCert144 | bind-only | lower_certificate | none
  lowerCert152 | bind-only | lower_certificate | none
  lowerCert160 | bind-only | lower_certificate | none
  lowerCert168 | bind-only | lower_certificate | none
  lowerCert176 | bind-only | lower_certificate | none
  lowerCert184 | bind-only | lower_certificate | none
  lowerCert192 | bind-only | lower_certificate | none
  lower_certificate | bind-only | lower_cell | none
  upperCert0 | bind-only | upper_certificate | none
  upperCert8 | bind-only | upper_certificate | none
  upperCert16 | bind-only | upper_certificate | none
  upperCert24 | bind-only | upper_certificate | none
  upperCert32 | bind-only | upper_certificate | none
  upperCert40 | bind-only | upper_certificate | none
  upperCert48 | bind-only | upper_certificate | none
  upperCert56 | bind-only | upper_certificate | none
  upperCert64 | bind-only | upper_certificate | none
  upperCert72 | bind-only | upper_certificate | none
  upperCert80 | bind-only | upper_certificate | none
  upperCert88 | bind-only | upper_certificate | none
  upper_certificate | bind-only | upper_cell | none
  peak_upper | bind-only | upper_cell | none
  lower_cell | bind-only | witness_lower | none
  upper_cell | bind-only | witness_upper | none
  lowerSum0 | bind-only | lower_sum | none
  lowerSum8 | bind-only | lower_sum | none
  lowerSum16 | bind-only | lower_sum | none
  lowerSum24 | bind-only | lower_sum | none
  lowerSum32 | bind-only | lower_sum | none
  lowerSum40 | bind-only | lower_sum | none
  lowerSum48 | bind-only | lower_sum | none
  lowerSum56 | bind-only | lower_sum | none
  lowerSum64 | bind-only | lower_sum | none
  lowerSum72 | bind-only | lower_sum | none
  lowerSum80 | bind-only | lower_sum | none
  lowerSum88 | bind-only | lower_sum | none
  lowerSum96 | bind-only | lower_sum | none
  lowerSum104 | bind-only | lower_sum | none
  lowerSum112 | bind-only | lower_sum | none
  lowerSum120 | bind-only | lower_sum | none
  lowerSum128 | bind-only | lower_sum | none
  lowerSum136 | bind-only | lower_sum | none
  lowerSum144 | bind-only | lower_sum | none
  lowerSum152 | bind-only | lower_sum | none
  lowerSum160 | bind-only | lower_sum | none
  lowerSum168 | bind-only | lower_sum | none
  lowerSum176 | bind-only | lower_sum | none
  lowerSum184 | bind-only | lower_sum | none
  lowerSum192 | bind-only | lower_sum | none
  lower_sum | bind-only | witness_lower | none
  witness_lower | bind-only | result | none
  witness_upper | bind-only | result | none
  result | bind-only | settling result | none
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SumIntegralComparisons
open MeasureTheory Set Real Filter
open scoped Topology BigOperators
noncomputable section
namespace D5.S3.Analytic.GammaGammaNBU.Result

def besselK (ν z : ℝ) : ℝ := ∫ t in Ioi 0, exp (-z * cosh t) * cosh (ν*t)
def density (a b α u : ℝ) : ℝ :=
  2 * (a*b)^((a+b)/2) * u^((a+b)/2-1) /
    (Gamma a * Gamma b * α^((a+b)/2)) * besselK (a-b) (2*sqrt (a*b*u/α))
def survival (a b α u : ℝ) : ℝ := ∫ t in Ioi u, density a b α t
def claim : Prop := ∀ a b α : ℝ, 0<a → 0<b → 0<α → ∀ u1 u2 : ℝ,
  0<u1 → 0<u2 → survival a b α (u1+u2) ≤ survival a b α u1 * survival a b α u2

private def kernel (u s : ℝ) := exp (-s-u/s)

private lemma kernel_integrable (u : ℝ) (hu : 0 ≤ u) : IntegrableOn (kernel u) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono' ?_ ?_
  · exact (measurable_id.neg.sub (measurable_const.div measurable_id)).exp.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change ‖exp (-s-u/s)‖ ≤ exp (-s)
    rw [Real.norm_of_nonneg (exp_nonneg _)]
    apply exp_le_exp.mpr
    have := div_nonneg hu (le_of_lt hs)
    linarith

private lemma density_one (t : ℝ) : density 1 1 1 t = 2*besselK 0 (2*sqrt t) := by
  norm_num [density, Gamma_one]


private lemma bessel_mix (t : ℝ) (ht : 0<t) :
    2*besselK 0 (2*sqrt t) = ∫ s in Ioi 0, s⁻¹ * kernel t s := by
  have hr : 0 < sqrt t := sqrt_pos_of_pos ht
  have hne := sqrt_ne_zero'.mpr ht
  have hs : (sqrt t)^2 = t := sq_sqrt ht.le
  have hp (x : ℝ) :
      exp x * ((exp x)⁻¹ * kernel t (exp x)) = exp (-exp x-t/exp x) := by
    simp [kernel, (exp_pos x).ne']
  rw [← integral_comp_exp (fun s => s⁻¹ * kernel t s)]
  simp_rw [smul_eq_mul, hp]
  rw [← integral_add_right_eq_self (fun x => exp (-exp x-t/exp x)) (log (sqrt t))]
  have he (x : ℝ) : -exp (x+log (sqrt t))-t/exp (x+log (sqrt t)) =
      -(2*sqrt t)*cosh x := by
    rw [exp_add, exp_log hr, cosh_eq, exp_neg]
    field_simp
    nlinarith [hs]
  simp_rw [he]
  have heven : (fun x : ℝ => exp (-(2*sqrt t)*cosh |x|)) =
      (fun x : ℝ => exp (-(2*sqrt t)*cosh x)) := by
    ext x; rw [cosh_abs]
  rw [← heven, integral_comp_abs (f := fun x => exp (-(2*sqrt t)*cosh x))]
  simp [besselK]

private lemma mix_integrable_inner (s u : ℝ) (hs : 0<s) :
    IntegrableOn (fun t => s⁻¹ * kernel t s) (Ioi u) := by
  have he (t : ℝ) : s⁻¹ * kernel t s = (s⁻¹ * exp (-s)) * exp ((-s⁻¹)*t) := by
    unfold kernel
    rw [show -s-t/s = -s + (-s⁻¹)*t by ring, exp_add]
    ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr (inv_pos.mpr hs)) u).const_mul _

private lemma mix_integral_inner (s u : ℝ) (hs : 0<s) :
    (∫ t in Ioi u, s⁻¹ * kernel t s) = kernel u s := by
  have he (t : ℝ) : s⁻¹ * kernel t s = (s⁻¹ * exp (-s)) * exp ((-s⁻¹)*t) := by
    unfold kernel
    rw [show -s-t/s = -s + (-s⁻¹)*t by ring, exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_iff_pos.mpr (inv_pos.mpr hs))]
  rw [show -s⁻¹*u = -(u/s) by ring, kernel, sub_eq_add_neg, exp_add]
  field_simp

private lemma survival_mix (u : ℝ) (hu : 0<u) :
    survival 1 1 1 u = ∫ s in Ioi 0, kernel u s := by
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1⁻¹ * kernel p.2 p.1) := by
    exact measurable_fst.inv.mul ((measurable_fst.neg.sub
      (measurable_snd.div measurable_fst)).exp)
  have hint : Integrable (fun p : ℝ × ℝ => p.1⁻¹ * kernel p.2 p.1)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi u))) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mix_integrable_inner s u hs
    · apply (kernel_integrable u hu.le).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      symm
      calc
        (∫ t in Ioi u, ‖s⁻¹ * kernel t s‖) = ∫ t in Ioi u, s⁻¹ * kernel t s := by
          apply integral_congr_ae
          filter_upwards with t
          apply Real.norm_of_nonneg
          exact mul_nonneg (inv_nonneg.mpr hs.le) (exp_nonneg _)
        _ = kernel u s := mix_integral_inner s u hs
  unfold survival
  calc
    (∫ t in Ioi u, density 1 1 1 t) = ∫ t in Ioi u, ∫ s in Ioi 0, s⁻¹ * kernel t s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [density_one, bessel_mix t (lt_trans hu ht)]
    _ = ∫ s in Ioi 0, ∫ t in Ioi u, s⁻¹ * kernel t s := (integral_integral_swap hint).symm
    _ = ∫ s in Ioi 0, kernel u s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact fun s hs => mix_integral_inner s u hs
private lemma kernel_inc (u a b : ℝ) (ha : 0<a) (hab : a≤b) (hp : a*b≤u) :
    kernel u a ≤ kernel u b := by
  have hb : 0<b := ha.trans_le hab
  have he (s : ℝ) (hs : s ≠ 0) : -s-u/s = (-s^2-u)/s := by field_simp
  unfold kernel
  apply exp_le_exp.mpr
  rw [he a ha.ne', he b hb.ne', div_le_div_iff₀ ha hb]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hp)]
private lemma kernel_dec (u a b : ℝ) (ha : 0<a) (hab : a≤b) (hp : u≤a*b) :
    kernel u b ≤ kernel u a := by
  have hb : 0<b := ha.trans_le hab
  have he (s : ℝ) (hs : s ≠ 0) : -s-u/s = (-s^2-u)/s := by field_simp
  unfold kernel
  apply exp_le_exp.mpr
  rw [he a ha.ne', he b hb.ne', div_le_div_iff₀ hb ha]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hp)]
private lemma kernel_lower (u a b s : ℝ) (ha : 0<a) (hs : s∈Icc a b) :
    min (kernel u a) (kernel u b) ≤ kernel u s := by
  have hp : 0<s := ha.trans_le hs.1
  by_cases hu : s*s ≤ u
  · exact (min_le_left _ _).trans (kernel_inc u a s ha hs.1
      ((mul_le_mul_of_nonneg_right hs.1 hp.le).trans hu))
  · exact (min_le_right _ _).trans (kernel_dec u s b hp hs.2
      ((le_of_not_ge hu).trans (mul_le_mul_of_nonneg_left hs.2 hp.le)))
private def poly (x : ℝ) := ∑ k ∈ Finset.range 6, x^k/(k.factorial : ℝ)
private def err (x : ℝ) := |x|^6 * (7/(720*6) : ℝ)
private lemma exp_scaled_bounds (y : ℝ) (hy : 0≤y) (hy' : y≤32)
    (hp : 0≤poly (-y/32) - err (-y/32)) :
    (poly (-y/32) - err (-y/32))^32 ≤ exp (-y) ∧
    exp (-y) ≤ (poly (-y/32) + err (-y/32))^32 := by
  have h := Real.exp_bound (x := -y/32) (n := 6) (by rw [abs_of_nonpos (by linarith)]; linarith) (by norm_num)
  change |exp (-y/32)-poly (-y/32)| ≤ err (-y/32) at h
  have hl : poly (-y/32)-err (-y/32) ≤ exp (-y/32) := by exact sub_le_of_abs_sub_le_left h
  have hh : exp (-y/32) ≤ poly (-y/32)+err (-y/32) := by linarith [(abs_sub_le_iff.mp h).1]
  have he : exp (-y/32)^32 = exp (-y) := by rw [← exp_nat_mul]; congr 1; norm_num; ring
  constructor
  · rw [← he]; exact pow_le_pow_left₀ hp hl 32
  · rw [← he]; exact pow_le_pow_left₀ (exp_nonneg _) hh 32

private lemma exp_lower_cert (y l : ℝ) (hy : 0≤y) (hy' : y≤32)
    (hp : 0≤poly (-y/32)-err (-y/32))
    (hl : l≤(poly (-y/32)-err (-y/32))^32) : l≤exp (-y) :=
  hl.trans (exp_scaled_bounds y hy hy' hp).1
private lemma exp_upper_cert (y r : ℝ) (hy : 0≤y) (hy' : y≤32)
    (hp : 0≤poly (-y/32)-err (-y/32))
    (hr : (poly (-y/32)+err (-y/32))^32≤r) : exp (-y)≤r :=
  (exp_scaled_bounds y hy hy' hp).2.trans hr

private lemma grid_integral_lower (u h : ℝ) (hu : 0≤u) (hh : 0<h)
    (n : ℕ) (c : ℕ → ℝ)
    (hb : ∀ k<n, ∀ s∈Ico ((k:ℝ)*h) ((k+1:ℕ)*h), c k ≤ kernel u s) :
    h * ∑ k∈Finset.range n, c k ≤ ∫ s in (0:ℝ)..(n:ℝ)*h, kernel u s := by
  have hi : IntervalIntegrable (kernel u) volume 0 ((n:ℝ)*h) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact (kernel_integrable u hu).mono_set (fun s hs => hs.1)
  have his : IntervalIntegrable (fun x => kernel u (h*x)) volume 0 (n:ℝ) := by
    simpa [hh.ne'] using hi.comp_mul_left (c := h)
  have hsum := sum_Ico_le_integral_of_le (a := 0) (b := n)
    (f := fun x => c ⌊x⌋₊) (g := fun x => kernel u (h*x)) (Nat.zero_le n)
    (by
      intro k hk x hx
      rw [Nat.floor_natCast]
      apply hb k hk.2 (h*x)
      constructor
      · simpa [mul_comm] using mul_le_mul_of_nonneg_left hx.1 hh.le
      · simpa [mul_comm] using mul_lt_mul_of_pos_left hx.2 hh)
    (by simpa using (intervalIntegrable_iff_integrableOn_Ico_of_le
      (Nat.cast_nonneg n)).mp his)
  simp only [Nat.cast_zero, Nat.floor_natCast, Nat.Ico_zero_eq_range] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum hh.le
  simpa [intervalIntegral.integral_comp_mul_left, hh.ne', smul_eq_mul,
    mul_comm h] using hscaled

private lemma grid_integral_upper (u h : ℝ) (hu : 0≤u) (hh : 0<h)
    (n : ℕ) (c : ℕ → ℝ)
    (hb : ∀ k<n, ∀ s∈Ico ((k:ℝ)*h) ((k+1:ℕ)*h), 0<s → kernel u s ≤ c k) :
    (∫ s in (0:ℝ)..(n:ℝ)*h, kernel u s) ≤ h * ∑ k∈Finset.range n, c k := by
  let g (x : ℝ) := if x=0 then c 0 else kernel u (h*x)
  have hi : IntervalIntegrable (kernel u) volume 0 ((n:ℝ)*h) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact (kernel_integrable u hu).mono_set (fun s hs => hs.1)
  have his : IntervalIntegrable (fun x => kernel u (h*x)) volume 0 (n:ℝ) := by
    simpa [hh.ne'] using hi.comp_mul_left (c := h)
  have heq : EqOn (fun x => kernel u (h*x)) g (uIoo 0 (n:ℝ)) := by
    rw [uIoo_of_le (Nat.cast_nonneg n)]
    intro x hx
    simp [g, ne_of_gt hx.1]
  have hsum := integral_le_sum_Ico_of_le (a := 0) (b := n)
    (f := fun x => c ⌊x⌋₊) (g := g) (Nat.zero_le n)
    (by
      intro k hk x hx
      rw [Nat.floor_natCast]
      by_cases hx0 : x=0
      · have hk0 : k=0 := by simpa [hx0] using hx.1
        simp [g, hx0, hk0]
      · have hxpos : 0<x := lt_of_le_of_ne ((Nat.cast_nonneg k).trans hx.1) (Ne.symm hx0)
        simp only [g, ite_eq_right hx0]
        apply hb k hk.2 (h*x) ?_ (mul_pos hh hxpos)
        constructor
        · simpa [mul_comm] using mul_le_mul_of_nonneg_left hx.1 hh.le
        · simpa [mul_comm] using mul_lt_mul_of_pos_left hx.2 hh)
    (by simpa using (intervalIntegrable_iff_integrableOn_Ico_of_le
      (Nat.cast_nonneg n)).mp (his.congr_uIoo heq))
  simp only [Nat.cast_zero, Nat.floor_natCast, Nat.Ico_zero_eq_range] at hsum
  rw [← intervalIntegral.integral_congr_uIoo heq] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum hh.le
  simpa [intervalIntegral.integral_comp_mul_left, hh.ne', smul_eq_mul,
    mul_comm h] using hscaled

private def lowerData (k : ℕ) : ℝ :=
  (if k < 100 then (if k < 50 then (if k < 25 then (if k < 12 then (if k < 6 then (if k < 3 then (if k < 1 then 0/1000000 else (if k < 2 then 0/1000000 else 3/1000000)) else (if k < 4 then 213/1000000 else (if k < 5 then 1645/1000000 else 5516/1000000))) else (if k < 9 then (if k < 7 then 12195/1000000 else (if k < 8 then 21249/1000000 else 31904/1000000)) else (if k < 10 then 43379/1000000 else (if k < 11 then 55023/1000000 else 66355/1000000)))) else (if k < 18 then (if k < 15 then (if k < 13 then 77047/1000000 else (if k < 14 then 86893/1000000 else 95778/1000000)) else (if k < 16 then 103657/1000000 else (if k < 17 then 110526/1000000 else 116415/1000000))) else (if k < 21 then (if k < 19 then 121372/1000000 else (if k < 20 then 125457/1000000 else 128734/1000000)) else (if k < 23 then (if k < 22 then 131272/1000000 else 133138/1000000) else (if k < 24 then 134397/1000000 else 135109/1000000))))) else (if k < 37 then (if k < 31 then (if k < 28 then (if k < 26 then 135127/1000000 else (if k < 27 then 134535/1000000 else 133606/1000000)) else (if k < 29 then 132381/1000000 else (if k < 30 then 130898/1000000 else 129192/1000000))) else (if k < 34 then (if k < 32 then 127294/1000000 else (if k < 33 then 125233/1000000 else 123034/1000000)) else (if k < 35 then 120719/1000000 else (if k < 36 then 118310/1000000 else 115824/1000000)))) else (if k < 43 then (if k < 40 then (if k < 38 then 113279/1000000 else (if k < 39 then 110689/1000000 else 108067/1000000)) else (if k < 41 then 105424/1000000 else (if k < 42 then 102772/1000000 else 100119/1000000))) else (if k < 46 then (if k < 44 then 97472/1000000 else (if k < 45 then 94840/1000000 else 92229/1000000)) else (if k < 48 then (if k < 47 then 89643/1000000 else 87088/1000000) else (if k < 49 then 84567/1000000 else 82084/1000000)))))) else (if k < 75 then (if k < 62 then (if k < 56 then (if k < 53 then (if k < 51 then 79643/1000000 else (if k < 52 then 77245/1000000 else 74892/1000000)) else (if k < 54 then 72587/1000000 else (if k < 55 then 70330/1000000 else 68123/1000000))) else (if k < 59 then (if k < 57 then 65967/1000000 else (if k < 58 then 63861/1000000 else 61807/1000000)) else (if k < 60 then 59804/1000000 else (if k < 61 then 57853/1000000 else 55953/1000000)))) else (if k < 68 then (if k < 65 then (if k < 63 then 54105/1000000 else (if k < 64 then 52307/1000000 else 50558/1000000)) else (if k < 66 then 48860/1000000 else (if k < 67 then 47210/1000000 else 45609/1000000))) else (if k < 71 then (if k < 69 then 44054/1000000 else (if k < 70 then 42547/1000000 else 41084/1000000)) else (if k < 73 then (if k < 72 then 39667/1000000 else 38293/1000000) else (if k < 74 then 36962/1000000 else 35673/1000000))))) else (if k < 87 then (if k < 81 then (if k < 78 then (if k < 76 then 34425/1000000 else (if k < 77 then 33217/1000000 else 32048/1000000)) else (if k < 79 then 30916/1000000 else (if k < 80 then 29822/1000000 else 28763/1000000))) else (if k < 84 then (if k < 82 then 27740/1000000 else (if k < 83 then 26750/1000000 else 25793/1000000)) else (if k < 85 then 24869/1000000 else (if k < 86 then 23976/1000000 else 23113/1000000)))) else (if k < 93 then (if k < 90 then (if k < 88 then 22279/1000000 else (if k < 89 then 21474/1000000 else 20696/1000000)) else (if k < 91 then 19946/1000000 else (if k < 92 then 19221/1000000 else 18521/1000000))) else (if k < 96 then (if k < 94 then 17846/1000000 else (if k < 95 then 17194/1000000 else 16565/1000000)) else (if k < 98 then (if k < 97 then 15958/1000000 else 15373/1000000) else (if k < 99 then 14808/1000000 else 14264/1000000))))))) else (if k < 150 then (if k < 125 then (if k < 112 then (if k < 106 then (if k < 103 then (if k < 101 then 13738/1000000 else (if k < 102 then 13232/1000000 else 12743/1000000)) else (if k < 104 then 12272/1000000 else (if k < 105 then 11818/1000000 else 11380/1000000))) else (if k < 109 then (if k < 107 then 10958/1000000 else (if k < 108 then 10551/1000000 else 10159/1000000)) else (if k < 110 then 9781/1000000 else (if k < 111 then 9417/1000000 else 9066/1000000)))) else (if k < 118 then (if k < 115 then (if k < 113 then 8727/1000000 else (if k < 114 then 8401/1000000 else 8087/1000000)) else (if k < 116 then 7785/1000000 else (if k < 117 then 7493/1000000 else 7213/1000000))) else (if k < 121 then (if k < 119 then 6942/1000000 else (if k < 120 then 6682/1000000 else 6431/1000000)) else (if k < 123 then (if k < 122 then 6189/1000000 else 5956/1000000) else (if k < 124 then 5732/1000000 else 5516/1000000))))) else (if k < 137 then (if k < 131 then (if k < 128 then (if k < 126 then 5308/1000000 else (if k < 127 then 5108/1000000 else 4915/1000000)) else (if k < 129 then 4730/1000000 else (if k < 130 then 4551/1000000 else 4379/1000000))) else (if k < 134 then (if k < 132 then 4213/1000000 else (if k < 133 then 4054/1000000 else 3900/1000000)) else (if k < 135 then 3753/1000000 else (if k < 136 then 3610/1000000 else 3473/1000000)))) else (if k < 143 then (if k < 140 then (if k < 138 then 3342/1000000 else (if k < 139 then 3215/1000000 else 3093/1000000)) else (if k < 141 then 2975/1000000 else (if k < 142 then 2862/1000000 else 2753/1000000))) else (if k < 146 then (if k < 144 then 2648/1000000 else (if k < 145 then 2548/1000000 else 2451/1000000)) else (if k < 148 then (if k < 147 then 2357/1000000 else 2267/1000000) else (if k < 149 then 2181/1000000 else 2098/1000000)))))) else (if k < 175 then (if k < 162 then (if k < 156 then (if k < 153 then (if k < 151 then 2018/1000000 else (if k < 152 then 1941/1000000 else 1867/1000000)) else (if k < 154 then 1795/1000000 else (if k < 155 then 1727/1000000 else 1661/1000000))) else (if k < 159 then (if k < 157 then 1597/1000000 else (if k < 158 then 1536/1000000 else 1477/1000000)) else (if k < 160 then 1421/1000000 else (if k < 161 then 1366/1000000 else 1314/1000000)))) else (if k < 168 then (if k < 165 then (if k < 163 then 1264/1000000 else (if k < 164 then 1215/1000000 else 1169/1000000)) else (if k < 166 then 1124/1000000 else (if k < 167 then 1081/1000000 else 1039/1000000))) else (if k < 171 then (if k < 169 then 999/1000000 else (if k < 170 then 961/1000000 else 924/1000000)) else (if k < 173 then (if k < 172 then 889/1000000 else 854/1000000) else (if k < 174 then 822/1000000 else 790/1000000))))) else (if k < 187 then (if k < 181 then (if k < 178 then (if k < 176 then 760/1000000 else (if k < 177 then 730/1000000 else 702/1000000)) else (if k < 179 then 675/1000000 else (if k < 180 then 649/1000000 else 624/1000000))) else (if k < 184 then (if k < 182 then 600/1000000 else (if k < 183 then 577/1000000 else 555/1000000)) else (if k < 185 then 533/1000000 else (if k < 186 then 513/1000000 else 493/1000000)))) else (if k < 193 then (if k < 190 then (if k < 188 then 474/1000000 else (if k < 189 then 456/1000000 else 438/1000000)) else (if k < 191 then 421/1000000 else (if k < 192 then 405/1000000 else 389/1000000))) else (if k < 196 then (if k < 194 then 374/1000000 else (if k < 195 then 360/1000000 else 346/1000000)) else (if k < 198 then (if k < 197 then 333/1000000 else 320/1000000) else (if k < 199 then 307/1000000 else 296/1000000))))))))

private def upperData (k : ℕ) : ℝ :=
  (if k < 48 then (if k < 24 then (if k < 12 then (if k < 6 then (if k < 3 then (if k < 1 then 2281/1000000 else (if k < 2 then 42144/1000000 else 105400/1000000)) else (if k < 4 then 159880/1000000 else (if k < 5 then 198560/1000000 else 223131/1000000))) else (if k < 9 then (if k < 7 then 236815/1000000 else (if k < 8 then 242522/1000000 else 250000/1000000)) else (if k < 10 then 242522/1000000 else (if k < 11 then 238513/1000000 else 231745/1000000)))) else (if k < 18 then (if k < 15 then (if k < 13 then 223131/1000000 else (if k < 14 then 213340/1000000 else 202861/1000000)) else (if k < 16 then 192050/1000000 else (if k < 17 then 181168/1000000 else 170400/1000000))) else (if k < 21 then (if k < 19 then 159880/1000000 else (if k < 20 then 149700/1000000 else 139923/1000000)) else (if k < 22 then 130588/1000000 else (if k < 23 then 121717/1000000 else 113321/1000000))))) else (if k < 36 then (if k < 30 then (if k < 27 then (if k < 25 then 105400/1000000 else (if k < 26 then 97947/1000000 else 90951/1000000)) else (if k < 28 then 84398/1000000 else (if k < 29 then 78268/1000000 else 72544/1000000))) else (if k < 33 then (if k < 31 then 67206/1000000 else (if k < 32 then 62233/1000000 else 57604/1000000)) else (if k < 34 then 53301/1000000 else (if k < 35 then 49302/1000000 else 45589/1000000)))) else (if k < 42 then (if k < 39 then (if k < 37 then 42144/1000000 else (if k < 38 then 38950/1000000 else 35989/1000000)) else (if k < 40 then 33246/1000000 else (if k < 41 then 30705/1000000 else 28354/1000000))) else (if k < 45 then (if k < 43 then 26178/1000000 else (if k < 44 then 24165/1000000 else 22304/1000000)) else (if k < 46 then 20583/1000000 else (if k < 47 then 18992/1000000 else 17522/1000000)))))) else (if k < 72 then (if k < 60 then (if k < 54 then (if k < 51 then (if k < 49 then 16164/1000000 else (if k < 50 then 14910/1000000 else 13751/1000000)) else (if k < 52 then 12682/1000000 else (if k < 53 then 11694/1000000 else 10783/1000000))) else (if k < 57 then (if k < 55 then 9941/1000000 else (if k < 56 then 9165/1000000 else 8449/1000000)) else (if k < 58 then 7788/1000000 else (if k < 59 then 7178/1000000 else 6616/1000000)))) else (if k < 66 then (if k < 63 then (if k < 61 then 6097/1000000 else (if k < 62 then 5619/1000000 else 5178/1000000)) else (if k < 64 then 4771/1000000 else (if k < 65 then 4396/1000000 else 4051/1000000))) else (if k < 69 then (if k < 67 then 3732/1000000 else (if k < 68 then 3438/1000000 else 3168/1000000)) else (if k < 70 then 2918/1000000 else (if k < 71 then 2688/1000000 else 2476/1000000))))) else (if k < 84 then (if k < 78 then (if k < 75 then (if k < 73 then 2281/1000000 else (if k < 74 then 2101/1000000 else 1935/1000000)) else (if k < 76 then 1783/1000000 else (if k < 77 then 1642/1000000 else 1512/1000000))) else (if k < 81 then (if k < 79 then 1393/1000000 else (if k < 80 then 1283/1000000 else 1181/1000000)) else (if k < 82 then 1088/1000000 else (if k < 83 then 1002/1000000 else 923/1000000)))) else (if k < 90 then (if k < 87 then (if k < 85 then 850/1000000 else (if k < 86 then 782/1000000 else 720/1000000)) else (if k < 88 then 663/1000000 else (if k < 89 then 611/1000000 else 562/1000000))) else (if k < 93 then (if k < 91 then 518/1000000 else (if k < 92 then 477/1000000 else 439/1000000)) else (if k < 94 then 404/1000000 else (if k < 95 then 372/1000000 else 343/1000000)))))))

private def lowerY (k : ℕ) : ℝ :=
  max ((k:ℝ)/25+1/((k:ℝ)/25)) (((k:ℝ)+1)/25+1/(((k:ℝ)+1)/25))
private def upperY (k : ℕ) : ℝ :=
  if k≤7 then ((k:ℝ)+1)/12+(1/2)/(((k:ℝ)+1)/12)
  else (k:ℝ)/12+(1/2)/((k:ℝ)/12)

private lemma lowerCert0 (k : ℕ) (hk : 0≤k ∧ k<8) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert8 (k : ℕ) (hk : 8≤k ∧ k<16) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert16 (k : ℕ) (hk : 16≤k ∧ k<24) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert24 (k : ℕ) (hk : 24≤k ∧ k<32) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert32 (k : ℕ) (hk : 32≤k ∧ k<40) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert40 (k : ℕ) (hk : 40≤k ∧ k<48) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert48 (k : ℕ) (hk : 48≤k ∧ k<56) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert56 (k : ℕ) (hk : 56≤k ∧ k<64) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert64 (k : ℕ) (hk : 64≤k ∧ k<72) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert72 (k : ℕ) (hk : 72≤k ∧ k<80) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert80 (k : ℕ) (hk : 80≤k ∧ k<88) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert88 (k : ℕ) (hk : 88≤k ∧ k<96) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert96 (k : ℕ) (hk : 96≤k ∧ k<104) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert104 (k : ℕ) (hk : 104≤k ∧ k<112) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert112 (k : ℕ) (hk : 112≤k ∧ k<120) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert120 (k : ℕ) (hk : 120≤k ∧ k<128) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert128 (k : ℕ) (hk : 128≤k ∧ k<136) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert136 (k : ℕ) (hk : 136≤k ∧ k<144) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert144 (k : ℕ) (hk : 144≤k ∧ k<152) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert152 (k : ℕ) (hk : 152≤k ∧ k<160) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert160 (k : ℕ) (hk : 160≤k ∧ k<168) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert168 (k : ℕ) (hk : 168≤k ∧ k<176) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert176 (k : ℕ) (hk : 176≤k ∧ k<184) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert184 (k : ℕ) (hk : 184≤k ∧ k<192) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lowerCert192 (k : ℕ) (hk : 192≤k ∧ k<200) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_lower_cert
  all_goals interval_cases k <;>
    norm_num [lowerData, lowerY, poly, err, Finset.sum_range_succ] at *

private lemma lower_certificate (k : ℕ) (hk : k<200) (hx : k≠0) :
    lowerData k ≤ exp (-lowerY k) := by
  by_cases h8 : k<8
  · exact lowerCert0 k ⟨by omega, h8⟩ hx
  by_cases h16 : k<16
  · exact lowerCert8 k ⟨by omega, h16⟩ hx
  by_cases h24 : k<24
  · exact lowerCert16 k ⟨by omega, h24⟩ hx
  by_cases h32 : k<32
  · exact lowerCert24 k ⟨by omega, h32⟩ hx
  by_cases h40 : k<40
  · exact lowerCert32 k ⟨by omega, h40⟩ hx
  by_cases h48 : k<48
  · exact lowerCert40 k ⟨by omega, h48⟩ hx
  by_cases h56 : k<56
  · exact lowerCert48 k ⟨by omega, h56⟩ hx
  by_cases h64 : k<64
  · exact lowerCert56 k ⟨by omega, h64⟩ hx
  by_cases h72 : k<72
  · exact lowerCert64 k ⟨by omega, h72⟩ hx
  by_cases h80 : k<80
  · exact lowerCert72 k ⟨by omega, h80⟩ hx
  by_cases h88 : k<88
  · exact lowerCert80 k ⟨by omega, h88⟩ hx
  by_cases h96 : k<96
  · exact lowerCert88 k ⟨by omega, h96⟩ hx
  by_cases h104 : k<104
  · exact lowerCert96 k ⟨by omega, h104⟩ hx
  by_cases h112 : k<112
  · exact lowerCert104 k ⟨by omega, h112⟩ hx
  by_cases h120 : k<120
  · exact lowerCert112 k ⟨by omega, h120⟩ hx
  by_cases h128 : k<128
  · exact lowerCert120 k ⟨by omega, h128⟩ hx
  by_cases h136 : k<136
  · exact lowerCert128 k ⟨by omega, h136⟩ hx
  by_cases h144 : k<144
  · exact lowerCert136 k ⟨by omega, h144⟩ hx
  by_cases h152 : k<152
  · exact lowerCert144 k ⟨by omega, h152⟩ hx
  by_cases h160 : k<160
  · exact lowerCert152 k ⟨by omega, h160⟩ hx
  by_cases h168 : k<168
  · exact lowerCert160 k ⟨by omega, h168⟩ hx
  by_cases h176 : k<176
  · exact lowerCert168 k ⟨by omega, h176⟩ hx
  by_cases h184 : k<184
  · exact lowerCert176 k ⟨by omega, h184⟩ hx
  by_cases h192 : k<192
  · exact lowerCert184 k ⟨by omega, h192⟩ hx
  exact lowerCert192 k ⟨by omega, hk⟩ hx

private lemma upperCert0 (k : ℕ) (hk : 0≤k ∧ k<8) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert8 (k : ℕ) (hk : 8≤k ∧ k<16) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert16 (k : ℕ) (hk : 16≤k ∧ k<24) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert24 (k : ℕ) (hk : 24≤k ∧ k<32) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert32 (k : ℕ) (hk : 32≤k ∧ k<40) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert40 (k : ℕ) (hk : 40≤k ∧ k<48) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert48 (k : ℕ) (hk : 48≤k ∧ k<56) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert56 (k : ℕ) (hk : 56≤k ∧ k<64) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert64 (k : ℕ) (hk : 64≤k ∧ k<72) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert72 (k : ℕ) (hk : 72≤k ∧ k<80) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert80 (k : ℕ) (hk : 80≤k ∧ k<88) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upperCert88 (k : ℕ) (hk : 88≤k ∧ k<96) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  rcases hk with ⟨hklo, hkhi⟩
  apply exp_upper_cert
  all_goals interval_cases k <;>
    norm_num [upperData, upperY, poly, err, Finset.sum_range_succ] at *

private lemma upper_certificate (k : ℕ) (hk : k<96) (hx : k≠8) :
    exp (-upperY k) ≤ upperData k := by
  by_cases h8 : k<8
  · exact upperCert0 k ⟨by omega, h8⟩ hx
  by_cases h16 : k<16
  · exact upperCert8 k ⟨by omega, h16⟩ hx
  by_cases h24 : k<24
  · exact upperCert16 k ⟨by omega, h24⟩ hx
  by_cases h32 : k<32
  · exact upperCert24 k ⟨by omega, h32⟩ hx
  by_cases h40 : k<40
  · exact upperCert32 k ⟨by omega, h40⟩ hx
  by_cases h48 : k<48
  · exact upperCert40 k ⟨by omega, h48⟩ hx
  by_cases h56 : k<56
  · exact upperCert48 k ⟨by omega, h56⟩ hx
  by_cases h64 : k<64
  · exact upperCert56 k ⟨by omega, h64⟩ hx
  by_cases h72 : k<72
  · exact upperCert64 k ⟨by omega, h72⟩ hx
  by_cases h80 : k<80
  · exact upperCert72 k ⟨by omega, h80⟩ hx
  by_cases h88 : k<88
  · exact upperCert80 k ⟨by omega, h88⟩ hx
  exact upperCert88 k ⟨by omega, hk⟩ hx

private lemma peak_upper (s : ℝ) (hs : 0<s) : kernel (1/2) s ≤ 1/4 := by
  have he : exp (-(7/5:ℝ)) ≤ 1/4 := by
    apply exp_upper_cert <;> norm_num [poly, err, Finset.sum_range_succ]
  apply le_trans _ he
  apply exp_le_exp.mpr
  have hp : (7/5:ℝ)*s ≤ s^2+1/2 := by nlinarith [sq_nonneg (s-7/10)]
  have := (le_div_iff₀ hs).mpr hp
  field_simp at this ⊢
  nlinarith

private lemma lower_cell (k : ℕ) (hk : k<200) (s : ℝ)
    (hs : s∈Ico ((k:ℝ)/25) (((k:ℝ)+1)/25)) : lowerData k ≤ kernel 1 s := by
  by_cases hk0 : k=0
  · subst k; norm_num [lowerData]; exact (exp_pos _).le
  have hp : 0<(k:ℝ)/25 := by exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)) (by norm_num)
  apply (lower_certificate k hk hk0).trans
  apply le_trans _ (kernel_lower 1 ((k:ℝ)/25) (((k:ℝ)+1)/25) s hp ⟨hs.1, hs.2.le⟩)
  apply le_min
  · apply exp_le_exp.mpr
    have := le_max_left ((k:ℝ)/25+1/((k:ℝ)/25)) (((k:ℝ)+1)/25+1/(((k:ℝ)+1)/25))
    dsimp [lowerY, kernel]
    linarith
  · apply exp_le_exp.mpr
    have := le_max_right ((k:ℝ)/25+1/((k:ℝ)/25)) (((k:ℝ)+1)/25+1/(((k:ℝ)+1)/25))
    dsimp [lowerY, kernel]
    linarith

private lemma upper_cell (k : ℕ) (hk : k<96) (s : ℝ) (hs0 : 0<s)
    (hs : s∈Ico ((k:ℝ)/12) (((k:ℝ)+1)/12)) : kernel (1/2) s ≤ upperData k := by
  by_cases hk8 : k=8
  · subst k
    convert peak_upper s hs0 using 1; norm_num [upperData]
  apply le_trans _ (upper_certificate k hk hk8)
  by_cases hk7 : k≤7
  · have hb : (((k:ℝ)+1)/12)^2 ≤ (1/2:ℝ) := by
      have : (k:ℝ)≤7 := by exact Nat.cast_le_ofNat.mpr hk7
      have := Nat.cast_nonneg (α := ℝ) k
      nlinarith [sq_nonneg ((k:ℝ)-7)]
    have hp : s*(((k:ℝ)+1)/12) ≤ (1/2:ℝ) := by
      have := mul_le_mul_of_nonneg_right hs.2.le (show 0≤((k:ℝ)+1)/12 by positivity)
      nlinarith
    have h := kernel_inc (1/2) s (((k:ℝ)+1)/12) hs0 hs.2.le hp
    convert h using 1
    simp only [upperY, ite_eq_left hk7, kernel]
    congr 1
    ring
  · have hk9 : 9≤k := by omega
    have ha : 0<(k:ℝ)/12 := by positivity
    have hp : (1/2:ℝ)≤((k:ℝ)/12)^2 := by
      have : 9≤(k:ℝ) := by exact Nat.ofNat_le_cast.mpr hk9
      nlinarith [sq_nonneg ((k:ℝ)-9)]
    have h := kernel_dec (1/2) ((k:ℝ)/12) s ha hs.1
      (hp.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) ha.le]))
    convert h using 1
    simp only [upperY, ite_eq_right hk7, kernel]
    congr 1
    ring

private lemma lowerSum0 : (∑ i∈Finset.range 8, lowerData (0+i)) = (40821/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum8 : (∑ i∈Finset.range 8, lowerData (8+i)) = (140009/250000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum16 : (∑ i∈Finset.range 8, lowerData (16+i)) = (1001311/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum24 : (∑ i∈Finset.range 8, lowerData (24+i)) = (529071/500000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum32 : (∑ i∈Finset.range 8, lowerData (32+i)) = (187031/200000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum40 : (∑ i∈Finset.range 8, lowerData (40+i)) = (769587/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum48 : (∑ i∈Finset.range 8, lowerData (48+i)) = (609471/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum56 : (∑ i∈Finset.range 8, lowerData (56+i)) = (471657/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum64 : (∑ i∈Finset.range 8, lowerData (64+i)) = (359589/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum72 : (∑ i∈Finset.range 8, lowerData (72+i)) = (67839/250000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum80 : (∑ i∈Finset.range 8, lowerData (80+i)) = (203283/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum88 : (∑ i∈Finset.range 8, lowerData (88+i)) = (151463/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum96 : (∑ i∈Finset.range 8, lowerData (96+i)) = (28097/250000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum104 : (∑ i∈Finset.range 8, lowerData (104+i)) = (8313/100000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum112 : (∑ i∈Finset.range 8, lowerData (112+i)) = (6133/100000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum120 : (∑ i∈Finset.range 8, lowerData (120+i)) = (9031/200000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum128 : (∑ i∈Finset.range 8, lowerData (128+i)) = (3319/100000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum136 : (∑ i∈Finset.range 8, lowerData (136+i)) = (24361/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum144 : (∑ i∈Finset.range 8, lowerData (144+i)) = (17861/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum152 : (∑ i∈Finset.range 8, lowerData (152+i)) = (13081/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum160 : (∑ i∈Finset.range 8, lowerData (160+i)) = (2393/250000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum168 : (∑ i∈Finset.range 8, lowerData (168+i)) = (6999/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum176 : (∑ i∈Finset.range 8, lowerData (176+i)) = (639/125000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum184 : (∑ i∈Finset.range 8, lowerData (184+i)) = (3733/1000000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lowerSum192 : (∑ i∈Finset.range 8, lowerData (192+i)) = (109/40000:ℝ) := by
  norm_num [Finset.sum_range_succ, lowerData]

private lemma lower_sum : (2731/10000:ℝ) ≤ (1/25)*∑ k∈Finset.range 200, lowerData k := by
  rw [Finset.sum_range_add (n := 192) (m := 8), lowerSum192]
  rw [Finset.sum_range_add (n := 184) (m := 8), lowerSum184]
  rw [Finset.sum_range_add (n := 176) (m := 8), lowerSum176]
  rw [Finset.sum_range_add (n := 168) (m := 8), lowerSum168]
  rw [Finset.sum_range_add (n := 160) (m := 8), lowerSum160]
  rw [Finset.sum_range_add (n := 152) (m := 8), lowerSum152]
  rw [Finset.sum_range_add (n := 144) (m := 8), lowerSum144]
  rw [Finset.sum_range_add (n := 136) (m := 8), lowerSum136]
  rw [Finset.sum_range_add (n := 128) (m := 8), lowerSum128]
  rw [Finset.sum_range_add (n := 120) (m := 8), lowerSum120]
  rw [Finset.sum_range_add (n := 112) (m := 8), lowerSum112]
  rw [Finset.sum_range_add (n := 104) (m := 8), lowerSum104]
  rw [Finset.sum_range_add (n := 96) (m := 8), lowerSum96]
  rw [Finset.sum_range_add (n := 88) (m := 8), lowerSum88]
  rw [Finset.sum_range_add (n := 80) (m := 8), lowerSum80]
  rw [Finset.sum_range_add (n := 72) (m := 8), lowerSum72]
  rw [Finset.sum_range_add (n := 64) (m := 8), lowerSum64]
  rw [Finset.sum_range_add (n := 56) (m := 8), lowerSum56]
  rw [Finset.sum_range_add (n := 48) (m := 8), lowerSum48]
  rw [Finset.sum_range_add (n := 40) (m := 8), lowerSum40]
  rw [Finset.sum_range_add (n := 32) (m := 8), lowerSum32]
  rw [Finset.sum_range_add (n := 24) (m := 8), lowerSum24]
  rw [Finset.sum_range_add (n := 16) (m := 8), lowerSum16]
  rw [Finset.sum_range_add (n := 8) (m := 8), lowerSum8]
  rw [show (∑ i∈Finset.range 8, lowerData i) = ∑ i∈Finset.range 8, lowerData (0+i) by simp only [zero_add], lowerSum0]
  norm_num

private lemma witness_lower : (2731/10000:ℝ) ≤ survival 1 1 1 1 := by
  rw [survival_mix 1 (by norm_num)]
  have h := grid_integral_lower 1 (1/25) (by norm_num) (by norm_num) 200 lowerData
    (by intro k hk s hs; apply lower_cell k hk s; simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using hs)
  have hn := lower_sum
  apply hn.trans (h.trans _)
  norm_num only [Nat.cast_ofNat, mul_one_div, div_self] at *
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤8)]
  apply setIntegral_mono_set (kernel_integrable 1 (by norm_num))
    (Filter.Eventually.of_forall (fun s => (exp_nonneg _)))
  exact Filter.Eventually.of_forall (fun s hs => hs.1)

private lemma witness_upper : survival 1 1 1 (1/2) ≤ (467/1000:ℝ) := by
  rw [survival_mix (1/2) (by norm_num)]
  have h := grid_integral_upper (1/2) (1/12) (by norm_num) (by norm_num) 96 upperData
    (by intro k hk s hs hs0; apply upper_cell k hk s hs0; simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using hs)
  have hn : (1/12)*∑ k∈Finset.range 96, upperData k ≤ (466/1000:ℝ) := by
    norm_num [Finset.sum_range_succ, upperData]
  have ht : (∫ s in Ioi (8:ℝ), kernel (1/2) s) ≤ (1/1000:ℝ) := by
    have he : exp (-(8:ℝ)) ≤ 1/1000 := by
      apply exp_upper_cert <;> norm_num [poly, err, Finset.sum_range_succ]
    apply le_trans _ he
    rw [← integral_exp_neg_Ioi 8]
    apply setIntegral_mono_on
      ((kernel_integrable (1/2) (by norm_num)).mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤8)))
      (integrableOn_exp_neg_Ioi 8) measurableSet_Ioi
    intro s hs
    apply exp_le_exp.mpr
    have := div_nonneg (by norm_num : (0:ℝ)≤1/2) (show 0≤s from le_trans (by norm_num) hs.le)
    linarith
  have hi := intervalIntegral.integral_interval_add_Ioi (a := (0:ℝ)) (b := (8:ℝ))
    (kernel_integrable (1/2) (by norm_num))
    ((kernel_integrable (1/2) (by norm_num)).mono_set (Ioi_subset_Ioi (by norm_num)))
  norm_num at h
  linarith [h.trans hn]

theorem result : ¬ claim := by
  intro hc
  have h := hc 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (1/2) (1/2) (by norm_num) (by norm_num)
  have hl := witness_lower
  have hu := witness_upper
  have hp : 0 ≤ survival 1 1 1 (1/2) := by
    rw [survival_mix (1/2) (by norm_num)]
    exact integral_nonneg (fun s => exp_nonneg _)
  norm_num at h
  nlinarith
end D5.S3.Analytic.GammaGammaNBU.Result

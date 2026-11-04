/- GID: D5/S3/Weil/ZetaGamma/FormCore/PositiveHankelL2
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-positive-halfline-Hankel-domain)
   anchors: []
   utility: none
   digest: Actual half-line L2 Hankel domains, complete positive Laplace-square series, and the quarter-rate pi Schur bound. -/


import D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Actual positive half-line Hankel domains

The independent Carleman supplier is imported from its own owner.
The remaining private Hankel suppliers and their consumers live here.
The actual complex L2 inputs need no trace or compact-support condition.
The full positive Laplace-square series holds for every k>0, and the pi
upper bound holds for k>=1/4. No Gamma/Fourier or full-energy identity is
introduced by these integral domain and Schur estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2
open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open scoped ENNReal Topology

abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

private theorem positive_pair_ae :
    ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline, 0 < z.1 ∧ 0 < z.2 := by
  rw [halfline, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

def positiveHankelKernel (k x : ℝ) : ℝ :=
  Real.exp (-k * x) / (1 - Real.exp (-x))

private theorem hankel_kernel_le {k x : ℝ} (hk : (1 / 2 : ℝ) ≤ k) (hx : 0 < x) :
    0 ≤ positiveHankelKernel k x ∧ positiveHankelKernel k x ≤ x⁻¹ := by
  have hden : 0 < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (by linarith : -x < 0)
    linarith
  have hbase : x * Real.exp (-x / 2) ≤ 1 - Real.exp (-x) := by
    have hs : x / 2 ≤ Real.sinh (x / 2) :=
      Real.self_le_sinh_iff.mpr (by positivity)
    rw [Real.sinh_eq] at hs
    have hcancel : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
      rw [← Real.exp_add]
      have : x / 2 + -x / 2 = 0 := by ring
      rw [this, Real.exp_zero]
    have hsquare : Real.exp (-(x / 2)) * Real.exp (-x / 2) = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (x / 2) * (2 * Real.exp (-x / 2)) := by ring
      _ ≤ ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) *
          (2 * Real.exp (-x / 2)) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = Real.exp (x / 2) * Real.exp (-x / 2) -
          Real.exp (-(x / 2)) * Real.exp (-x / 2) := by ring
      _ = _ := by rw [hcancel, hsquare]
  have hexp : Real.exp (-k * x) ≤ Real.exp (-x / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine ⟨by unfold positiveHankelKernel; positivity, ?_⟩
  unfold positiveHankelKernel
  calc
    _ ≤ Real.exp (-x / 2) / (1 - Real.exp (-x)) :=
      div_le_div_of_nonneg_right hexp hden.le
    _ ≤ x⁻¹ := by
      apply (div_le_iff₀ hden).2
      have hdiv : Real.exp (-x / 2) ≤ (1 - Real.exp (-x)) / x :=
        (le_div_iff₀ hx).2 (by simpa only [mul_comm] using hbase)
      simpa only [div_eq_mul_inv, mul_comm] using hdiv

def hankelAbsolute (k : ℝ) (u : ℝ → ℂ) (z : ℝ × ℝ) : ℝ :=
  positiveHankelKernel k (z.1 + z.2) * (‖u z.1‖ * ‖u z.2‖)

def hankelIntegrand (k : ℝ) (u : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (positiveHankelKernel k (z.1 + z.2) : ℂ) * ((starRingEnd ℂ) (u z.1) * u z.2)

def actualHankel (k : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ z : ℝ × ℝ, hankelIntegrand k u z ∂halfline.prod halfline

def literalLaplace (a : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ s : ℝ, (Real.exp (-a * s) : ℂ) * u s ∂halfline

private theorem hankel_actual_absolute_domain {k : ℝ} (hk : (1 / 2 : ℝ) ≤ k)
    (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (hankelAbsolute k u) (halfline.prod halfline) ∧
    Integrable (hankelIntegrand k u) (halfline.prod halfline) ∧
    (∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline) ≤
      Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  obtain ⟨hc, hcb⟩ := carleman_actual_l2_domain u hu
  have hmK : Measurable (fun z : ℝ × ℝ => positiveHankelKernel k (z.1 + z.2)) := by
    unfold positiveHankelKernel
    fun_prop
  have hmA : AEStronglyMeasurable (hankelAbsolute k u) (halfline.prod halfline) :=
    hmK.aestronglyMeasurable.mul (hu.aestronglyMeasurable.comp_fst.norm.mul
      hu.aestronglyMeasurable.comp_snd.norm)
  have hmC : AEStronglyMeasurable (hankelIntegrand k u) (halfline.prod halfline) :=
    hmK.complex_ofReal.aestronglyMeasurable.mul
      ((Complex.continuous_conj.comp_aestronglyMeasurable
        hu.aestronglyMeasurable.comp_fst).mul hu.aestronglyMeasurable.comp_snd)
  have hnorm : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline,
      ‖hankelIntegrand k u z‖ = hankelAbsolute k u z := by
    filter_upwards [positive_pair_ae] with z hz
    have hK := (hankel_kernel_le hk (add_pos hz.1 hz.2)).1
    simp only [hankelIntegrand, hankelAbsolute, norm_mul, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  have hle : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline,
      hankelAbsolute k u z ≤ carlemanAbsolute u z := by
    filter_upwards [positive_pair_ae] with z hz
    have h := mul_le_mul_of_nonneg_right
      (hankel_kernel_le hk (add_pos hz.1 hz.2)).2
        (mul_nonneg (norm_nonneg (u z.1)) (norm_nonneg (u z.2)))
    simpa only [hankelAbsolute, carlemanAbsolute, div_eq_mul_inv, mul_comm] using h
  have hiA : Integrable (hankelAbsolute k u) (halfline.prod halfline) := by
    apply hc.mono' hmA
    filter_upwards [positive_pair_ae, hle] with z hz h
    have hznonneg : 0 ≤ hankelAbsolute k u z := by
      dsimp only [hankelAbsolute]
      exact mul_nonneg (hankel_kernel_le hk (add_pos hz.1 hz.2)).1
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_of_nonneg hznonneg]
    exact h
  have hiC : Integrable (hankelIntegrand k u) (halfline.prod halfline) :=
    hiA.mono' hmC (hnorm.mono fun _ h => h.le)
  exact ⟨hiA, hiC, (integral_mono_ae hiA hc hle).trans hcb⟩

private theorem exponential_hankel_series {k x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-(k + n) * x)) (positiveHankelKernel k x) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_lt_exp.mpr (by linarith : -x < 0)
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-k * x))
  have hterm (n : ℕ) : Real.exp (-(k + n) * x) =
      Real.exp (-k * x) * Real.exp (-x) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  simpa only [← hterm, positiveHankelKernel, div_eq_mul_inv] using h

private def laplacePairTerm (k : ℝ) (u : ℝ → ℂ) (n : ℕ) (z : ℝ × ℝ) : ℂ :=
  (Real.exp (-(k + n) * (z.1 + z.2)) : ℂ) * ((starRingEnd ℂ) (u z.1) * u z.2)

private theorem laplace_pair_integral (k : ℝ) (u : ℝ → ℂ) (n : ℕ) :
    (∫ z : ℝ × ℝ, laplacePairTerm k u n z ∂halfline.prod halfline) =
      (Complex.normSq (literalLaplace (k + n) u) : ℂ) := by
  have heq : laplacePairTerm k u n = fun z : ℝ × ℝ =>
      (starRingEnd ℂ) ((Real.exp (-(k + n) * z.1) : ℂ) * u z.1) *
        ((Real.exp (-(k + n) * z.2) : ℂ) * u z.2) := by
    funext z
    have he : Real.exp (-(k + n) * (z.1 + z.2)) =
        Real.exp (-(k + n) * z.1) * Real.exp (-(k + n) * z.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [laplacePairTerm, map_mul, Complex.conj_ofReal, he, Complex.ofReal_mul]
    ring
  calc
    _ = (∫ s : ℝ, (starRingEnd ℂ)
          ((Real.exp (-(k + n) * s) : ℂ) * u s) ∂halfline) *
        (∫ t : ℝ, (Real.exp (-(k + n) * t) : ℂ) * u t ∂halfline) := by
      rw [heq]
      exact integral_prod_mul
        (fun s : ℝ => (starRingEnd ℂ) ((Real.exp (-(k + n) * s) : ℂ) * u s))
        (fun t : ℝ => (Real.exp (-(k + n) * t) : ℂ) * u t)
    _ = _ := by
      rw [integral_conj]
      change (starRingEnd ℂ) (literalLaplace (k + n) u) *
          literalLaplace (k + n) u =
        (Complex.normSq (literalLaplace (k + n) u) : ℂ)
      exact (Complex.normSq_eq_conj_mul_self (z := literalLaplace (k + n) u)).symm

/-- Complete actual L2 Hankel domain and positive Laplace-square series.
The required absolute convergence is a conclusion supplied by Schur's test. -/
theorem positive_hankel_actual_l2_domain {k : ℝ} (hk : (1 / 2 : ℝ) ≤ k)
    (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (hankelAbsolute k u) (halfline.prod halfline) ∧
    (∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline) ≤
      Real.pi * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) ∧
    Integrable (hankelIntegrand k u) (halfline.prod halfline) ∧
    (∀ n : ℕ, Integrable (fun s : ℝ => (Real.exp (-(k + n) * s) : ℂ) * u s) halfline) ∧
    Summable (fun n : ℕ => Complex.normSq (literalLaplace (k + n) u)) ∧
    actualHankel k u = ((∑' n : ℕ, Complex.normSq (literalLaplace (k + n) u)) : ℂ) ∧
    0 ≤ (actualHankel k u).re ∧ (actualHankel k u).im = 0 ∧
    (actualHankel k u).re ≤ Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  obtain ⟨hAi, hHi, hAbound⟩ := hankel_actual_absolute_domain hk u hu
  have hL (n : ℕ) : Integrable (fun s : ℝ => (Real.exp (-(k + n) * s) : ℂ) * u s) halfline := by
    simpa only [zero_add] using
      (right_exponential_tail_l2_integrable_and_sq_le
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith : 0 < k + n)
        u hu 0 le_rfl).1
  let bound : ℕ → ℝ × ℝ → ℝ := fun n z =>
    Real.exp (-(k + n) * (z.1 + z.2)) * (‖u z.1‖ * ‖u z.2‖)
  have hpoint : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline,
      HasSum (fun n => bound n z) (hankelAbsolute k u z) := by
    filter_upwards [positive_pair_ae] with z hz
    exact (exponential_hankel_series (k := k) (add_pos hz.1 hz.2)).mul_right _
  have hbi : Integrable (fun z => ∑' n : ℕ, bound n z) (halfline.prod halfline) :=
    hAi.congr (hpoint.mono fun _ h => h.tsum_eq.symm)
  have hFm (n : ℕ) : AEStronglyMeasurable (laplacePairTerm k u n)
      (halfline.prod halfline) := by
    have hm : Measurable (fun z : ℝ × ℝ =>
        (Real.exp (-(k + n) * (z.1 + z.2)) : ℂ)) := by fun_prop
    exact hm.aestronglyMeasurable.mul
      ((Complex.continuous_conj.comp_aestronglyMeasurable
        hu.aestronglyMeasurable.comp_fst).mul hu.aestronglyMeasurable.comp_snd)
  have hFnorm (n : ℕ) : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline,
      ‖laplacePairTerm k u n z‖ ≤ bound n z := by
    exact Eventually.of_forall fun z => by
      simp only [laplacePairTerm, bound, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]
  have hFsum : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline,
      HasSum (fun n => laplacePairTerm k u n z) (hankelIntegrand k u z) := by
    filter_upwards [positive_pair_ae] with z hz
    have h := Complex.ofRealCLM.hasSum
      (exponential_hankel_series (k := k) (add_pos hz.1 hz.2))
    simpa only [Complex.ofRealCLM_apply, laplacePairTerm, hankelIntegrand] using
      h.mul_right ((starRingEnd ℂ) (u z.1) * u z.2)
  have hS := hasSum_integral_of_dominated_convergence bound hFm hFnorm
    (hpoint.mono fun _ h => h.summable) hbi hFsum
  simp_rw [laplace_pair_integral] at hS
  change HasSum (fun n : ℕ => (Complex.normSq (literalLaplace (k + n) u) : ℂ))
    (actualHankel k u) at hS
  have hSR : HasSum (fun n : ℕ => Complex.normSq (literalLaplace (k + n) u))
      (actualHankel k u).re := by
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum hS
  have hreal : actualHankel k u = ((actualHankel k u).re : ℂ) :=
    hS.unique (Complex.ofRealCLM.hasSum hSR)
  have hnonneg : 0 ≤ (actualHankel k u).re := by
    rw [← hSR.tsum_eq]
    exact tsum_nonneg (fun _ => Complex.normSq_nonneg _)
  have him : (actualHankel k u).im = 0 := by
    rw [hreal]
    exact Complex.ofReal_im _
  have hupper : (actualHankel k u).re ≤
      Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
    calc
      _ ≤ ‖actualHankel k u‖ := Complex.re_le_norm _
      _ ≤ ∫ z : ℝ × ℝ, ‖hankelIntegrand k u z‖ ∂halfline.prod halfline :=
        norm_integral_le_integral_norm _
      _ = ∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline := by
        apply integral_congr_ae
        filter_upwards [positive_pair_ae] with z hz
        simp only [hankelIntegrand, hankelAbsolute, norm_mul, Complex.norm_conj,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hankel_kernel_le hk (add_pos hz.1 hz.2)).1]
      _ ≤ _ := hAbound
  refine ⟨hAi, hAbound, hHi, hL, hSR.summable, ?_, hnonneg, him, hupper⟩
  rw [← Complex.ofReal_tsum
    (fun n : ℕ => Complex.normSq (literalLaplace (k + n) u)), hSR.tsum_eq]
  exact hreal

private theorem positive_hankel_kernel_split {k x : ℝ} (hx : 0 < x) :
    positiveHankelKernel k x =
      Real.exp (-k * x) + positiveHankelKernel (k + 1) x := by
  have hd : 1 - Real.exp (-x) ≠ 0 := by
    have h : Real.exp (-x) < 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (by linarith : -x < 0)
    linarith
  have he : Real.exp (-(k + 1) * x) =
      Real.exp (-k * x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold positiveHankelKernel
  rw [he]
  field_simp [hd]
  <;> ring

private theorem positive_hankel_rank_domain {k : ℝ} (hk : 0 < k)
    (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    let a : ℝ → ℝ := fun s => Real.exp (-k * s) * ‖u s‖
    Integrable (fun z : ℝ × ℝ => a z.1 * a z.2) (halfline.prod halfline) ∧
    Integrable (laplacePairTerm k u 0) (halfline.prod halfline) ∧
    (∫ z : ℝ × ℝ, a z.1 * a z.2 ∂halfline.prod halfline) ≤
      (1 / (2 * k)) * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  dsimp only
  let a : ℝ → ℝ := fun s => Real.exp (-k * s) * ‖u s‖
  let w : ℝ → ℂ := fun s => (‖u s‖ : ℂ)
  have hw : MemLp w 2 halfline := hu.norm.ofReal
  have hW := right_exponential_tail_l2_integrable_and_sq_le hk w hw 0 le_rfl
  simp only [zero_add] at hW
  have hn (s : ℝ) :
      ‖(Real.exp (-k * s) : ℂ) * w s‖ = a s := by
    simp only [w, a, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (norm_nonneg _)]
  have ha : Integrable a halfline := hW.1.norm.congr (Eventually.of_forall hn)
  have hR : Integrable (fun z : ℝ × ℝ => a z.1 * a z.2)
      (halfline.prod halfline) := ha.mul_prod ha
  have hmeas : AEStronglyMeasurable (laplacePairTerm k u 0)
      (halfline.prod halfline) := by
    have hExp : Measurable (fun z : ℝ × ℝ =>
        (Real.exp (-(k + (0 : ℕ)) * (z.1 + z.2)) : ℂ)) := by fun_prop
    exact hExp.aestronglyMeasurable.mul
      ((Complex.continuous_conj.comp_aestronglyMeasurable
        hu.aestronglyMeasurable.comp_fst).mul hu.aestronglyMeasurable.comp_snd)
  have hnorm (z : ℝ × ℝ) :
      ‖laplacePairTerm k u 0 z‖ = a z.1 * a z.2 := by
    have he : Real.exp (-k * (z.1 + z.2)) =
        Real.exp (-k * z.1) * Real.exp (-k * z.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [laplacePairTerm, Nat.cast_zero, add_zero, norm_mul,
      Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), he, a]
    ring
  have hIR : Integrable (laplacePairTerm k u 0) (halfline.prod halfline) :=
    hR.mono' hmeas (Eventually.of_forall fun z => (hnorm z).le)
  have hLap : rightExponentialTail k w 0 =
      Complex.ofReal (∫ s : ℝ, a s ∂halfline) := by
    calc
      _ = ∫ s : ℝ, (a s : ℂ) ∂halfline := by
        unfold rightExponentialTail
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          simp only [zero_add, w, a, Complex.ofReal_mul]
      _ = Complex.ofReal (∫ s : ℝ, a s ∂halfline) := integral_complex_ofReal
  have hmass : (∫ s : ℝ, a s ∂halfline) ^ 2 ≤
      (1 / (2 * k)) * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
    simpa only [hLap, w, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), sq_abs] using hW.2
  refine ⟨hR, hIR, ?_⟩
  calc
    _ = (∫ s : ℝ, a s ∂halfline) ^ 2 := by
      simpa only [pow_two, a] using
        (integral_prod_mul (μ := halfline) (ν := halfline) a a)
    _ ≤ _ := hmass

/-- Every positive rate, including the actual quarter rate, has its
literal half-line L2 Hankel domain and complete positive Laplace-square
series. The first exponential is a paid rank-one form and the remaining
kernel has rate k+1 >= 1/2, where the Carleman estimate applies. -/
theorem positive_hankel_actual_l2_domain_all_positive_rates
    {k : ℝ} (hk : 0 < k) (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (hankelAbsolute k u) (halfline.prod halfline) ∧
    (∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline) ≤
      (Real.pi + 1 / (2 * k)) * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) ∧
    Integrable (hankelIntegrand k u) (halfline.prod halfline) ∧
    (∀ n : ℕ, Integrable (fun s : ℝ => (Real.exp (-(k + n) * s) : ℂ) * u s) halfline) ∧
    Summable (fun n : ℕ => Complex.normSq (literalLaplace (k + n) u)) ∧
    actualHankel k u = ((∑' n : ℕ, Complex.normSq (literalLaplace (k + n) u)) : ℂ) ∧
    0 ≤ (actualHankel k u).re ∧ (actualHankel k u).im = 0 ∧
    (actualHankel k u).re ≤
      (Real.pi + 1 / (2 * k)) * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  obtain ⟨hAT, hATbound, hIT, hLT, hST, hHT, hTnonneg, hTim, hTupper⟩ :=
    positive_hankel_actual_l2_domain (k := k + 1) (by linarith) u hu
  obtain ⟨hR, hIR, hRbound⟩ := positive_hankel_rank_domain hk u hu
  let a : ℝ → ℝ := fun s => Real.exp (-k * s) * ‖u s‖
  have hAbs : (fun z : ℝ × ℝ => hankelAbsolute k u z) =ᵐ[halfline.prod halfline]
      (fun z => a z.1 * a z.2 + hankelAbsolute (k + 1) u z) := by
    filter_upwards [positive_pair_ae] with z hz
    have he : Real.exp (-k * (z.1 + z.2)) =
        Real.exp (-k * z.1) * Real.exp (-k * z.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [hankelAbsolute, a]
    rw [positive_hankel_kernel_split (add_pos hz.1 hz.2), he]
    ring
  have hComp : (fun z : ℝ × ℝ => hankelIntegrand k u z) =ᵐ[halfline.prod halfline]
      (fun z => laplacePairTerm k u 0 z + hankelIntegrand (k + 1) u z) := by
    filter_upwards [positive_pair_ae] with z hz
    dsimp only [hankelIntegrand, laplacePairTerm]
    rw [positive_hankel_kernel_split (add_pos hz.1 hz.2)]
    push_cast
    simp only [Nat.cast_zero, add_zero]
    ring
  have hAi : Integrable (hankelAbsolute k u) (halfline.prod halfline) :=
    (hR.add hAT).congr hAbs.symm
  have hHi : Integrable (hankelIntegrand k u) (halfline.prod halfline) :=
    (hIR.add hIT).congr hComp.symm
  have hAbound : (∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline) ≤
      (Real.pi + 1 / (2 * k)) * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
    rw [integral_congr_ae hAbs, integral_add hR hAT]
    calc
      _ ≤ (1 / (2 * k)) * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) +
          Real.pi * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) :=
        add_le_add hRbound hATbound
      _ = _ := by ring
  have hHd : actualHankel k u =
      (Complex.normSq (literalLaplace k u) : ℂ) + actualHankel (k + 1) u := by
    unfold actualHankel
    rw [integral_congr_ae hComp, integral_add hIR hIT, laplace_pair_integral]
    simp only [Nat.cast_zero, add_zero]
  have hL (n : ℕ) : Integrable
      (fun s : ℝ => (Real.exp (-(k + n) * s) : ℂ) * u s) halfline := by
    simpa only [zero_add] using
      (right_exponential_tail_l2_integrable_and_sq_le
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith : 0 < k + n)
        u hu 0 le_rfl).1
  let f : ℕ → ℝ := fun n => Complex.normSq (literalLaplace (k + n) u)
  have hshift (n : ℕ) : f (n + 1) =
      Complex.normSq (literalLaplace ((k + 1) + n) u) := by
    dsimp only [f]
    congr 2
    push_cast
    ring
  have hs : Summable f := (summable_nat_add_iff 1).mp (by
    simpa only [hshift] using hST)
  have hsum : (∑' n : ℕ, f n) =
      Complex.normSq (literalLaplace k u) +
        ∑' n : ℕ, Complex.normSq (literalLaplace ((k + 1) + n) u) := by
    rw [hs.tsum_eq_zero_add]
    have hzero : f 0 = Complex.normSq (literalLaplace k u) := by
      simp only [f, Nat.cast_zero, add_zero]
    rw [hzero]
    congr 1
    exact tsum_congr hshift
  have hHreal : actualHankel k u = Complex.ofReal (∑' n : ℕ, f n) := by
    rw [hHd, hHT,
      ← Complex.ofReal_tsum
        (fun n : ℕ => Complex.normSq (literalLaplace ((k + 1) + n) u)),
      hsum, Complex.ofReal_add]
  have hH : actualHankel k u = ((∑' n : ℕ, f n) : ℂ) :=
    hHreal.trans (Complex.ofReal_tsum f)
  have hnonneg : 0 ≤ (actualHankel k u).re := by
    rw [hHreal, Complex.ofReal_re]
    exact tsum_nonneg fun n => Complex.normSq_nonneg _
  have him : (actualHankel k u).im = 0 := by rw [hHreal, Complex.ofReal_im]
  have hupper : (actualHankel k u).re ≤
      (Real.pi + 1 / (2 * k)) * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
    calc
      _ = Complex.normSq (literalLaplace k u) + (actualHankel (k + 1) u).re := by
        rw [hHd, Complex.add_re, Complex.ofReal_re]
      _ ≤ (1 / (2 * k)) * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) +
          Real.pi * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) := by
        apply add_le_add _ hTupper
        have hb := (right_exponential_tail_l2_integrable_and_sq_le hk u hu 0 le_rfl).2
        simpa only [← Complex.normSq_eq_norm_sq, literalLaplace,
          rightExponentialTail, zero_add] using hb
      _ = _ := by ring
  exact ⟨hAi, hAbound, hHi, hL, hs, hH, hnonneg, him, hupper⟩

/- Actual parameter: k=1/4 gives bound (pi+2)*||u||_2^2 and every
Laplace rate 1/4+n>0. This supplies domain/positivity for the literal
Hankel kernel only; an independent Fourier/digamma/even-extension identity
is still required before applying it to an original Gamma energy. -/

private def quarterSchurWeight (s : ℝ) : ℝ :=
  Real.exp (-s / 4) / Real.sqrt (1 - Real.exp (-s))

private theorem quarter_schur_weight_pos {s : ℝ} (hs : 0 < s) :
    0 < quarterSchurWeight s := by
  have he : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by linarith))

private def quarterCauchy (b q : ℝ) : ℝ := (q ^ 2 + b ^ 2)⁻¹

private theorem quarter_cauchy_domain {b : ℝ} (hb : 0 < b) :
    Integrable (quarterCauchy b) halfline ∧
      (∫ q : ℝ, quarterCauchy b q ∂halfline) = Real.pi / (2 * b) := by
  have hscale (q : ℝ) :
      quarterCauchy b (b * q) = b⁻¹ ^ 2 * (1 + q ^ 2)⁻¹ := by
    unfold quarterCauchy
    field_simp [hb.ne', show (b * q) ^ 2 + b ^ 2 ≠ 0 by positivity,
      show 1 + q ^ 2 ≠ 0 by positivity]
    <;> ring
  have hbase : Integrable (fun q : ℝ => (1 + q ^ 2)⁻¹) halfline :=
    integrable_inv_one_add_sq.integrableOn
  have hscaled : IntegrableOn (fun q : ℝ => quarterCauchy b (b * q)) (Ioi 0) := by
    change Integrable _ halfline
    apply (hbase.const_mul (b⁻¹ ^ 2)).congr
    exact Eventually.of_forall fun q => (hscale q).symm
  have hi : Integrable (quarterCauchy b) halfline := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (quarterCauchy b) 0 hb).1 hscaled
    simpa only [mul_zero, IntegrableOn, halfline] using h
  refine ⟨hi, ?_⟩
  calc
    _ = b * ∫ q : ℝ in Ioi 0, quarterCauchy b (b * q) := by
      simpa only [mul_zero, smul_eq_mul] using
        (integral_comp_mul_left_Ioi' (quarterCauchy b) 0 hb).symm
    _ = b * (b⁻¹ ^ 2 * (Real.pi / 2)) := by
      simp_rw [hscale]
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
      simp only [Real.arctan_zero, sub_zero]
    _ = _ := by
      field_simp [hb.ne']
      <;> ring

private def quarterSchurChange (q : ℝ) : ℝ := Real.log (1 + q ^ 2)

private def quarterSchurChangeDeriv (q : ℝ) : ℝ := 2 * q / (1 + q ^ 2)

private theorem quarter_schur_change_deriv (q : ℝ) :
    HasDerivAt quarterSchurChange (quarterSchurChangeDeriv q) q := by
  have hbase : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * q) q := by
    simpa using (hasDerivAt_pow 2 q).const_add (1 : ℝ)
  exact hbase.log (by positivity)

private theorem quarter_schur_change_pos {q : ℝ} (hq : 0 < q) :
    0 < quarterSchurChange q := by
  unfold quarterSchurChange
  exact Real.log_pos (by nlinarith [sq_pos_of_pos hq])

private theorem quarter_schur_change_image :
    quarterSchurChange '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext s
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact quarter_schur_change_pos hq
  · intro hs
    have he : 0 < Real.exp s - 1 := by
      have := Real.one_lt_exp_iff.mpr hs
      linarith
    refine ⟨Real.sqrt (Real.exp s - 1), Real.sqrt_pos.2 he, ?_⟩
    rw [quarterSchurChange, Real.sq_sqrt he.le]
    rw [show 1 + (Real.exp s - 1) = Real.exp s by ring, Real.log_exp]

private theorem quarter_schur_change_inj :
    InjOn quarterSchurChange (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have he := congrArg Real.exp hxy
  simp only [quarterSchurChange, Real.exp_log (by positivity : 0 < 1 + x ^ 2),
    Real.exp_log (by positivity : 0 < 1 + y ^ 2)] at he
  have hs : x ^ 2 = y ^ 2 := by linarith
  have hroot := congrArg Real.sqrt hs
  simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hx, abs_of_pos hy] using hroot

private theorem quarter_hankel_row_product (t s : ℝ) :
    positiveHankelKernel (1 / 4) (t + s) * quarterSchurWeight s =
      Real.exp (-t / 4) * Real.exp (-s / 2) /
        ((1 - Real.exp (-t) * Real.exp (-s)) * Real.sqrt (1 - Real.exp (-s))) := by
  have he : Real.exp (-(1 / 4 : ℝ) * (t + s)) * Real.exp (-s / 4) =
      Real.exp (-t / 4) * Real.exp (-s / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he' : Real.exp (-(t + s)) = Real.exp (-t) * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold positiveHankelKernel quarterSchurWeight
  rw [he', div_mul_div_comm, he]

/-- Exact transformed row, including the Jacobian. This is the nontrivial
normalization step: q=sqrt(exp(s)-1), equivalently s=log(1+q^2). -/
private theorem quarter_schur_row_substitution {t q : ℝ} (ht : 0 < t) (hq : 0 < q) :
    |quarterSchurChangeDeriv q| •
      (positiveHankelKernel (1 / 4) (t + quarterSchurChange q) *
        quarterSchurWeight (quarterSchurChange q)) =
      2 * Real.exp (-t / 4) / (q ^ 2 + (1 - Real.exp (-t))) := by
  have hQ : 0 < 1 + q ^ 2 := by positivity
  have he : Real.exp (-quarterSchurChange q) = (1 + q ^ 2)⁻¹ := by
    rw [quarterSchurChange, Real.exp_neg, Real.exp_log hQ]
  have hhalf : Real.exp (-quarterSchurChange q / 2) =
      (Real.sqrt (1 + q ^ 2))⁻¹ := by
    rw [Real.exp_half, he, Real.sqrt_inv]
  have hfrac : 1 - (1 + q ^ 2)⁻¹ = q ^ 2 / (1 + q ^ 2) := by
    field_simp [hQ.ne']
    <;> ring
  have hsqrt : Real.sqrt (1 - Real.exp (-quarterSchurChange q)) =
      q / Real.sqrt (1 + q ^ 2) := by
    rw [he, hfrac, Real.sqrt_div (sq_nonneg q), Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hA : 0 < 1 - Real.exp (-t) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0)
    linarith
  have hnormalizedDen : 1 + q ^ 2 - Real.exp (-t) ≠ 0 := by
    have hpos : 0 < 1 + q ^ 2 - Real.exp (-t) := by
      linarith [sq_nonneg q]
    exact hpos.ne'
  have hden : 1 - Real.exp (-t) * (1 + q ^ 2)⁻¹ ≠ 0 := by
    have hlt : Real.exp (-t) * Real.exp (-quarterSchurChange q) < 1 := by
      rw [← Real.exp_add, Real.exp_lt_one_iff]
      linarith [quarter_schur_change_pos hq]
    rw [he] at hlt
    exact (sub_pos.mpr hlt).ne'
  have hd : 0 < quarterSchurChangeDeriv q := by
    unfold quarterSchurChangeDeriv
    positivity
  rw [abs_of_pos hd, smul_eq_mul, quarter_hankel_row_product, hhalf, hsqrt, he]
  unfold quarterSchurChangeDeriv
  field_simp [hq.ne', hQ.ne', (Real.sqrt_pos.2 hQ).ne', hden, hnormalizedDen,
    show q ^ 2 + (1 - Real.exp (-t)) ≠ 0 by positivity]
  <;> ring

/-- Both the actual row L1 domain and row equality are conclusions. The
Jacobian integrability iff transfers a genuine Cauchy L1 integral, avoiding
any circular assumption that the target row is already integrable. -/
private theorem quarter_schur_weighted_row_domain {t : ℝ} (ht : 0 < t) :
    Integrable (fun s : ℝ =>
      positiveHankelKernel (1 / 4) (t + s) * quarterSchurWeight s) halfline ∧
    (∫ s : ℝ, positiveHankelKernel (1 / 4) (t + s) *
      quarterSchurWeight s ∂halfline) = Real.pi * quarterSchurWeight t := by
  let A : ℝ := 1 - Real.exp (-t)
  have hA : 0 < A := by
    dsimp only [A]
    have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0)
    linarith
  have hb : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  obtain ⟨hCI, hCeq⟩ := quarter_cauchy_domain hb
  have hC : Integrable (fun q : ℝ =>
      2 * Real.exp (-t / 4) / (q ^ 2 + A)) halfline := by
    simpa only [quarterCauchy, Real.sq_sqrt hA.le, div_eq_mul_inv] using
      hCI.const_mul (2 * Real.exp (-t / 4))
  let R : ℝ → ℝ := fun s =>
    positiveHankelKernel (1 / 4) (t + s) * quarterSchurWeight s
  have hD (q : ℝ) (_hq : q ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt quarterSchurChange (quarterSchurChangeDeriv q) (Ioi 0) q :=
    (quarter_schur_change_deriv q).hasDerivWithinAt
  have hT : IntegrableOn (fun q : ℝ =>
      |quarterSchurChangeDeriv q| • R (quarterSchurChange q)) (Ioi 0) := by
    change Integrable _ halfline
    apply hC.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    exact (quarter_schur_row_substitution ht hq).symm
  have hi : Integrable R halfline := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hD quarter_schur_change_inj R).2 hT
    simpa only [quarter_schur_change_image, IntegrableOn, halfline] using h
  refine ⟨hi, ?_⟩
  change (∫ s : ℝ in Ioi 0, R s) = _
  calc
    _ = ∫ q : ℝ in Ioi 0,
        |quarterSchurChangeDeriv q| • R (quarterSchurChange q) := by
      simpa only [quarter_schur_change_image] using
        integral_image_eq_integral_abs_deriv_smul
          measurableSet_Ioi hD quarter_schur_change_inj R
    _ = ∫ q : ℝ in Ioi 0, 2 * Real.exp (-t / 4) / (q ^ 2 + A) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact quarter_schur_row_substitution ht hq
    _ = 2 * Real.exp (-t / 4) * (Real.pi / (2 * Real.sqrt A)) := by
      have hpoint (q : ℝ) :
          2 * Real.exp (-t / 4) / (q ^ 2 + A) =
            2 * Real.exp (-t / 4) * quarterCauchy (Real.sqrt A) q := by
        rw [quarterCauchy, Real.sq_sqrt hA.le, div_eq_mul_inv]
      simp_rw [hpoint]
      rw [integral_const_mul, hCeq]
    _ = Real.pi * quarterSchurWeight t := by
      change 2 * Real.exp (-t / 4) * (Real.pi / (2 * Real.sqrt A)) =
        Real.pi * (Real.exp (-t / 4) / Real.sqrt A)
      field_simp [hb.ne']
      <;> ring

private def quarterSchurRow (t s : ℝ) : ℝ :=
  positiveHankelKernel (1 / 4) (t + s) *
    quarterSchurWeight s / quarterSchurWeight t

private theorem quarter_kernel_domination {k x : ℝ}
    (hk : (1 / 4 : ℝ) ≤ k) (hx : 0 < x) :
    0 ≤ positiveHankelKernel k x ∧
      positiveHankelKernel k x ≤ positiveHankelKernel (1 / 4) x := by
  have hd : 0 < 1 - Real.exp (-x) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -x < 0)
    linarith
  constructor
  · unfold positiveHankelKernel
    exact div_nonneg (Real.exp_pos _).le hd.le
  · unfold positiveHankelKernel
    exact div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith)) hd.le

private theorem quarter_schur_row_nonneg {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 ≤ quarterSchurRow s t := by
  unfold quarterSchurRow
  exact div_nonneg
    (mul_nonneg (quarter_kernel_domination le_rfl (add_pos hs ht)).1
      (quarter_schur_weight_pos ht).le) (quarter_schur_weight_pos hs).le

private theorem quarter_schur_row_domain {t : ℝ} (ht : 0 < t) :
    Integrable (quarterSchurRow t) halfline ∧
      (∫ s : ℝ, quarterSchurRow t s ∂halfline) = Real.pi := by
  obtain ⟨hi, heq⟩ := quarter_schur_weighted_row_domain ht
  refine ⟨hi.div_const _, ?_⟩
  change (∫ s : ℝ, (positiveHankelKernel (1 / 4) (t + s) *
    quarterSchurWeight s) / quarterSchurWeight t ∂halfline) = _
  rw [integral_div, heq]
  field_simp [(quarter_schur_weight_pos ht).ne']

private theorem quarter_schur_amgm (a b p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * a * b ≤ a ^ 2 * (p / q) + b ^ 2 * (q / p) := by
  apply (mul_le_mul_iff_left₀ (mul_pos hp hq)).1
  have hcancel : (a ^ 2 * (p / q) + b ^ 2 * (q / p)) * (p * q) =
      (a * p) ^ 2 + (b * q) ^ 2 := by
    field_simp [hp.ne', hq.ne']
    <;> ring
  rw [hcancel]
  nlinarith [sq_nonneg (a * p - b * q)]

private theorem quarter_hankel_amgm {k s t : ℝ} (hk : (1 / 4 : ℝ) ≤ k)
    (hs : 0 < s) (ht : 0 < t) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    positiveHankelKernel k (s + t) * (a * b) ≤
      (a ^ 2 * quarterSchurRow s t + b ^ 2 * quarterSchurRow t s) / 2 := by
  have hK := quarter_kernel_domination hk (add_pos hs ht)
  have hKQ := (quarter_kernel_domination le_rfl (add_pos hs ht)).1
  have hw := quarter_schur_amgm a b (quarterSchurWeight t) (quarterSchurWeight s)
    (quarter_schur_weight_pos ht) (quarter_schur_weight_pos hs)
  have hm := mul_le_mul_of_nonneg_left hw hKQ
  calc
    _ ≤ positiveHankelKernel (1 / 4) (s + t) * (a * b) :=
      mul_le_mul_of_nonneg_right hK.2 (mul_nonneg ha hb)
    _ ≤ positiveHankelKernel (1 / 4) (s + t) *
        (a ^ 2 * (quarterSchurWeight t / quarterSchurWeight s) +
          b ^ 2 * (quarterSchurWeight s / quarterSchurWeight t)) / 2 := by
      linarith
    _ = _ := by
      unfold quarterSchurRow
      rw [show t + s = s + t by ring]
      ring

private def quarterSchurMajorant (u : ℝ → ℂ) (z : ℝ × ℝ) : ℝ :=
  ‖u z.1‖ ^ 2 * quarterSchurRow z.1 z.2

private theorem quarter_schur_majorant_domain (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (quarterSchurMajorant u) (halfline.prod halfline) ∧
      (∫ z : ℝ × ℝ, quarterSchurMajorant u z ∂halfline.prod halfline) =
        Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  have hsq : Integrable (fun s : ℝ => ‖u s‖ ^ 2) halfline :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hmrow : Measurable (fun z : ℝ × ℝ => quarterSchurRow z.1 z.2) := by
    unfold quarterSchurRow quarterSchurWeight positiveHankelKernel
    fun_prop
  have hm : AEStronglyMeasurable (quarterSchurMajorant u) (halfline.prod halfline) :=
    (hu.aestronglyMeasurable.comp_fst.norm.pow 2).mul hmrow.aestronglyMeasurable
  have hnorm (s : ℝ) (hs : 0 < s) :
      (∫ t : ℝ, ‖quarterSchurMajorant u (s, t)‖ ∂halfline) =
        ‖u s‖ ^ 2 * Real.pi := by
    calc
      _ = ∫ t : ℝ, ‖u s‖ ^ 2 * quarterSchurRow s t ∂halfline := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.norm_of_nonneg
          (mul_nonneg (sq_nonneg _) (quarter_schur_row_nonneg hs ht))
      _ = _ := by rw [integral_const_mul, (quarter_schur_row_domain hs).2]
  have hi : Integrable (quarterSchurMajorant u) (halfline.prod halfline) := by
    apply (integrable_prod_iff hm).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change Integrable (fun t : ℝ => ‖u s‖ ^ 2 * quarterSchurRow s t) halfline
      exact (quarter_schur_row_domain hs).1.const_mul _
    · apply (hsq.mul_const Real.pi).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hnorm s hs).symm
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ = ∫ s : ℝ, ‖u s‖ ^ 2 * Real.pi ∂halfline := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change (∫ t : ℝ, ‖u s‖ ^ 2 * quarterSchurRow s t ∂halfline) = _
      rw [integral_const_mul, (quarter_schur_row_domain hs).2]
    _ = _ := by rw [integral_mul_const]; ring

private theorem quarter_hankel_actual_absolute_domain {k : ℝ}
    (hk : (1 / 4 : ℝ) ≤ k) (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (hankelAbsolute k u) (halfline.prod halfline) ∧
      (∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline) ≤
        Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  obtain ⟨hF, hmass⟩ := quarter_schur_majorant_domain u hu
  let M : ℝ × ℝ → ℝ := fun z =>
    (quarterSchurMajorant u z + quarterSchurMajorant u z.swap) / 2
  have hFswap : Integrable (fun z : ℝ × ℝ => quarterSchurMajorant u z.swap)
      (halfline.prod halfline) := by
    simpa only [Function.comp_def] using hF.swap
  have hM : Integrable M (halfline.prod halfline) := (hF.add hFswap).div_const 2
  have hmK : Measurable (fun z : ℝ × ℝ => positiveHankelKernel k (z.1 + z.2)) := by
    unfold positiveHankelKernel
    fun_prop
  have hm : AEStronglyMeasurable (hankelAbsolute k u) (halfline.prod halfline) :=
    hmK.aestronglyMeasurable.mul (hu.aestronglyMeasurable.comp_fst.norm.mul
      hu.aestronglyMeasurable.comp_snd.norm)
  have hbound : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline, ‖hankelAbsolute k u z‖ ≤ M z := by
    filter_upwards [positive_pair_ae] with z hz
    have hK := (quarter_kernel_domination hk (add_pos hz.1 hz.2)).1
    rw [Real.norm_of_nonneg (by
      exact mul_nonneg hK (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
    exact quarter_hankel_amgm hk hz.1 hz.2 ‖u z.1‖ ‖u z.2‖
      (norm_nonneg _) (norm_nonneg _)
  have hi := hM.mono' hm hbound
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z : ℝ × ℝ, M z ∂halfline.prod halfline :=
      integral_mono_ae hi hM (hbound.mono fun z hz => (le_abs_self _).trans hz)
    _ = Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
      dsimp only [M]
      rw [integral_div, integral_add hF hFswap,
        integral_prod_swap (quarterSchurMajorant u), hmass]
      ring

/-- The true L2 Hankel domain at every k>=1/4 has the pi bound, including
the literal quarter kernel. Absolute double integrability is paid by the
new exact Schur row. The complete Laplace series and complex domain are
reused from the actual all-positive-rate theorem rather than reproved. -/
theorem positive_hankel_actual_l2_domain_quarter_sharp
    {k : ℝ} (hk : (1 / 4 : ℝ) ≤ k) (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (hankelAbsolute k u) (halfline.prod halfline) ∧
    (∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline) ≤
      Real.pi * (∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) ∧
    Integrable (hankelIntegrand k u) (halfline.prod halfline) ∧
    (∀ n : ℕ, Integrable (fun s : ℝ => (Real.exp (-(k + n) * s) : ℂ) * u s) halfline) ∧
    Summable (fun n : ℕ => Complex.normSq (literalLaplace (k + n) u)) ∧
    actualHankel k u = ((∑' n : ℕ, Complex.normSq (literalLaplace (k + n) u)) : ℂ) ∧
    0 ≤ (actualHankel k u).re ∧ (actualHankel k u).im = 0 ∧
    (actualHankel k u).re ≤ Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  obtain ⟨hAi, hAbound⟩ := quarter_hankel_actual_absolute_domain hk u hu
  obtain ⟨_, _, hHi, hL, hS, hH, hpos, him, _⟩ :=
    positive_hankel_actual_l2_domain_all_positive_rates (by linarith : 0 < k) u hu
  refine ⟨hAi, hAbound, hHi, hL, hS, hH, hpos, him, ?_⟩
  calc
    _ ≤ ‖actualHankel k u‖ := Complex.re_le_norm _
    _ ≤ ∫ z : ℝ × ℝ, ‖hankelIntegrand k u z‖ ∂halfline.prod halfline :=
      norm_integral_le_integral_norm _
    _ = ∫ z : ℝ × ℝ, hankelAbsolute k u z ∂halfline.prod halfline := by
      apply integral_congr_ae
      filter_upwards [positive_pair_ae] with z hz
      simp only [hankelIntegrand, hankelAbsolute, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (quarter_kernel_domination hk (add_pos hz.1 hz.2)).1]
    _ ≤ _ := hAbound

#print axioms positive_hankel_actual_l2_domain
#print axioms positive_hankel_actual_l2_domain_all_positive_rates
#print axioms positive_hankel_actual_l2_domain_quarter_sharp
end D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2


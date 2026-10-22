/-
Source-only continuation r4056, retaining the r4039 analytic bodies.
UNCOMPILED throughout; no native acceptance is claimed.
The sealed r4033 file is evidence, not an import: its false image split,
whole-line periodic carrier, and placeholder bridges are deliberately replaced.
Original definitions/owners and all signed modes are retained below.

The general weighted-lattice theorem consumed here was inspected in immutable
5860a2489d25479eed8a8fc3ee91719f543189ff, PeriodicEnergyTransport.lean.
Mathlib API inspection is at 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import D5.S3.Weil.ZetaCore.Defs
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.FormCore.LogGraph
import D5.S3.Weil.ZetaGamma.FormCore.Carleman
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators

namespace D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

/-- Literal carrier, dx measure. -/
def window (L : ℝ) : Set ℝ := Ioc (-L / 2) (L / 2)
def omega (L : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / L
def mode (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (omega L n : ℂ) * (x : ℂ)) / (Real.sqrt L : ℂ)
def zeroMode (L : ℝ) (n : ℤ) : ℝ → ℂ := (window L).indicator (mode L n)
def rate (j : ℕ) : ℝ := 2 * (j : ℝ) + 1 / 2

lemma rate_pos (j : ℕ) : 0 < rate j := by dsimp [rate]; positivity
lemma rate_ge_half (j : ℕ) : (1 : ℝ) / 2 ≤ rate j := by
  dsimp [rate]
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]

/-- The displacement is on all R for the literal indicator zero extension. -/
def displacementPair (L : ℝ) (m n : ℤ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, conj (zeroMode L m x - zeroMode L m (x - s)) *
    (zeroMode L n x - zeroMode L n (x - s))

/-- Corrected comparison: periodic displacement on the original window ONLY.
The positive-period instance is an actual parameter, absent from old4033. -/
def periodicPair (L : ℝ) [Fact (0 < L)] (m n : ℤ) (s : ℝ) : ℂ :=
  ∫ x in window L,
    conj (zeroMode L m x - periodicExtension L (-L / 2) (zeroMode L m) (x - s)) *
      (zeroMode L n x - periodicExtension L (-L / 2) (zeroMode L n) (x - s))

lemma window_eq (L : ℝ) : window L = Ioc (-L / 2) (-L / 2 + L) := by
  unfold window
  congr 1 <;> ring
lemma zeroMode_eq (L : ℝ) (n : ℤ) :
    zeroMode L n = zeroExtension L (-L / 2) (mode L n) := by
  simp only [zeroMode, zeroExtension, window_eq]

/-- Fix b>0 BEFORE using the geometric series. Both tails start at 1. -/
theorem image_hasSum (L b d : ℝ) (hL : 0 < L) (hb : 0 < b)
    (hd : -L ≤ d) (hd' : d ≤ L) :
    HasSum (fun k : ℤ => Real.exp (-b * |d + (k : ℝ) * L|))
      (Real.exp (-b * |d|) +
        Real.exp (-b * L) / (1 - Real.exp (-b * L)) *
          (Real.exp (-b * d) + Real.exp (b * d))) := by
  let r := Real.exp (-b * L)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hg : HasSum (fun j : ℕ => r ^ j) (1 - r)⁻¹ :=
    hasSum_geometric_of_lt_one hr0 hr1
  have hplus (j : ℕ) :
      Real.exp (-b * |d + (((j : ℤ) + 1 : ℤ) : ℝ) * L|) =
        (Real.exp (-b * d) * r) * r ^ j := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hs : 0 ≤ d + (((j : ℤ) + 1 : ℤ) : ℝ) * L := by
      push_cast
      nlinarith
    rw [abs_of_nonneg hs, ← Real.exp_nat_mul]
    dsimp [r]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hminus (j : ℕ) :
      Real.exp (-b * |d + ((-((j : ℤ) + 1) : ℤ) : ℝ) * L|) =
        (Real.exp (b * d) * r) * r ^ j := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hs : d + ((-((j : ℤ) + 1) : ℤ) : ℝ) * L ≤ 0 := by
      push_cast
      nlinarith
    rw [abs_of_nonpos hs, ← Real.exp_nat_mul]
    dsimp [r]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hp : HasSum
      (fun j : ℕ => Real.exp (-b * |d + (((j : ℤ) + 1 : ℤ) : ℝ) * L|))
      ((Real.exp (-b * d) * r) * (1 - r)⁻¹) := by
    simpa only [hplus] using hg.mul_left (Real.exp (-b * d) * r)
  have hn : HasSum
      (fun j : ℕ => Real.exp (-b * |d + ((-((j : ℤ) + 1) : ℤ) : ℝ) * L|))
      ((Real.exp (b * d) * r) * (1 - r)⁻¹) := by
    simpa only [hminus] using hg.mul_left (Real.exp (b * d) * r)
  have hall := HasSum.of_add_one_of_neg_add_one
    (f := fun k : ℤ => Real.exp (-b * |d + (k : ℝ) * L|)) hp hn
  convert hall using 1 <;>
    simp only [Int.cast_zero, zero_mul, add_zero] <;>
    dsimp [r] <;> ring

/-- Includes d=0,+L,-L. Summability is proved before subtracting k=0. -/
theorem image_kernel (L b d : ℝ) (hL : 0 < L) (hb : 0 < b)
    (hd : -L ≤ d) (hd' : d ≤ L) :
    Summable (fun k : ℤ => Real.exp (-b * |d + (k : ℝ) * L|)) ∧
      (∑' k : ℤ, Real.exp (-b * |d + (k : ℝ) * L|)) - Real.exp (-b * |d|) =
        (2 * Real.exp (-b * L) / (1 - Real.exp (-b * L))) * Real.cosh (b * d) := by
  have h := image_hasSum L b d hL hb hd hd'
  refine ⟨h.summable, ?_⟩
  rw [h.tsum_eq, Real.cosh_eq]
  simp only [neg_mul]
  ring

/-- Exact noncentral kernel used by the original lattice owner. -/
theorem weightedImageKernel_exp (L b : ℝ) (hL : 0 < L) (hb : 0 < b)
    (x y : ℝ) (hx : x ∈ window L) (hy : y ∈ window L) :
    weightedImageKernel L (fun s => Real.exp (-b * |s|)) x y =
      (2 * Real.exp (-b * L) / (1 - Real.exp (-b * L))) * Real.cosh (b * (x-y)) := by
  have hd : -L ≤ x-y := by rcases hx with ⟨hx,hx'⟩; rcases hy with ⟨hy,hy'⟩; linarith
  have hd' : x-y ≤ L := by rcases hx with ⟨hx,hx'⟩; rcases hy with ⟨hy,hy'⟩; linarith
  have hk := image_kernel L b (x-y) hL hb hd hd'
  have hsplit : (fun k : ℤ => Real.exp (-b * |x-y+(k:ℝ)*L|)) =
      fun k : ℤ => (if k = 0 then Real.exp (-b * |x-y|) else 0) +
        (if k = 0 then 0 else Real.exp (-b * |x-y+(k:ℝ)*L|)) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk]
  have hcentral : Summable (fun k : ℤ => if k = 0 then Real.exp (-b * |x-y|) else 0) :=
    (hasSum_ite_eq 0 _).summable
  have htail : Summable (fun k : ℤ => if k = 0 then 0 else
      Real.exp (-b * |x-y+(k:ℝ)*L|)) := by
    have hs := hk.1.sub hcentral
    convert hs using 1
    funext k
    by_cases hk : k = 0 <;> simp [hk]
  have heq := congrArg (fun f : ℤ → ℝ => ∑' k, f k) hsplit
  rw [hcentral.tsum_add htail] at heq
  simp only [tsum_ite_eq] at heq
  unfold weightedImageKernel
  simp only [zsmul_eq_mul]
  rw [← hk.2]
  linarith

lemma exp_pos_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => Real.exp (-b * s)) (Ioi 0) := by
  simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0

lemma exp_abs_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ => Real.exp (-b * |s|)) := by
  have hp := (exp_pos_integrable hb).integrable_indicator measurableSet_Ioi
  have hn : IntegrableOn (fun s : ℝ => Real.exp (b * s)) (Iic 0) :=
    integrableOn_exp_mul_Iic hb 0
  have hn' := hn.integrable_indicator measurableSet_Iic
  convert hp.add hn' using 1
  funext s
  by_cases hs : 0 < s
  · simp [hs, abs_of_pos hs, show ¬ s ≤ 0 by linarith]
  · have hs' : s ≤ 0 := le_of_not_gt hs
    simp [hs, hs', abs_of_nonpos hs', neg_mul_neg]

/-- Actual L2 => actual complex slice integrability on each carrier. -/
lemma zero_slice_integrable (L t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure L t)) (hg : MemLp g 2 (windowMeasure L t))
    (s : ℝ) :
    Integrable (fun x => conj (zeroExtension L t f x - zeroExtension L t f (x-s)) *
      (zeroExtension L t g x - zeroExtension L t g (x-s))) := by
  have hf0 := zero_extension_memLp L t f hf
  have hg0 := zero_extension_memLp L t g hg
  exact l2_complex_correlation_integrable
    (hf0.sub (hf0.comp_measurePreserving (measurePreserving_sub_right volume s)))
    (hg0.sub (hg0.comp_measurePreserving (measurePreserving_sub_right volume s)))

lemma periodic_slice_integrable (L t : ℝ) [Fact (0 < L)] (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure L t)) (hg : MemLp g 2 (windowMeasure L t))
    (s : ℝ) :
    Integrable (fun x => conj (f x - periodicExtension L t f (x-s)) *
      (g x - periodicExtension L t g (x-s))) (windowMeasure L t) :=
  l2_complex_correlation_integrable
    (hf.sub (periodic_shift_memLp L t f hf s))
    (hg.sub (periodic_shift_memLp L t g hg s))

lemma mask_slice_integrable_le (L t : ℝ) [Fact (0 < L)]
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure L t)) (s : ℝ) :
    Integrable (fun x => ‖u x‖ *
      ‖periodicExtension L t u (x-s) - zeroExtension L t u (x-s)‖) (windowMeasure L t) ∧
    (∫ x, ‖u x‖ * ‖periodicExtension L t u (x-s) - zeroExtension L t u (x-s)‖
      ∂windowMeasure L t) ≤ windowEnergy L t u := by
  have hp := periodic_shift_memLp L t u hu s
  have hz := (zero_extension_memLp L t u hu).comp_measurePreserving
    (measurePreserving_sub_right volume s)
  have hm := (hp.sub (hz.restrict (Ioc t (t+L)))).aestronglyMeasurable.norm
  have hdom := periodic_correlation_integrable_le L t u hu s
  have hbound (x : ℝ) : ‖u x‖ *
      ‖periodicExtension L t u (x-s) - zeroExtension L t u (x-s)‖ ≤
        ‖u x‖ * ‖periodicExtension L t u (x-s)‖ :=
    mul_le_mul_of_nonneg_left (periodic_minus_zero_norm_le L t u (x-s)) (norm_nonneg _)
  have hi : Integrable (fun x => ‖u x‖ *
      ‖periodicExtension L t u (x-s) - zeroExtension L t u (x-s)‖) (windowMeasure L t) := by
    apply hdom.1.mono' (hu.aestronglyMeasurable.norm.mul hm)
    exact Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hbound x
  exact ⟨hi, (integral_mono hi hdom.1 hbound).trans hdom.2⟩

/-- This is the missing analytic payment. Joint measurability + absolute slices
+ an L1(s) majorant, not a bound on a potentially totalized product integral. -/
theorem exp_differenceCorrelation_integrable
    (L t b : ℝ) [Fact (0 < L)] (hb : 0 < b) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure L t)) :
    Integrable (weightedDifferenceCorrelation L t (fun s => Real.exp (-b * |s|)) u)
      ((windowMeasure L t).prod volume) := by
  let w : ℝ → ℝ := fun s => Real.exp (-b * |s|)
  let F : ℝ × ℝ → ℂ := fun p => weightedDifferenceCorrelation L t w u p.swap
  let N : ℝ → ℝ := fun s => ∫ x, ‖F (s,x)‖ ∂windowMeasure L t
  have hw : Integrable w := exp_abs_integrable hb
  have hFm : AEStronglyMeasurable F (volume.prod (windowMeasure L t)) := by
    have hwc : AEStronglyMeasurable (fun s => (w s : ℂ)) volume := hw.ofReal.aestronglyMeasurable
    have huc : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (u p.2))
        (volume.prod (windowMeasure L t)) := Complex.continuous_conj.comp_aestronglyMeasurable
      hu.aestronglyMeasurable.comp_snd
    exact (hwc.comp_fst.mul huc).mul
      ((periodic_shift_joint_aestronglyMeasurable L t u hu).sub
        (zero_shift_joint_aestronglyMeasurable L t u hu))
  have hnorm (s x : ℝ) : ‖F (s,x)‖ = w s *
      (‖u x‖ * ‖periodicExtension L t u (x-s) - zeroExtension L t u (x-s)‖) := by
    simp only [F, weightedDifferenceCorrelation, Prod.swap_prod_mk, norm_mul,
      Complex.norm_conj, Complex.norm_real, w, Real.norm_of_nonneg (Real.exp_pos _).le]
    ring
  have hSlice (s : ℝ) : Integrable (fun x => F (s,x)) (windowMeasure L t) := by
    have hz := (zero_extension_memLp L t u hu).comp_measurePreserving
      (measurePreserving_sub_right volume s)
    have hc := l2_complex_correlation_integrable hu
      ((periodic_shift_memLp L t u hu s).sub (hz.restrict (Ioc t (t+L))))
    convert hc.const_mul (w s : ℂ) using 1
    funext x
    dsimp [F, weightedDifferenceCorrelation]
    ring
  have hNm : AEStronglyMeasurable N volume := hFm.norm.integral_prod_right'
  have hNle (s : ℝ) : N s ≤ w s * windowEnergy L t u := by
    dsimp [N]
    simp_rw [hnorm]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (mask_slice_integrable_le L t u hu s).2
      (Real.exp_pos _).le
  have hNi : Integrable N := by
    apply (hw.const_mul (windowEnergy L t u)).mono' hNm
    exact Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      simpa only [mul_comm] using hNle s
  have hFi : Integrable F (volume.prod (windowMeasure L t)) :=
    (integrable_prod_iff hFm).mpr ⟨Eventually.of_forall hSlice,hNi⟩
  simpa only [F,Function.comp_def,Prod.swap_swap] using hFi.swap

lemma exp_energy_integrable (L t b : ℝ) [Fact (0 < L)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure L t)) :
    IntegrableOn (fun s => Real.exp (-b*s) * zeroTranslationEnergy L t u s) (Ioi 0) ∧
    IntegrableOn (fun s => Real.exp (-b*s) * periodicTranslationEnergy L t u s) (Ioi 0) := by
  have he := exp_pos_integrable hb
  constructor
  · apply (he.const_mul (4 * windowEnergy L t u)).mono'
      ((by fun_prop : AEStronglyMeasurable (fun s : ℝ => Real.exp (-b*s))
        (volume.restrict (Ioi 0))).mul
        (zeroTranslationEnergy_aestronglyMeasurable L t u hu).restrict)
    exact Eventually.of_forall fun s => by
      have h := zeroTranslationEnergy_nonneg_le L t u hu s
      dsimp only [Pi.mul_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le h.1)]
      nlinarith [mul_le_mul_of_nonneg_left h.2 (Real.exp_pos (-b*s)).le]
  · apply (he.const_mul (4 * windowEnergy L t u)).mono'
      ((by fun_prop : AEStronglyMeasurable (fun s : ℝ => Real.exp (-b*s))
        (volume.restrict (Ioi 0))).mul
        (periodicTranslationEnergy_aestronglyMeasurable L t u hu).restrict)
    exact Eventually.of_forall fun s => by
      have h := periodicTranslationEnergy_nonneg_le L t u hu s
      dsimp only [Pi.mul_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le h.1)]
      nlinarith [mul_le_mul_of_nonneg_left h.2 (Real.exp_pos (-b*s)).le]

lemma even_integral_eq_twice_positive (F : ℝ → ℝ) (hi : Integrable F)
    (he : ∀ s, F (-s) = F s) :
    (∫ s, F s) = 2 * ∫ s in Ioi 0, F s := by
  have hn : (∫ s in Iic 0, F s) = ∫ s in Ioi 0, F s := by
    calc
      _ = ∫ s in Ioi 0, F (-s) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi (c := (0:ℝ)) (f := F)).symm
      _ = _ := by simp_rw [he]
  have hs := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hi
  simp only [compl_Ioi] at hs
  rw [hn] at hs
  linarith

/-- Substantive literal one-rate integral identity on arbitrary complex L2
representatives. All integrability needed by the lattice owner is proved above.
The quadratic REAL PART is intentional; mixed forms are obtained by polarization. -/
theorem one_rate_quadratic_image
    (L b : ℝ) [hL : Fact (0 < L)] (hb : 0 < b) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure L (-L/2))) :
    (∫ s in Ioi 0, Real.exp (-b*s) * zeroTranslationEnergy L (-L/2) u s) =
      (∫ s in Ioi 0, Real.exp (-b*s) * periodicTranslationEnergy L (-L/2) u s) +
      (∫ p : ℝ × ℝ, conj (u p.1) *
        (((2 * Real.exp (-b*L) / (1-Real.exp (-b*L))) * Real.cosh (b*(p.1-p.2)) : ℝ) : ℂ) *
          u p.2 ∂(windowMeasure L (-L/2)).prod (windowMeasure L (-L/2))).re := by
  let t : ℝ := -L/2
  let w : ℝ → ℝ := fun s => Real.exp (-b*|s|)
  let R : ℝ → ℝ := fun s => (periodicCorrelation L t u s - zeroCorrelation L t u s).re
  have hF := exp_differenceCorrelation_integrable L t b hb u hu
  obtain ⟨hB,hFB⟩ := weightedLattice_image_integrable_and_identity L t w u hF
  have hE := exp_energy_integrable L t b hb u hu
  have hSlice := hF.integral_prod_right
  have hSliceEq (s : ℝ) :
      (∫ x, weightedDifferenceCorrelation L t w u (x,s) ∂windowMeasure L t) =
        (w s : ℂ) * (periodicCorrelation L t u s - zeroCorrelation L t u s) := by
    unfold weightedDifferenceCorrelation
    simp_rw [mul_assoc]
    rw [integral_const_mul,correlation_difference_slice L t u hu s]
  have hRi : Integrable (fun s => w s * R s) := by
    convert hSlice.re using 1
    funext s
    change w s * R s = (∫ x, weightedDifferenceCorrelation L t w u (x,s) ∂windowMeasure L t).re
    rw [hSliceEq]
    simp only [R,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hReven (s : ℝ) : R (-s) = R s := by
    simp only [R,periodicCorrelation_neg,zeroCorrelation_neg,map_sub,Complex.sub_re,Complex.conj_re]
  have hEven (s : ℝ) : w (-s) * R (-s) = w s * R s := by
    rw [hReven]
    simp only [w,abs_neg]
  have hPositive : (∫ s in Ioi 0, w s * R s) =
      ∫ s in Ioi 0, Real.exp (-b*s) * R s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [show w s = Real.exp (-b*s) by dsimp [w]; rw [abs_of_pos hs]]
  have hBreal :
      (∫ p : ℝ × ℝ, conj (u p.1) * (weightedImageKernel L w p.1 p.2 : ℂ) * u p.2
        ∂(windowMeasure L t).prod (windowMeasure L t)).re =
          2 * ∫ s in Ioi 0, Real.exp (-b*s) * R s := by
    calc
      _ = (∫ p, weightedDifferenceCorrelation L t w u p
          ∂(windowMeasure L t).prod volume).re := congrArg Complex.re hFB.symm
      _ = (∫ s, ∫ x, weightedDifferenceCorrelation L t w u (x,s) ∂windowMeasure L t).re :=
        congrArg Complex.re (integral_prod_symm _ hF)
      _ = ∫ s, (∫ x, weightedDifferenceCorrelation L t w u (x,s) ∂windowMeasure L t).re :=
        (integral_re hSlice).symm
      _ = ∫ s, w s * R s := by
        simp_rw [hSliceEq]
        simp only [R,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      _ = 2 * ∫ s in Ioi 0, w s * R s := even_integral_eq_twice_positive _ hRi hEven
      _ = _ := by rw [hPositive]
  have hDiff :
      (∫ s in Ioi 0, Real.exp (-b*s) * zeroTranslationEnergy L t u s) -
        (∫ s in Ioi 0, Real.exp (-b*s) * periodicTranslationEnergy L t u s) =
          2 * ∫ s in Ioi 0, Real.exp (-b*s) * R s := by
    rw [← integral_sub hE.1 hE.2]
    calc
      _ = ∫ s in Ioi 0, 2 * (Real.exp (-b*s) * R s) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          dsimp only
          rw [zeroTranslationEnergy_expansion L t u hu s,
            periodicTranslationEnergy_expansion L t u hu s]
          simp only [R,Complex.sub_re]
          ring
      _ = _ := integral_const_mul _ _
  have hKernel :
      (∫ p : ℝ × ℝ, conj (u p.1) * (weightedImageKernel L w p.1 p.2 : ℂ) * u p.2
        ∂(windowMeasure L t).prod (windowMeasure L t)) =
      ∫ p : ℝ × ℝ, conj (u p.1) *
        (((2 * Real.exp (-b*L) / (1-Real.exp (-b*L))) * Real.cosh (b*(p.1-p.2)) : ℝ) : ℂ) *
          u p.2 ∂(windowMeasure L t).prod (windowMeasure L t) := by
    apply integral_congr_ae
    have hmem : ∀ᵐ p : ℝ × ℝ ∂(windowMeasure L t).prod (windowMeasure L t),
        p.1 ∈ window L ∧ p.2 ∈ window L := by
      have hw : ∀ᵐ x ∂windowMeasure L t, x ∈ window L := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
        simpa only [t, window_eq] using hx
      exact (Measure.quasiMeasurePreserving_fst.ae hw).and
        (Measure.quasiMeasurePreserving_snd.ae hw)
    filter_upwards [hmem] with p hp
    rw [weightedImageKernel_exp L b hL.out hb p.1 p.2 hp.1 hp.2]
  dsimp only [t] at hDiff hBreal hKernel
  rw [hKernel] at hBreal
  linarith

/-- Real hyperbolic weights are exactly the restrictions of Complex.cosh/sinh;
no real/even restriction is placed on u. -/
def coshMoment (L b : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ x in window L, u x * (Real.cosh (b*x) : ℂ)
def sinhMoment (L b : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ x in window L, u x * (Real.sinh (b*x) : ℂ)

lemma continuous_memLp_window (L : ℝ) {u : ℝ → ℂ} (hu : Continuous u) :
    MemLp u 2 (windowMeasure L (-L/2)) := by
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
  exact (hu.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Actual product integrability and actual Fubini factorization, not a
formal factorization of a totalized double integral. -/
theorem hyperbolic_kernel_factorization (L b : ℝ) (f g : ℝ → ℂ)
    (hCf : IntegrableOn (fun x => f x * (Real.cosh (b*x) : ℂ)) (window L))
    (hSf : IntegrableOn (fun x => f x * (Real.sinh (b*x) : ℂ)) (window L))
    (hCg : IntegrableOn (fun x => g x * (Real.cosh (b*x) : ℂ)) (window L))
    (hSg : IntegrableOn (fun x => g x * (Real.sinh (b*x) : ℂ)) (window L)) :
    Integrable (fun p : ℝ × ℝ => conj (f p.1) *
      (Real.cosh (b*(p.1-p.2)) : ℂ) * g p.2)
      ((volume.restrict (window L)).prod (volume.restrict (window L))) ∧
    (∫ p : ℝ × ℝ, conj (f p.1) * (Real.cosh (b*(p.1-p.2)) : ℂ) * g p.2
      ∂(volume.restrict (window L)).prod (volume.restrict (window L))) =
        conj (coshMoment L b f) * coshMoment L b g -
          conj (sinhMoment L b f) * sinhMoment L b g := by
  let F : ℝ × ℝ → ℂ := fun p =>
    conj (f p.1 * (Real.cosh (b*p.1) : ℂ)) * (g p.2 * (Real.cosh (b*p.2) : ℂ))
  let G : ℝ × ℝ → ℂ := fun p =>
    conj (f p.1 * (Real.sinh (b*p.1) : ℂ)) * (g p.2 * (Real.sinh (b*p.2) : ℂ))
  have hF : Integrable F ((volume.restrict (window L)).prod (volume.restrict (window L))) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hCf).mul_prod hCg
  have hG : Integrable G ((volume.restrict (window L)).prod (volume.restrict (window L))) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hSf).mul_prod hSg
  have hp : (fun p : ℝ × ℝ => conj (f p.1) * (Real.cosh (b*(p.1-p.2)) : ℂ) * g p.2) =
      fun p => F p - G p := by
    funext p
    rw [mul_sub,Real.cosh_sub]
    simp only [Complex.ofReal_sub,Complex.ofReal_mul,F,G,map_mul,Complex.conj_ofReal]
    ring
  rw [hp]
  refine ⟨hF.sub hG, ?_⟩
  rw [integral_sub hF hG]
  dsimp only [F,G]
  rw [integral_prod_mul (fun x => conj (f x * (Real.cosh (b*x) : ℂ)))
      (fun y => g y * (Real.cosh (b*y) : ℂ)),
    integral_prod_mul (fun x => conj (f x * (Real.sinh (b*x) : ℂ)))
      (fun y => g y * (Real.sinh (b*y) : ℂ)), integral_conj, integral_conj]
  rfl

/-- A continuous representative suffices for every original Fourier mode and
for the four complex polarization profiles. This is NOT an even core. -/
theorem one_rate_quadratic
    (L b : ℝ) [hL : Fact (0 < L)] (hb : 0 < b)
    (u : ℝ → ℂ) (hu : Continuous u) :
    (∫ s in Ioi 0, Real.exp (-b*s) * zeroTranslationEnergy L (-L/2) u s) =
      (∫ s in Ioi 0, Real.exp (-b*s) * periodicTranslationEnergy L (-L/2) u s) +
      (2 * Real.exp (-b*L) / (1-Real.exp (-b*L))) *
        (Complex.normSq (coshMoment L b u) - Complex.normSq (sinhMoment L b u)) := by
  have hcu : IntegrableOn (fun x => u x * (Real.cosh (b*x) : ℂ)) (window L) :=
    (by fun_prop : Continuous (fun x => u x * (Real.cosh (b*x) : ℂ))).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hsu : IntegrableOn (fun x => u x * (Real.sinh (b*x) : ℂ)) (window L) :=
    (by fun_prop : Continuous (fun x => u x * (Real.sinh (b*x) : ℂ))).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hwin : windowMeasure L (-L/2) = volume.restrict (window L) := by
    simp only [windowMeasure,window_eq]
  have hfactor := (hyperbolic_kernel_factorization L b u u hcu hsu hcu hsu).2
  have hraw := one_rate_quadratic_image L b hb u (continuous_memLp_window L hu)
  have hscale :
      (∫ p : ℝ × ℝ, conj (u p.1) *
        (((2 * Real.exp (-b*L) / (1-Real.exp (-b*L))) * Real.cosh (b*(p.1-p.2)) : ℝ) : ℂ) *
          u p.2 ∂(windowMeasure L (-L/2)).prod (windowMeasure L (-L/2))) =
      ((2 * Real.exp (-b*L) / (1-Real.exp (-b*L)) : ℝ) : ℂ) *
        (conj (coshMoment L b u) * coshMoment L b u -
          conj (sinhMoment L b u) * sinhMoment L b u) := by
    rw [hwin,← hfactor]
    change _ = _ * ∫ p : ℝ × ℝ, conj (u p.1) *
      (Real.cosh (b*(p.1-p.2)) : ℂ) * u p.2
      ∂(volume.restrict (window L)).prod (volume.restrict (window L))
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by push_cast; ring
  rw [hscale] at hraw
  simpa only [← Complex.normSq_eq_conj_mul_self, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re] using hraw

/-- Conjugate-linear FIRST polarization. The -I sign matters. -/
def qPol (a b c d : ℂ) : ℂ := (a-b-Complex.I*(c-d))/4

lemma complex_polarization (z w : ℂ) :
    conj z * w = qPol (Complex.normSq (z+w)) (Complex.normSq (z-w))
      (Complex.normSq (z+Complex.I*w)) (Complex.normSq (z-Complex.I*w)) := by
  apply Complex.ext <;> simp [qPol,Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

lemma integral_qPol {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b c d : X → ℂ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) :
    (∫ x, qPol (a x) (b x) (c x) (d x) ∂μ) =
      qPol (∫ x, a x ∂μ) (∫ x, b x ∂μ) (∫ x, c x ∂μ) (∫ x, d x ∂μ) := by
  unfold qPol
  rw [integral_div]
  rw [integral_sub (show Integrable (fun x => a x - b x) μ from ha.sub hb)
    (show Integrable (fun x => Complex.I * (c x - d x)) μ from (hc.sub hd).const_mul Complex.I),
    integral_sub ha hb, integral_const_mul, integral_sub hc hd]

lemma integral_polarization {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, conj (f x) * g x ∂μ) =
      qPol (∫ x, (Complex.normSq (f x+g x) : ℂ) ∂μ)
        (∫ x, (Complex.normSq (f x-g x) : ℂ) ∂μ)
        (∫ x, (Complex.normSq (f x+Complex.I*g x) : ℂ) ∂μ)
        (∫ x, (Complex.normSq (f x-Complex.I*g x) : ℂ) ∂μ) := by
  have hIg : MemLp (fun x => Complex.I*g x) 2 μ := by
    exact hg.const_mul Complex.I
  have hi {h : X → ℂ} (hh : MemLp h 2 μ) :
      Integrable (fun x => (Complex.normSq (h x) : ℂ)) μ := by
    simpa only [Complex.normSq_eq_conj_mul_self] using l2_complex_correlation_integrable hh hh
  calc
    _ = ∫ x, qPol (Complex.normSq (f x+g x)) (Complex.normSq (f x-g x))
        (Complex.normSq (f x+Complex.I*g x)) (Complex.normSq (f x-Complex.I*g x)) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => complex_polarization (f x) (g x))
    _ = _ := integral_qPol (hi (hf.add hg)) (hi (hf.sub hg)) (hi (hf.add hIg)) (hi (hf.sub hIg))

/-- Linear maps into the literal displacement fields; these are integrands,
not replacement correction operators. -/
def zeroGapMap (L t s : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x => zeroExtension L t f x - zeroExtension L t f (x-s)
  map_add' := by
    intro f g; funext x
    simp only [zeroExtension,Set.indicator_apply,Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro a f; funext x
    simp only [zeroExtension,Set.indicator_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;> ring

def periodicGapMap (L t s : ℝ) [Fact (0 < L)] : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x => f x - periodicExtension L t f (x-s)
  map_add' := by
    intro f g; funext x
    simp only [periodicExtension,AddCircle.liftIoc,Function.comp_apply,domRestrict,Pi.add_apply]
    ring
  map_smul' := by
    intro a f; funext x
    simp only [periodicExtension,AddCircle.liftIoc,Function.comp_apply,domRestrict,
      Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

lemma linear_integral_polarization {V X : Type*} [AddCommGroup V] [Module ℂ V]
    [MeasurableSpace X] {μ : Measure X} (A : V →ₗ[ℂ] (X → ℂ)) (f g : V)
    (hf : MemLp (A f) 2 μ) (hg : MemLp (A g) 2 μ) :
    (∫ x, conj (A f x) * A g x ∂μ) =
      qPol (∫ x, (Complex.normSq (A (f+g) x) : ℂ) ∂μ)
        (∫ x, (Complex.normSq (A (f-g) x) : ℂ) ∂μ)
        (∫ x, (Complex.normSq (A (f+Complex.I • g) x) : ℂ) ∂μ)
        (∫ x, (Complex.normSq (A (f-Complex.I • g) x) : ℂ) ∂μ) := by
  simpa only [map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    using integral_polarization hf hg

/-- Young controls the integral of the ABSOLUTE slice, before cancellation. -/
lemma absolute_slice_young {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ‖conj (f x)*g x‖) μ ∧
    (∫ x, ‖conj (f x)*g x‖ ∂μ) ≤
      ((∫ x, ‖f x‖^2 ∂μ) + (∫ x, ‖g x‖^2 ∂μ))/2 := by
  have hprod := l2_complex_correlation_integrable hf hg
  have hF := hf.integrable_norm_pow (p := 2) (by norm_num)
  have hG := hg.integrable_norm_pow (p := 2) (by norm_num)
  refine ⟨hprod.norm, ?_⟩
  calc
    _ ≤ ∫ x, (‖f x‖^2+‖g x‖^2)/2 ∂μ := by
      apply integral_mono hprod.norm ((hF.add hG).div_const 2)
      intro x
      simp only [norm_mul,Complex.norm_conj,Pi.add_apply]
      nlinarith [sq_nonneg (‖f x‖-‖g x‖)]
    _ = _ := by rw [integral_div,integral_add hF hG]

/-- Complete-rate pointwise Young majorant. Integrability of the actual
absolute slice is paid before norm_integral_le_integral_norm is used. -/
lemma slice_young {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, conj (f x)*g x ∂μ‖ ≤
      ((∫ x, ‖f x‖^2 ∂μ) + (∫ x, ‖g x‖^2 ∂μ))/2 :=
  (norm_integral_le_integral_norm _).trans (absolute_slice_young hf hg).2

/-- Joint measurability uses the actual translation fibers; separate
measurability alone would not justify the product-integral inference. -/
lemma zeroGap_joint_aestronglyMeasurable
    (L t : ℝ) (μ : Measure ℝ) [SFinite μ] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure L t)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      zeroExtension L t u p.2-zeroExtension L t u (p.2-p.1)) (μ.prod volume) := by
  have hu0 := zero_extension_memLp L t u hu
  have hmp : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.2-p.1)
      (μ.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Eventually.of_forall fun s =>
      (measurePreserving_sub_right volume s).quasiMeasurePreserving
  exact hu0.aestronglyMeasurable.comp_snd.sub
    (hu0.aestronglyMeasurable.comp_quasiMeasurePreserving hmp)

/-- Stronger than scalar pairing integrability: the original mixed gap field
is absolutely integrable on (s>0) x R. This pays spatial Fubini as well as the
complete-rate exchange; no cancellation in the x-integral is used. -/
theorem finite_energy_mixed_joint_integrable
    (L t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure L t)) (hg : MemLp g 2 (windowMeasure L t))
    (hEf : IntegrableOn (fun s =>
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s * zeroTranslationEnergy L t f s) (Ioi 0))
    (hEg : IntegrableOn (fun s =>
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s * zeroTranslationEnergy L t g s) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ =>
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity p.1 : ℂ) *
        (conj (zeroExtension L t f p.2-zeroExtension L t f (p.2-p.1)) *
          (zeroExtension L t g p.2-zeroExtension L t g (p.2-p.1))))
      ((volume.restrict (Ioi 0)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let Q : ℝ × ℝ → ℂ := fun p =>
    conj (zeroExtension L t f p.2-zeroExtension L t f (p.2-p.1)) *
      (zeroExtension L t g p.2-zeroExtension L t g (p.2-p.1))
  let F : ℝ × ℝ → ℂ := fun p =>
    (ArchimedeanJumpDecomposition.archimedeanJumpDensity p.1 : ℂ)*Q p
  have hQm : AEStronglyMeasurable Q (μ.prod volume) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (zeroGap_joint_aestronglyMeasurable L t μ f hf)).mul
        (zeroGap_joint_aestronglyMeasurable L t μ g hg)
  have hFm : AEStronglyMeasurable F (μ.prod volume) := by
    have hρm : AEStronglyMeasurable
        (fun s => (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)) μ := by
      apply Measurable.aestronglyMeasurable
      apply Complex.continuous_ofReal.measurable.comp
      unfold ArchimedeanJumpDecomposition.archimedeanJumpDensity
      fun_prop
    exact hρm.comp_fst.mul hQm
  have hSlice (s : ℝ) : Integrable (fun x => F (s,x)) := by
    simpa only [F,Q] using (zero_slice_integrable L t f g hf hg s).const_mul
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)
  have hN : Integrable (fun s => ∫ x, ‖F (s,x)‖) μ := by
    apply ((hEf.add hEg).div_const 2).mono' hFm.norm.integral_prod_right'
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hρ := ArchimedeanJumpDecomposition.jump_density_nonnegative hs
    have hf0 := zero_extension_memLp L t f hf
    have hg0 := zero_extension_memLp L t g hg
    have hY := (absolute_slice_young
      (hf0.sub (hf0.comp_measurePreserving (measurePreserving_sub_right volume s)))
      (hg0.sub (hg0.comp_measurePreserving (measurePreserving_sub_right volume s)))).2
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    simp only [F,norm_mul,Complex.norm_real,Real.norm_of_nonneg hρ,integral_const_mul]
    simpa only [Q,zeroTranslationEnergy,Complex.normSq_eq_norm_sq,mul_add,← mul_div_assoc,Pi.add_apply,Pi.sub_apply,Function.comp_apply]
      using mul_le_mul_of_nonneg_left hY hρ
  exact (integrable_prod_iff hFm).mpr ⟨Eventually.of_forall hSlice,hN⟩

/-- A genuine consumer of the majorant: arbitrary supported complex finite-energy
inputs give an absolutely integrable literal mixed displacement. The diagonal
hypotheses are exactly the domains supplied by DomainPassage, not a mixed identity. -/
theorem finite_energy_mixed_integrable
    (L t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure L t)) (hg : MemLp g 2 (windowMeasure L t))
    (hEf : IntegrableOn (fun s =>
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s * zeroTranslationEnergy L t f s) (Ioi 0))
    (hEg : IntegrableOn (fun s =>
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s * zeroTranslationEnergy L t g s) (Ioi 0)) :
    IntegrableOn (fun s => (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ) *
      ∫ x, conj (zeroExtension L t f x-zeroExtension L t f (x-s)) *
        (zeroExtension L t g x-zeroExtension L t g (x-s))) (Ioi 0) := by
  let q : ℝ → ℂ := fun s => ∫ x, conj (zeroExtension L t f x-zeroExtension L t f (x-s)) *
    (zeroExtension L t g x-zeroExtension L t g (x-s))
  have hf0 := zero_extension_memLp L t f hf
  have hg0 := zero_extension_memLp L t g hg
  have hq : AEStronglyMeasurable q volume := by
    have hDf := zeroGap_joint_aestronglyMeasurable L t volume f hf
    have hDg := zeroGap_joint_aestronglyMeasurable L t volume g hg
    exact ((Complex.continuous_conj.comp_aestronglyMeasurable hDf).mul hDg).integral_prod_right'
  have hqm : AEStronglyMeasurable
      (fun s => (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*q s)
      (volume.restrict (Ioi 0)) := by
    have hρm : AEStronglyMeasurable
      (fun s => (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ))
        (volume.restrict (Ioi 0)) := by
      apply Measurable.aestronglyMeasurable
      apply Complex.continuous_ofReal.measurable.comp
      unfold ArchimedeanJumpDecomposition.archimedeanJumpDensity
      fun_prop
    exact hρm.mul hq.restrict
  apply ((hEf.add hEg).div_const 2).mono' hqm
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hρ := ArchimedeanJumpDecomposition.jump_density_nonnegative hs
  have hbound := slice_young
    (hf0.sub (hf0.comp_measurePreserving (measurePreserving_sub_right volume s)))
    (hg0.sub (hg0.comp_measurePreserving (measurePreserving_sub_right volume s)))
  change ‖(_ : ℂ) * q s‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hρ]
  simpa only [q,zeroTranslationEnergy,Complex.normSq_eq_norm_sq,mul_add,← mul_div_assoc,Pi.add_apply,Pi.sub_apply,Function.comp_apply]
    using mul_le_mul_of_nonneg_left hbound hρ

/-- The complete positive-rate geometric sum, before any integral exchange. -/
lemma rate_exp_hasSum (s : ℝ) (hs : 0 < s) :
    HasSum (fun j : ℕ => Real.exp (-rate j*s))
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity s) := by
  have hr0 : 0 ≤ Real.exp (-2*s) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2*s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-s/2))
  convert hg using 1
  · funext j
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    dsimp [rate]
    ring
  · dsimp [ArchimedeanJumpDecomposition.archimedeanJumpDensity]
    rw [div_eq_mul_inv]

/-- Absolute complete-rate interchange. Its input is actual L1(rho*q),
which the preceding Young lemma supplies from genuine diagonal domains.
It returns summability of INTEGRALS OF NORMS, stronger than entry summability. -/
theorem complete_rate_interchange (q : ℝ → ℂ)
    (hq : AEStronglyMeasurable q (volume.restrict (Ioi 0)))
    (hfull : IntegrableOn (fun s =>
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*q s) (Ioi 0)) :
    (∀ j : ℕ, IntegrableOn (fun s => (Real.exp (-rate j*s) : ℂ)*q s) (Ioi 0)) ∧
    Summable (fun j : ℕ => ∫ s in Ioi 0, ‖(Real.exp (-rate j*s) : ℂ)*q s‖) ∧
    (∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*q s) =
      ∑' j : ℕ, ∫ s in Ioi 0, (Real.exp (-rate j*s) : ℂ)*q s := by
  let F : ℕ → ℝ → ℂ := fun j s => (Real.exp (-rate j*s) : ℂ)*q s
  have hm (j : ℕ) : AEStronglyMeasurable (F j) (volume.restrict (Ioi 0)) := by
    exact (by fun_prop : AEStronglyMeasurable
      (fun s : ℝ => (Real.exp (-rate j*s) : ℂ)) (volume.restrict (Ioi 0))).mul hq
  have hi (j : ℕ) : IntegrableOn (F j) (Ioi 0) := by
    apply hfull.norm.mono' (hm j)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hρ := ArchimedeanJumpDecomposition.jump_density_nonnegative hs
    have hle : Real.exp (-rate j*s) ≤
        ArchimedeanJumpDecomposition.archimedeanJumpDensity s := by
      rw [← (rate_exp_hasSum s hs).tsum_eq]
      exact (rate_exp_hasSum s hs).summable.le_tsum j (fun k hk => (Real.exp_pos _).le)
    simp only [F,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hρ,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hpoint (s : ℝ) (hs : 0 < s) :
      (∑' j : ℕ, ‖F j s‖ₑ) =
        ‖(ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*q s‖ₑ := by
    have hρ := ArchimedeanJumpDecomposition.jump_density_nonnegative hs
    have hexp (j : ℕ) : ‖F j s‖ₑ = ENNReal.ofReal (Real.exp (-rate j*s)) * ‖q s‖ₑ := by
      dsimp only [F]
      rw [enorm_mul,← ofReal_norm]
      simp only [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    simp_rw [hexp]
    rw [ENNReal.tsum_mul_right,
      ← ENNReal.ofReal_tsum_of_nonneg (fun j => (Real.exp_pos _).le) (rate_exp_hasSum s hs).summable,
      (rate_exp_hasSum s hs).tsum_eq]
    simp only [enorm_mul,← ofReal_norm,norm_mul,Complex.norm_real,Real.norm_of_nonneg hρ,
      ENNReal.ofReal_mul hρ]
  have habs : (∑' j : ℕ, ∫⁻ s in Ioi 0, ‖F j s‖ₑ) ≠ ∞ := by
    rw [← lintegral_tsum (fun j => (hm j).enorm)]
    convert hfull.hasFiniteIntegral.ne using 1
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact hpoint s hs
  have hsum : Summable (fun j : ℕ => ∫ s in Ioi 0, ‖F j s‖) := by
    have h := ENNReal.summable_toReal habs
    convert h using 1
    funext j
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi j),ENNReal.toReal_ofReal]
    exact integral_nonneg fun s => norm_nonneg _
  refine ⟨hi,hsum,?_⟩
  have hsumPoint : ∀ᵐ s ∂volume.restrict (Ioi (0:ℝ)),
      (∑' j : ℕ, F j s) = (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*q s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hc : HasSum (fun j : ℕ => (Real.exp (-rate j*s) : ℂ))
        (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ) :=
      Complex.ofRealCLM.hasSum (rate_exp_hasSum s hs)
    exact (hc.mul_right (q s)).tsum_eq
  calc
    _ = ∫ s in Ioi 0, ∑' j : ℕ, F j s := (integral_congr_ae hsumPoint).symm
    _ = _ := integral_tsum (fun j => hm j) habs

/-- Apply the complete rate exchange to the absolute spatial slice. The result
controls the double integral of norms, not merely the norm of a spatial integral.
The hypothesis is genuine joint L1 and is supplied above from diagonal domains. -/
theorem complete_rate_joint_absolute (Q : ℝ × ℝ → ℂ)
    (hQm : AEStronglyMeasurable Q ((volume.restrict (Ioi 0)).prod volume))
    (hfull : Integrable (fun p : ℝ × ℝ =>
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity p.1 : ℂ)*Q p)
      ((volume.restrict (Ioi 0)).prod volume)) :
    (∀ j : ℕ, Integrable (fun p : ℝ × ℝ =>
      (Real.exp (-rate j*p.1) : ℂ)*Q p) ((volume.restrict (Ioi 0)).prod volume)) ∧
    Summable (fun j : ℕ =>
      ∫ s in Ioi 0, ∫ x, ‖(Real.exp (-rate j*s) : ℂ)*Q (s,x)‖) := by
  have hpos : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi 0)).prod volume, 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact Eventually.of_forall fun x => hs
  have hi (j : ℕ) : Integrable (fun p : ℝ × ℝ =>
      (Real.exp (-rate j*p.1) : ℂ)*Q p) ((volume.restrict (Ioi 0)).prod volume) := by
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Real.exp (-rate j*p.1) : ℂ)*Q p) ((volume.restrict (Ioi 0)).prod volume) :=
      (by fun_prop : AEStronglyMeasurable (fun s : ℝ => (Real.exp (-rate j*s) : ℂ))
        (volume.restrict (Ioi 0))).comp_fst.mul hQm
    apply hfull.norm.mono' hm
    filter_upwards [hpos] with p hp
    have hρ := ArchimedeanJumpDecomposition.jump_density_nonnegative hp
    have hle : Real.exp (-rate j*p.1) ≤
        ArchimedeanJumpDecomposition.archimedeanJumpDensity p.1 := by
      rw [← (rate_exp_hasSum p.1 hp).tsum_eq]
      exact (rate_exp_hasSum p.1 hp).summable.le_tsum j (fun k hk => (Real.exp_pos _).le)
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hρ]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  refine ⟨hi, ?_⟩
  let A : ℝ → ℝ := fun s => ∫ x, ‖Q (s,x)‖
  have hAm : AEStronglyMeasurable A (volume.restrict (Ioi 0)) :=
    hQm.norm.integral_prod_right'
  have hAi : IntegrableOn (fun s =>
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*(A s : ℂ)) (Ioi 0) := by
    apply hfull.integral_norm_prod_left.ofReal.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hρ := ArchimedeanJumpDecomposition.jump_density_nonnegative hs
    simp only [A,norm_mul,Complex.norm_real,Real.norm_of_nonneg hρ,
      integral_const_mul]
    exact Complex.ofReal_mul _ _
  have h := (complete_rate_interchange (fun s => (A s : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hAm) hAi).2.1
  have heq (j : ℕ) (s : ℝ) :
      ‖(Real.exp (-rate j*s) : ℂ)*(A s : ℂ)‖ =
        ∫ x, ‖(Real.exp (-rate j*s) : ℂ)*Q (s,x)‖ := by
    have hA0 : 0 ≤ A s := integral_nonneg fun x => norm_nonneg _
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_real,Real.norm_of_nonneg hA0]
    simp_rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (integral_const_mul _ _).symm
  simpa only [heq] using h

lemma mode_continuous (L : ℝ) (n : ℤ) : Continuous (mode L n) := by unfold mode; fun_prop

lemma mode_fourier (L : ℝ) (n : ℤ) (x : ℝ) :
    mode L n x = (Real.sqrt L : ℂ)⁻¹ * _root_.fourier n (x : AddCircle L) := by
  rw [_root_.fourier_coe_apply]
  unfold mode omega
  rw [div_eq_mul_inv,mul_comm _ ((Real.sqrt L : ℂ)⁻¹)]
  congr 1
  congr 1
  push_cast
  ring

/-- True lift of the actual exponential, proved using the Ioc representative.
The lift sees no window endpoints from outside the representative interval. -/
lemma lift_mode (L : ℝ) [Fact (0 < L)] (n : ℤ) :
    AddCircle.liftIoc L (-L/2) (mode L n) =
      fun c => (Real.sqrt L : ℂ)⁻¹ * _root_.fourier n c := by
  funext c
  calc
    _ = mode L n (AddCircle.equivIoc L (-L/2) c) := rfl
    _ = (Real.sqrt L : ℂ)⁻¹ * _root_.fourier n
        ((AddCircle.equivIoc L (-L/2) c : ℝ) : AddCircle L) := mode_fourier L n _
    _ = _ := by rw [AddCircle.coe_equivIoc]

lemma physicalCoeff_mode (L : ℝ) [hL : Fact (0 < L)] (n k : ℤ) :
    FormCore.PeriodicSpectralEnergy.physicalCoeff
      (AddCircle.liftIoc L (-L/2) (mode L n)) k = if k=n then 1 else 0 := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL.out).ne'
  rw [lift_mode]
  simp only [FormCore.PeriodicSpectralEnergy.physicalCoeff,_root_.fourierCoeff.const_mul,
    _root_.fourierCoeff_fourier,Pi.single_apply]
  split_ifs <;> simp [hs]

/-- Shortest strong domain route: the exact periodic spectral owner gives one
finite coefficient; the original DomainPassage theorem then gives zero energy.
This is a new proof consumer, not a restatement of the owner's domain theorem. -/
theorem mode_actual_energy_integrable (L : ℝ) [hL : Fact (0 < L)] (n : ℤ) :
    IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) (mode L n) s) (Ioi 0) := by
  have hu := continuous_memLp_window L (mode_continuous L n)
  have hperiod := FormCore.PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum
    (d := L) (-L/2) (mode L n) hu
  have hfin :
      (∫⁻ s in Ioi 0,
        ENNReal.ofReal (ArchimedeanJumpDecomposition.archimedeanJumpDensity s) *
        ENNReal.ofReal (FormCore.PeriodicSpectralEnergy.windowGapMass
          (d := L) (-L/2) (mode L n) s)) < ∞ := by
    rw [hperiod]
    have hterm (k : ℤ) :
        ENNReal.ofReal (FormCore.PeriodicSpectralEnergy.gammaIncrement
          (FormCore.PeriodicSpectralEnergy.angularFrequency (d := L) k)) *
        ENNReal.ofReal (‖FormCore.PeriodicSpectralEnergy.physicalCoeff
          (AddCircle.liftIoc L (-L/2) (mode L n)) k‖^2) =
        if k=n then ENNReal.ofReal (FormCore.PeriodicSpectralEnergy.gammaIncrement
          (FormCore.PeriodicSpectralEnergy.angularFrequency (d := L) n)) else 0 := by
      rw [physicalCoeff_mode]
      split_ifs with hk
      · subst k; simp
      · simp
    simp_rw [hterm]
    simp only [tsum_ite_eq]
    exact ENNReal.ofReal_lt_top
  have hnn : ∀ᵐ s ∂volume.restrict (Ioi (0:ℝ)), 0 ≤
      FormCore.DomainPassage.periodicEnergyDensity L (-L/2) (mode L n) s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (ArchimedeanJumpDecomposition.jump_density_nonnegative hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hmeas : AEStronglyMeasurable
      (FormCore.DomainPassage.periodicEnergyDensity L (-L/2) (mode L n))
      (volume.restrict (Ioi 0)) := by
    have hρm : Measurable ArchimedeanJumpDecomposition.archimedeanJumpDensity := by
      unfold ArchimedeanJumpDecomposition.archimedeanJumpDensity
      fun_prop
    exact (hρm.aestronglyMeasurable.mul
        (periodicTranslationEnergy_aestronglyMeasurable L (-L/2) (mode L n) hu)).restrict
  have hp : IntegrableOn
      (FormCore.DomainPassage.periodicEnergyDensity L (-L/2) (mode L n)) (Ioi 0) := by
    refine ⟨hmeas,(hasFiniteIntegral_iff_ofReal hnn).mpr ?_⟩
    convert hfin using 1
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    dsimp [FormCore.DomainPassage.periodicEnergyDensity,
      FormCore.DomainPassage.intervalMeasure,FormCore.PeriodicSpectralEnergy.windowGapMass,
      periodicExtension]
    rw [ENNReal.ofReal_mul (ArchimedeanJumpDecomposition.jump_density_nonnegative hs)]
    simp only [Complex.normSq_eq_norm_sq]
  have hmem : MemLp (mode L n) 2 (volume.restrict (Ioc (-(L/2)) (L/2))) := by
    convert hu using 1 <;> dsimp [windowMeasure] <;> congr 1 <;> ring
  have hdomain := FormCore.DomainPassage.actual_centered_gamma_full_domain_equivalence
    (L/2) (by linarith [hL.out]) (mode L n) hmem
  have hscale : 2*(L/2) = L := by ring
  letI : Fact (0 < 2*(L/2)) := ⟨by linarith [hL.out]⟩
  have hcanonical : IntegrableOn
      (FormCore.DomainPassage.zeroEnergyDensity L (-L/2) (mode L n)) (Ioi 0) := by
    have hp' : IntegrableOn
        (FormCore.DomainPassage.periodicEnergyDensity (2*(L/2)) (-(L/2)) (mode L n)) (Ioi 0) := by
      convert hp using 1 <;> congr 1 <;> ring
    have hz := hdomain.1.mpr hp'
    simpa only [hscale,neg_div] using hz
  exact hcanonical

/-- Actual all-signed mode consumer: the COMPLETE series of integrals of norms
converges, and its sum is the original rho-weighted complex displacement.
There is no even/real restriction and no condition m≠n. -/
theorem modes_complete_rate_interchange (L : ℝ) [hL : Fact (0 < L)] (m n : ℤ) :
    Summable (fun j : ℕ =>
      ∫ s in Ioi 0, ‖(Real.exp (-rate j*s) : ℂ)*displacementPair L m n s‖) ∧
    (∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*
      displacementPair L m n s) =
      ∑' j : ℕ, ∫ s in Ioi 0, (Real.exp (-rate j*s) : ℂ)*displacementPair L m n s := by
  have hm := continuous_memLp_window L (mode_continuous L m)
  have hn := continuous_memLp_window L (mode_continuous L n)
  have hf := finite_energy_mixed_integrable L (-L/2) (mode L m) (mode L n) hm hn
    (mode_actual_energy_integrable L m) (mode_actual_energy_integrable L n)
  have hfull : IntegrableOn (fun s =>
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*
        displacementPair L m n s) (Ioi 0) := by
    simpa only [displacementPair,zeroMode_eq] using hf
  have hq : AEStronglyMeasurable (displacementPair L m n) (volume.restrict (Ioi 0)) := by
    have hρpos : ∀ᵐ s ∂volume.restrict (Ioi (0:ℝ)),
        (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ) ≠ 0 := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      apply Complex.ofReal_ne_zero.mpr
      dsimp [ArchimedeanJumpDecomposition.archimedeanJumpDensity]
      exact ne_of_gt (div_pos (Real.exp_pos _) (sub_pos.mpr
        (Real.exp_lt_one_iff.mpr (by have hs' : 0 < s := hs; linarith))))
    have hd : AEStronglyMeasurable
        (fun s => ((ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ) *
          displacementPair L m n s) / (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ))
        (volume.restrict (Ioi 0)) := hfull.aestronglyMeasurable.div₀ (by
          apply Measurable.aestronglyMeasurable
          apply Complex.continuous_ofReal.measurable.comp
          unfold ArchimedeanJumpDecomposition.archimedeanJumpDensity
          fun_prop)
    apply hd.congr
    filter_upwards [hρpos] with s hs
    exact mul_div_cancel_left₀ _ hs
  exact (complete_rate_interchange _ hq hfull).2

/-- Original signed-mode consumer for the stronger joint absolute rate bound.
Together with modes_complete_rate_interchange this pays both spatial Fubini
and the entire positive-rate sum on the literal zero-extension carrier. -/
theorem modes_complete_rate_joint_absolute (L : ℝ) [Fact (0 < L)] (m n : ℤ) :
    (∀ j : ℕ, Integrable (fun p : ℝ × ℝ =>
      (Real.exp (-rate j*p.1) : ℂ) *
        (conj (zeroMode L m p.2-zeroMode L m (p.2-p.1)) *
          (zeroMode L n p.2-zeroMode L n (p.2-p.1))))
      ((volume.restrict (Ioi 0)).prod volume)) ∧
    Summable (fun j : ℕ => ∫ s in Ioi 0, ∫ x,
      ‖(Real.exp (-rate j*s) : ℂ) *
        (conj (zeroMode L m x-zeroMode L m (x-s)) *
          (zeroMode L n x-zeroMode L n (x-s)))‖) := by
  have hm := continuous_memLp_window L (mode_continuous L m)
  have hn := continuous_memLp_window L (mode_continuous L n)
  let Q : ℝ × ℝ → ℂ := fun p =>
    conj (zeroExtension L (-L/2) (mode L m) p.2-
      zeroExtension L (-L/2) (mode L m) (p.2-p.1)) *
        (zeroExtension L (-L/2) (mode L n) p.2-
          zeroExtension L (-L/2) (mode L n) (p.2-p.1))
  have hQm : AEStronglyMeasurable Q ((volume.restrict (Ioi 0)).prod volume) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (zeroGap_joint_aestronglyMeasurable L (-L/2) (volume.restrict (Ioi 0)) (mode L m) hm)).mul
        (zeroGap_joint_aestronglyMeasurable L (-L/2) (volume.restrict (Ioi 0)) (mode L n) hn)
  have hfull := finite_energy_mixed_joint_integrable L (-L/2) (mode L m) (mode L n) hm hn
    (mode_actual_energy_integrable L m) (mode_actual_energy_integrable L n)
  simpa only [Q,zeroMode_eq] using complete_rate_joint_absolute Q hQm hfull


end D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

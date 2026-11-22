/- GID: D5/S3/Analytic/PetzStripFiniteSeries
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzStripFiniteSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boundary integrals recover the real derivative of a finite complex overlap. -/

import D5.S3.Analytic.PetzCothStripMode
import D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Basic.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
# Finite-frequency Petz strip integrals

The two width-one-half boundary weights and derivative relation come from
Yang, *Quantum data processing equality*, arXiv:2609.33815v2, §III.1, Eq. (III.2).
Nonnegativity controls the deficit at the singular lower boundary. At the
upper boundary the integrable weight dominates the bounded deficit. Reflection
then removes the odd sine terms from both integrals.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace PetzStripFiniteSeries

open PetzCothStripMode
open PetzExponentialBoundaryEvaluation
  (petzWeight petzWeight_pos petzWeight_neg continuous_petzWeight)

noncomputable section

/-- The actual upper weight is a difference of dilates off the singular point. -/
private theorem petzWeight_eq_lowerWeight {s : ℝ} (hs : s ≠ 0) :
    petzWeight s = lowerWeight s - 4 * lowerWeight (2 * s) := by
  let x : ℝ := 2 * Real.pi * s
  have hx : x ≠ 0 := mul_ne_zero (by positivity) hs
  have hminus : Real.cosh x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_cosh.mpr hx)).ne'
  have hplus : Real.cosh x + 1 ≠ 0 := (add_pos (Real.cosh_pos x) zero_lt_one).ne'
  have hdouble : Real.cosh (2 * x) - 1 =
      2 * (Real.cosh x - 1) * (Real.cosh x + 1) := by
    rw [Real.cosh_two_mul]
    nlinarith only [Real.cosh_sq_sub_sinh_sq x]
  have harg : 2 * Real.pi * (2 * s) = 2 * x := by dsimp [x]; ring
  unfold petzWeight lowerWeight
  rw [harg, hdouble]
  change Real.pi / (Real.cosh x + 1) =
    Real.pi / (Real.cosh x - 1) - 4 * (Real.pi /
      (2 * (Real.cosh x - 1) * (Real.cosh x + 1)))
  field_simp [hminus, hplus]
  ring

private def upperPrimitive (s : ℝ) : ℝ := Real.sigmoid (2 * Real.pi * s)

private theorem petzWeight_eq_exp (s : ℝ) :
    petzWeight s =
      2 * Real.pi * Real.exp (-(2 * Real.pi * s)) /
        (1 + Real.exp (-(2 * Real.pi * s))) ^ 2 := by
  let x : ℝ := 2 * Real.pi * s
  let r : ℝ := Real.exp (-x)
  have hr : 0 < r := Real.exp_pos _
  have hexp : Real.exp x = r⁻¹ := by
    dsimp only [r]
    rw [Real.exp_neg, inv_inv]
  have hcosh : Real.cosh x + 1 = (1 + r) ^ 2 / (2 * r) := by
    rw [Real.cosh_eq, hexp]
    change (r⁻¹ + r) / 2 + 1 = (1 + r) ^ 2 / (2 * r)
    field_simp [hr.ne']
    ring
  change Real.pi / (Real.cosh x + 1) = 2 * Real.pi * r / (1 + r) ^ 2
  rw [hcosh, div_div_eq_mul_div]
  congr 1
  ring

private theorem hasDerivAt_upperPrimitive (s : ℝ) :
    HasDerivAt upperPrimitive (petzWeight s) s := by
  let x : ℝ := 2 * Real.pi * s
  have h : HasDerivAt upperPrimitive
      ((Real.sigmoid x * (1 - Real.sigmoid x)) * (2 * Real.pi)) s :=
    (Real.hasDerivAt_sigmoid x).comp s (hasDerivAt_const_mul (x := s) (2 * Real.pi))
  have hvalue : (Real.sigmoid x * (1 - Real.sigmoid x)) * (2 * Real.pi) =
      petzWeight s := by
    rw [← Real.sigmoid_neg x, ← Real.sigmoid_mul_rexp_neg x, Real.sigmoid_def x,
      petzWeight_eq_exp s]
    change ((1 + Real.exp (-x))⁻¹ * ((1 + Real.exp (-x))⁻¹ * Real.exp (-x))) *
      (2 * Real.pi) = 2 * Real.pi * Real.exp (-x) / (1 + Real.exp (-x)) ^ 2
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  exact hvalue ▸ h

private theorem tendsto_upperPrimitive_atTop : Tendsto upperPrimitive atTop (𝓝 1) := by
  have hrate : 0 < 2 * Real.pi := by positivity
  have hlin : Tendsto (fun s : ℝ => 2 * Real.pi * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hrate).2 tendsto_id
  exact Real.tendsto_sigmoid_atTop.comp hlin

private theorem integrableOn_petzWeight : IntegrableOn petzWeight (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => hasDerivAt_upperPrimitive s)
    (fun s _ => (petzWeight_pos s).le) tendsto_upperPrimitive_atTop

private theorem integrable_petzWeight : Integrable petzWeight := by
  have hneg : IntegrableOn petzWeight (Iio 0) := by
    have hpreimage : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by
      ext s
      change 0 < -s ↔ s < 0
      exact neg_pos
    have hreflected :
        IntegrableOn (petzWeight ∘ (Neg.neg : ℝ → ℝ))
          ((Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0) :=
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := petzWeight)
        (s := Ioi (0 : ℝ))).2 integrableOn_petzWeight
    have heven : petzWeight ∘ (Neg.neg : ℝ → ℝ) = petzWeight := by
      funext s
      exact petzWeight_neg s
    simpa only [hpreimage, heven] using hreflected
  have hleft : IntegrableOn petzWeight (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio (f := petzWeight) (b := (0 : ℝ))
      (μ := volume) (by finiteness)).mpr hneg
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union integrableOn_petzWeight

/-- The upper-boundary Poisson weight has unit mass on the whole real line. -/
private theorem integral_petzWeight : (∫ s : ℝ, petzWeight s) = 1 := by
  have hhalf : (∫ s in Ioi 0, petzWeight s) = 1 - upperPrimitive 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => hasDerivAt_upperPrimitive s)
      integrableOn_petzWeight tendsto_upperPrimitive_atTop
  have habs (s : ℝ) : petzWeight |s| = petzWeight s := by
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs]
    · rw [abs_of_nonpos hs, petzWeight_neg]
  calc
    _ = 2 * ∫ s in Ioi 0, petzWeight s := by
      simpa only [habs] using (integral_comp_abs (f := petzWeight))
    _ = 1 := by
      rw [hhalf]
      norm_num [upperPrimitive]

private theorem integrable_petzWeight_mul_cos (ω : ℝ) :
    Integrable (fun s : ℝ => petzWeight s * Real.cos (ω * s)) := by
  have hcont : Continuous (fun s : ℝ => petzWeight s * Real.cos (ω * s)) :=
    continuous_petzWeight.mul (by fun_prop)
  refine integrable_petzWeight.mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [norm_mul, Real.norm_of_nonneg (petzWeight_pos s).le, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (petzWeight_pos s).le (Real.abs_cos_le_one _)

/-- The factor four in the weight difference becomes two after the change of variable. -/
private theorem integral_upper_compensated (ω : ℝ) :
    (∫ s : ℝ, petzWeight s * (1 - Real.cos (ω * s))) =
      (∫ s : ℝ, lowerMode ω s) - 2 * ∫ s : ℝ, lowerMode (ω / 2) s := by
  have heq : (fun s : ℝ => petzWeight s * (1 - Real.cos (ω * s))) =ᵐ[volume]
      (fun s : ℝ => lowerMode ω s - 4 * lowerMode (ω / 2) (2 * s)) := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with s hs
    rw [petzWeight_eq_lowerWeight hs]
    simp only [lowerMode, show ω / 2 * (2 * s) = ω * s by ring]
    ring
  have hscaled : Integrable (fun s : ℝ => lowerMode (ω / 2) (2 * s)) :=
    ((integral_lowerMode (ω / 2)).1).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
  have hscale : (∫ s : ℝ, lowerMode (ω / 2) (2 * s)) =
      (1 / 2) * ∫ s : ℝ, lowerMode (ω / 2) s := by
    simpa only [abs_of_nonneg (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)),
      smul_eq_mul, one_div] using (Measure.integral_comp_mul_left (lowerMode (ω / 2)) 2)
  rw [integral_congr_ae heq, integral_sub ((integral_lowerMode ω).1) (hscaled.const_mul 4),
    integral_const_mul, hscale]
  ring

private theorem coth_half_sub_coth {x : ℝ} (hx : x ≠ 0) :
    Real.cosh (x / 2) / Real.sinh (x / 2) - Real.cosh x / Real.sinh x =
      1 / Real.sinh x := by
  have hsh : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr
    (div_ne_zero hx (by norm_num))
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have harg : 2 * (x / 2) = x := by ring
  have hc := Real.cosh_two_mul (x / 2)
  have hs := Real.sinh_two_mul (x / 2)
  rw [harg] at hc hs
  calc
    _ = (Real.cosh (x / 2) ^ 2 - Real.sinh (x / 2) ^ 2) /
        (2 * Real.sinh (x / 2) * Real.cosh (x / 2)) := by
      rw [hc, hs]
      field_simp [hsh, hch]
      ring
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq, hs]

/-- The cosine transform of the upper weight from the actual lower mode integrals. -/
private theorem integral_petzWeight_mul_cos (ω : ℝ) :
    (∫ s : ℝ, petzWeight s * Real.cos (ω * s)) =
      if ω = 0 then 1 else (ω / 2) / Real.sinh (ω / 2) := by
  by_cases hω : ω = 0
  · subst ω
    simp [integral_petzWeight]
  have hhalf : ω / 2 ≠ 0 := div_ne_zero hω (by norm_num)
  have hsub : (∫ s : ℝ, petzWeight s * (1 - Real.cos (ω * s))) =
      1 - ∫ s : ℝ, petzWeight s * Real.cos (ω * s) := by
    simp only [mul_sub, mul_one]
    rw [integral_sub integrable_petzWeight (integrable_petzWeight_mul_cos ω),
      integral_petzWeight]
  have hcomp := integral_upper_compensated ω
  rw [hsub, (integral_lowerMode ω).2, ite_eq_right hω, (integral_lowerMode (ω / 2)).2,
    ite_eq_right hhalf] at hcomp
  rw [ite_eq_right hω]
  calc
    _ = 1 - (1 - ∫ s : ℝ, petzWeight s * Real.cos (ω * s)) := by ring
    _ = 1 - ((ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1 -
          2 * (((ω / 2) / 2) * (Real.cosh ((ω / 2) / 2) / Real.sinh ((ω / 2) / 2)) - 1)) := by
      rw [hcomp]
    _ = (ω / 2) * (Real.cosh ((ω / 2) / 2) / Real.sinh ((ω / 2) / 2) -
        Real.cosh (ω / 2) / Real.sinh (ω / 2)) := by ring
    _ = _ := by rw [coth_half_sub_coth hhalf, mul_one_div]

/-- The upper-boundary mode includes the change in the real part of the strip argument. -/
private def upperMode (ω s : ℝ) : ℝ :=
  petzWeight s * (1 - Real.exp (ω / 2) * Real.cos (ω * s))

private theorem upperMode_eq_sub (ω s : ℝ) :
    upperMode ω s = petzWeight s - Real.exp (ω / 2) * (petzWeight s * Real.cos (ω * s)) := by
  unfold upperMode
  ring

private theorem integrable_upperMode (ω : ℝ) : Integrable (upperMode ω) := by
  have heq : upperMode ω =
      petzWeight - (fun s : ℝ => Real.exp (ω / 2) * (petzWeight s * Real.cos (ω * s))) := by
    funext s
    simp only [Pi.sub_apply, upperMode_eq_sub]
  rw [heq]
  exact integrable_petzWeight.sub
    ((integrable_petzWeight_mul_cos ω).const_mul (Real.exp (ω / 2)))

/-- The sum of the two actual strip contributions is exactly the negative frequency. -/
private theorem integral_combined_mode (ω : ℝ) :
    2 * ((∫ s : ℝ, lowerMode ω s) + (∫ s : ℝ, upperMode ω s)) = -ω := by
  by_cases hω : ω = 0
  · subst ω
    simp [upperMode, lowerMode]
  have hsh : Real.sinh (ω / 2) ≠ 0 :=
    Real.sinh_ne_zero.mpr (div_ne_zero hω (by norm_num))
  have hu : (∫ s : ℝ, upperMode ω s) =
      1 - Real.exp (ω / 2) * ((ω / 2) / Real.sinh (ω / 2)) := by
    simp only [upperMode_eq_sub]
    rw [integral_sub integrable_petzWeight
      ((integrable_petzWeight_mul_cos ω).const_mul (Real.exp (ω / 2))),
      integral_const_mul, integral_petzWeight, integral_petzWeight_mul_cos, ite_eq_right hω]
  rw [(integral_lowerMode ω).2, ite_eq_right hω, hu]
  calc
    _ = ω * ((Real.cosh (ω / 2) - Real.exp (ω / 2)) / Real.sinh (ω / 2)) := by ring
    _ = -ω := by
      rw [← Real.cosh_add_sinh, show Real.cosh (ω / 2) -
        (Real.cosh (ω / 2) + Real.sinh (ω / 2)) = -Real.sinh (ω / 2) by ring,
        neg_div, div_self hsh]
      ring

section FiniteSeries

variable {ι : Type*} [Fintype ι]

/-- The real cosine sum on the line with real part `a`. -/
private def cosineSeries (ω c : ι → ℝ) (a s : ℝ) : ℝ :=
  ∑ i, c i * (Real.exp (ω i * a) * Real.cos (ω i * s))

private theorem weighted_cosine_deficit (ω c : ι → ℝ) (hc : (∑ i, c i) = 1)
    (w a s : ℝ) :
    w * (2 * (1 - cosineSeries ω c a s)) =
      ∑ i, (2 * c i) * (w * (1 - Real.exp (ω i * a) * Real.cos (ω i * s))) := by
  unfold cosineSeries
  calc
    _ = w * (2 * ∑ i, (c i - c i * (Real.exp (ω i * a) * Real.cos (ω i * s)))) := by
      rw [Finset.sum_sub_distrib, hc]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Finite linearity for normalized real coefficients, including zero frequencies. -/
private theorem integral_finite_cosine (ω c : ι → ℝ) (hc : (∑ i, c i) = 1) :
    let L := fun s => lowerWeight s * (2 * (1 - cosineSeries ω c 0 s))
    let U := fun s => petzWeight s * (2 * (1 - cosineSeries ω c (1 / 2) s))
    Integrable L ∧ Integrable U ∧
      (∫ s, L s) + (∫ s, U s) = -(∑ i, c i * ω i) := by
  dsimp only
  have hL : (fun s => lowerWeight s * (2 * (1 - cosineSeries ω c 0 s))) =
      fun s => ∑ i, (2 * c i) * lowerMode (ω i) s := by
    funext s
    simpa only [mul_zero, Real.exp_zero, one_mul, lowerMode] using
      weighted_cosine_deficit ω c hc (lowerWeight s) 0 s
  have hU : (fun s => petzWeight s * (2 * (1 - cosineSeries ω c (1 / 2) s))) =
      fun s => ∑ i, (2 * c i) * upperMode (ω i) s := by
    funext s
    simpa only [mul_one_div, upperMode] using
      weighted_cosine_deficit ω c hc (petzWeight s) (1 / 2) s
  have hLi (i : ι) : Integrable (fun s => (2 * c i) * lowerMode (ω i) s) :=
    ((integral_lowerMode (ω i)).1).const_mul _
  have hUi (i : ι) : Integrable (fun s => (2 * c i) * upperMode (ω i) s) :=
    (integrable_upperMode (ω i)).const_mul _
  rw [hL, hU]
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hLi i),
    integrable_finsetSum Finset.univ (fun i _ => hUi i), ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hLi i),
    integral_finsetSum Finset.univ (fun i _ => hUi i)]
  simp only [integral_const_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = c i * (2 * ((∫ s, lowerMode (ω i) s) + (∫ s, upperMode (ω i) s))) := by ring
    _ = _ := by rw [integral_combined_mode, mul_neg]

/-- The finite exponential overlap at a complex strip argument. -/
def finiteOverlap (ω : ι → ℝ) (c : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, c i * Complex.exp ((ω i : ℂ) * z)

private def stripPoint (a s : ℝ) : ℂ := (a : ℂ) + (s : ℂ) * Complex.I

private theorem finiteOverlap_re (ω : ι → ℝ) (c : ι → ℂ) (a s : ℝ) :
    (finiteOverlap ω c (stripPoint a s)).re =
      ∑ i, ((c i).re * (Real.exp (ω i * a) * Real.cos (ω i * s)) -
        (c i).im * (Real.exp (ω i * a) * Real.sin (ω i * s))) := by
  unfold finiteOverlap
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [stripPoint, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]

private theorem finiteOverlap_re_add_reflect (ω : ι → ℝ) (c : ι → ℂ) (a s : ℝ) :
    (finiteOverlap ω c (stripPoint a s)).re + (finiteOverlap ω c (stripPoint a (-s))).re =
      2 * cosineSeries ω (fun i => (c i).re) a s := by
  simp only [finiteOverlap_re, cosineSeries, ← Finset.sum_add_distrib, Finset.mul_sum,
    mul_neg, Real.cos_neg, Real.sin_neg]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem integral_eq_reflection_average {f g : ℝ → ℝ} (hf : Integrable f)
    (havg : ∀ s, f s + f (-s) = 2 * g s) :
    (∫ s, f s) = ∫ s, g s := by
  have hneg : Integrable (fun s => f (-s)) := by
    simpa only [neg_one_mul] using hf.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have hreflect : (∫ s, f (-s)) = ∫ s, f s := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using
      Measure.integral_comp_mul_left f (-1)
  have hint : (∫ s, f s + f (-s)) = ∫ s, 2 * g s :=
    congrArg (fun k : ℝ → ℝ => ∫ s, k s) (funext havg)
  rw [integral_add hf hneg, hreflect, integral_const_mul] at hint
  linarith only [hint]

/-- The unsymmetrized boundary deficit of the finite exponential overlap. -/
def overlapDeficit (ω : ι → ℝ) (c : ι → ℂ) (a s : ℝ) : ℝ :=
  2 * (1 - (finiteOverlap ω c (stripPoint a s)).re)

private theorem continuous_overlapDeficit (ω : ι → ℝ) (c : ι → ℂ) (a : ℝ) :
    Continuous (overlapDeficit ω c a) := by
  unfold overlapDeficit finiteOverlap stripPoint
  fun_prop

private theorem weighted_deficit_add_reflect (ω : ι → ℝ) (c : ι → ℂ) (a : ℝ)
    (w : ℝ → ℝ) (hwe : ∀ s, w (-s) = w s) (s : ℝ) :
    w s * overlapDeficit ω c a s + w (-s) * overlapDeficit ω c a (-s) =
      2 * (w s * (2 * (1 - cosineSeries ω (fun i => (c i).re) a s))) := by
  simp only [hwe, overlapDeficit]
  calc
    _ = w s * (4 - 2 * ((finiteOverlap ω c (stripPoint a s)).re +
        (finiteOverlap ω c (stripPoint a (-s))).re)) := by ring
    _ = _ := by rw [finiteOverlap_re_add_reflect]; ring

private theorem integrable_upper_deficit (ω : ι → ℝ) (c : ι → ℂ) :
    Integrable (fun s => petzWeight s * overlapDeficit ω c (1 / 2) s) := by
  let bound := 2 * (1 + ∑ i, ‖c i‖ * Real.exp (ω i / 2))
  refine (integrable_petzWeight.const_mul bound).mono'
    (continuous_petzWeight.mul (continuous_overlapDeficit ω c (1 / 2))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  have hnorm : ‖finiteOverlap ω c (stripPoint (1 / 2) s)‖ ≤
      ∑ i, ‖c i‖ * Real.exp (ω i / 2) := by
    unfold finiteOverlap
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    simp [Complex.norm_exp, stripPoint, Complex.mul_re, div_eq_mul_inv]
  have hdeficit : ‖overlapDeficit ω c (1 / 2) s‖ ≤ bound := by
    unfold overlapDeficit
    rw [norm_mul, show ‖(2 : ℝ)‖ = 2 by norm_num]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by norm_num)
    rw [norm_one, Real.norm_eq_abs]
    exact add_le_add le_rfl ((Complex.abs_re_le_norm _).trans hnorm)
  rw [norm_mul, Real.norm_of_nonneg (petzWeight_pos s).le]
  exact (mul_le_mul_of_nonneg_left hdeficit (petzWeight_pos s).le).trans_eq (mul_comm _ _)

/-- Differentiate the finite overlap at the left boundary point. -/
theorem hasDerivAt_finiteOverlap_zero (ω : ι → ℝ) (c : ι → ℂ) :
    HasDerivAt (finiteOverlap ω c) (∑ i, c i * (ω i : ℂ)) 0 := by
  unfold finiteOverlap
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [mul_zero, Complex.exp_zero, mul_one, one_mul] using
    (((hasDerivAt_id' (0 : ℂ)).const_mul (ω i : ℂ)).cexp.const_mul (c i))

/-- For a normalized finite exponential overlap with nonnegative lower deficit,
both weighted boundary deficits are integrable. Their integrals sum to the
negative real derivative at zero. -/
theorem integral_finiteOverlap_strip (ω : ι → ℝ) (c : ι → ℂ)
    (hc : (finiteOverlap ω c 0).re = 1)
    (hL : ∀ s, 0 ≤ overlapDeficit ω c 0 s) :
    Integrable (fun s => lowerWeight s * overlapDeficit ω c 0 s) ∧
    Integrable (fun s => petzWeight s * overlapDeficit ω c (1 / 2) s) ∧
      (∫ s, lowerWeight s * overlapDeficit ω c 0 s) +
        (∫ s, petzWeight s * overlapDeficit ω c (1 / 2) s) =
        -(deriv (finiteOverlap ω c) 0).re := by
  have hsum : (∑ i, (c i).re) = 1 := by
    simpa only [finiteOverlap, mul_zero, Complex.exp_zero, mul_one, Complex.re_sum] using hc
  have h := integral_finite_cosine ω (fun i => (c i).re) hsum
  have hLm : Measurable lowerWeight := by
    unfold lowerWeight
    exact measurable_const.div (show Continuous (fun s : ℝ =>
      Real.cosh (2 * Real.pi * s) - 1) by fun_prop).measurable
  have hLavg := weighted_deficit_add_reflect ω c 0 lowerWeight
    (fun s => by simp only [lowerWeight, mul_neg, Real.cosh_neg])
  have hLnonneg (s : ℝ) : 0 ≤ lowerWeight s * overlapDeficit ω c 0 s :=
    mul_nonneg (div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _))) (hL s)
  have hLi : Integrable (fun s => lowerWeight s * overlapDeficit ω c 0 s) :=
    (h.1.const_mul 2).mono'
      (hLm.mul (continuous_overlapDeficit ω c 0).measurable).aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (hLnonneg s), ← hLavg s]
        exact le_add_of_nonneg_right (hLnonneg (-s)))
  have hLint := integral_eq_reflection_average hLi hLavg
  have hUi := integrable_upper_deficit ω c
  have hUint := integral_eq_reflection_average hUi
    (weighted_deficit_add_reflect ω c (1 / 2) petzWeight petzWeight_neg)
  refine ⟨hLi, hUi, ?_⟩
  rw [hLint, hUint, h.2.2, (hasDerivAt_finiteOverlap_zero ω c).deriv]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

end FiniteSeries

end

end PetzStripFiniteSeries

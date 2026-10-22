/- GID: D5/S3/Weil/ZetaGamma/FormCore/CornerTransport
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/CornerTransport
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Endpoint corner transport and absolute integrability. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.Carleman
import D5.S3.Weil.ZetaGamma.GammaMu
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open scoped ComplexConjugate FourierTransform ENNReal Topology ContDiff Classical
open scoped SchwartzMap NNReal Convolution Pointwise

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

abbrev intervalMeasure (a : ℝ) : Measure ℝ := volume.restrict (Ioo (-a) a)
private abbrev shortMeasure (a : ℝ) : Measure ℝ := volume.restrict (Ioo 0 (2 * a))
private abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

private def shiftEquiv (a : ℝ) : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight a
private def reflectEquiv (a : ℝ) : ℝ ≃ᵐ ℝ := MeasurableEquiv.subLeft a

private theorem shift_preimage_window (a : ℝ) :
    (fun x : ℝ => x + a) ⁻¹' Ioo 0 (2 * a) = Ioo (-a) a := by
  ext x
  change (0 < x + a ∧ x + a < 2 * a) ↔ (-a < x ∧ x < a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem reflect_preimage_window (a : ℝ) :
    (fun x : ℝ => a - x) ⁻¹' Ioo 0 (2 * a) = Ioo (-a) a := by
  ext x
  change (0 < a - x ∧ a - x < 2 * a) ↔ (-a < x ∧ x < a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem shift_interval_measurePreserving (a : ℝ) :
    MeasurePreserving (shiftEquiv a) (intervalMeasure a) (shortMeasure a) := by
  change MeasurePreserving (fun x : ℝ => x + a)
    (volume.restrict (Ioo (-a) a)) (volume.restrict (Ioo 0 (2 * a)))
  rw [← shift_preimage_window a]
  exact (measurePreserving_add_right (volume : Measure ℝ) a).restrict_preimage
    measurableSet_Ioo

private theorem reflect_interval_measurePreserving (a : ℝ) :
    MeasurePreserving (reflectEquiv a) (intervalMeasure a) (shortMeasure a) := by
  change MeasurePreserving (fun x : ℝ => a - x)
    (volume.restrict (Ioo (-a) a)) (volume.restrict (Ioo 0 (2 * a)))
  rw [← reflect_preimage_window a]
  exact (Measure.measurePreserving_sub_left (volume : Measure ℝ) a).restrict_preimage
    measurableSet_Ioo

private theorem short_restrict_positive (a : ℝ) :
    positiveMeasure.restrict (Ioo 0 (2 * a)) = shortMeasure a := by
  exact Measure.restrict_restrict_of_subset (fun _ hx => hx.1)

private def transported (a : ℝ) (e : ℝ ≃ᵐ ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Ioo 0 (2 * a)).indicator (u ∘ e.symm)

private theorem transported_memLp (a : ℝ) (e : ℝ ≃ᵐ ℝ)
    (he : MeasurePreserving e (intervalMeasure a) (shortMeasure a))
    {u : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a)) :
    MemLp (transported a e u) 2 positiveMeasure := by
  unfold transported
  apply (memLp_indicator_iff_restrict (μ := positiveMeasure)
    measurableSet_Ioo.nullMeasurableSet).2
  rw [short_restrict_positive]
  exact hu.comp_measurePreserving (MeasurePreserving.symm e he)

private theorem transported_square_integral (a : ℝ) (e : ℝ ≃ᵐ ℝ)
    (he : MeasurePreserving e (intervalMeasure a) (shortMeasure a)) (u : ℝ → ℂ) :
    (∫ r, ‖transported a e u r‖ ^ 2 ∂positiveMeasure) =
      ∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a := by
  calc
    _ = ∫ r, (Ioo 0 (2 * a)).indicator
        (fun r => ‖u (e.symm r)‖ ^ 2) r ∂positiveMeasure := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioo 0 (2 * a) <;> simp [transported, hr]
    _ = ∫ r, ‖u (e.symm r)‖ ^ 2 ∂shortMeasure a := by
      rw [integral_indicator measurableSet_Ioo, short_restrict_positive]
    _ = _ := (MeasurePreserving.symm e he).integral_comp'
      (fun x => ‖u x‖ ^ 2)

private def plusEquiv (a : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (shiftEquiv a).prodCongr (reflectEquiv a)

private def minusEquiv (a : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (reflectEquiv a).prodCongr (shiftEquiv a)

def plusDistance (a : ℝ) (p : ℝ × ℝ) : ℝ := p.1 - p.2 + 2 * a
def minusDistance (a : ℝ) (p : ℝ × ℝ) : ℝ := p.2 - p.1 + 2 * a

private theorem plus_distance_coordinates (a : ℝ) (p : ℝ × ℝ) :
    plusDistance a p = (plusEquiv a p).1 + (plusEquiv a p).2 := by
  change p.1 - p.2 + 2 * a = (p.1 + a) + (a - p.2)
  ring

private theorem minus_distance_coordinates (a : ℝ) (p : ℝ × ℝ) :
    minusDistance a p = (minusEquiv a p).1 + (minusEquiv a p).2 := by
  change p.2 - p.1 + 2 * a = (a - p.1) + (p.2 + a)
  ring

theorem distances_pos {a : ℝ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    0 < plusDistance a p ∧ 0 < minusDistance a p := by
  dsimp [plusDistance, minusDistance]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

abbrev actualDensity :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

def plusPair (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (actualDensity (plusDistance a p) : ℂ) * v p.2

def minusPair (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (actualDensity (minusDistance a p) : ℂ) * v p.2

def twoCornerCutoffPair (a ε : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  {q | ε < plusDistance a q}.indicator (plusPair a u v) p +
    {q | ε < minusDistance a q}.indicator (minusPair a u v) p

end D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

open Filter
open scoped Topology

theorem interval_product_membership (a : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂(intervalMeasure a).prod (intervalMeasure a),
      p.1 ∈ Ioo (-a) a ∧ p.2 ∈ Ioo (-a) a := by
  exact (Measure.quasiMeasurePreserving_fst.ae
    (self_mem_ae_restrict measurableSet_Ioo)).and
      (Measure.quasiMeasurePreserving_snd.ae
        (self_mem_ae_restrict measurableSet_Ioo))

private theorem shortMeasure_le_positive (a : ℝ) : shortMeasure a ≤ positiveMeasure := by
  rw [← short_restrict_positive a]
  exact Measure.restrict_le_self

private theorem transported_carleman_pullback (a : ℝ) (e f : ℝ ≃ᵐ ℝ)
    (he : MeasurePreserving e (intervalMeasure a) (shortMeasure a))
    (hf : MeasurePreserving f (intervalMeasure a) (shortMeasure a))
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (fun p : ℝ × ℝ =>
      ‖u p.1‖ * ‖v p.2‖ / (e p.1 + f p.2))
      ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (e p.1 + f p.2)
      ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  let U := transported a e u
  let V := transported a f v
  let F : ℝ × ℝ → ℝ := fun p => ‖U p.1‖ * ‖V p.2‖ / (p.1 + p.2)
  have hU : MemLp U 2 positiveMeasure := transported_memLp a e he hu
  have hV : MemLp V 2 positiveMeasure := transported_memLp a f hf hv
  obtain ⟨hF, hBound⟩ :=
    D5.S3.Weil.ZetaGamma.FormCore.Carleman.carleman_integrable_and_integral_le hU hV
  have hFi : Integrable F (positiveMeasure.prod positiveMeasure) := hF
  have hprod : (shortMeasure a).prod (shortMeasure a) ≤
      positiveMeasure.prod positiveMeasure :=
    Measure.prod_mono (shortMeasure_le_positive a) (shortMeasure_le_positive a)
  have hFshort : Integrable F ((shortMeasure a).prod (shortMeasure a)) :=
    hFi.mono_measure hprod
  have hPos : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      0 < p.1 ∧ 0 < p.2 :=
    (Measure.quasiMeasurePreserving_fst.ae
      (self_mem_ae_restrict measurableSet_Ioi)).and
        (Measure.quasiMeasurePreserving_snd.ae
          (self_mem_ae_restrict measurableSet_Ioi))
  have hFnonneg : ∀ᵐ p ∂positiveMeasure.prod positiveMeasure, 0 ≤ F p := by
    filter_upwards [hPos] with p hp
    exact div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (add_pos hp.1 hp.2).le
  change (∫ p, F p ∂positiveMeasure.prod positiveMeasure) ≤
    Real.pi * Real.sqrt (∫ x, ‖transported a e u x‖ ^ 2 ∂positiveMeasure) *
      Real.sqrt (∫ y, ‖transported a f v y‖ ^ 2 ∂positiveMeasure) at hBound
  rw [transported_square_integral a e he u,
    transported_square_integral a f hf v] at hBound
  have hShortBound : (∫ p, F p ∂(shortMeasure a).prod (shortMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) :=
    (integral_mono_measure hprod hFnonneg hFi).trans hBound
  have hmap : MeasurePreserving (e.prodCongr f)
      ((intervalMeasure a).prod (intervalMeasure a))
      ((shortMeasure a).prod (shortMeasure a)) := by
    change MeasurePreserving (Prod.map e f) _ _
    exact he.prod hf
  have hEJ : ∀ᵐ p : ℝ × ℝ ∂(intervalMeasure a).prod (intervalMeasure a),
      e p.1 ∈ Ioo 0 (2 * a) ∧ f p.2 ∈ Ioo 0 (2 * a) :=
    (Measure.quasiMeasurePreserving_fst.ae
      (he.quasiMeasurePreserving.ae (self_mem_ae_restrict measurableSet_Ioo))).and
        (Measure.quasiMeasurePreserving_snd.ae
          (hf.quasiMeasurePreserving.ae (self_mem_ae_restrict measurableSet_Ioo)))
  have hEq : (fun p : ℝ × ℝ => F ((e.prodCongr f) p)) =ᵐ[
      (intervalMeasure a).prod (intervalMeasure a)]
      (fun p => ‖u p.1‖ * ‖v p.2‖ / (e p.1 + f p.2)) := by
    filter_upwards [hEJ] with p hp
    have hEu : transported a e u (e p.1) = u p.1 := by
      change (Ioo 0 (2 * a)).indicator (u ∘ e.symm) (e p.1) = u p.1
      rw [indicator_of_mem hp.1]
      exact congrArg u (e.symm_apply_apply p.1)
    have hFv : transported a f v (f p.2) = v p.2 := by
      change (Ioo 0 (2 * a)).indicator (v ∘ f.symm) (f p.2) = v p.2
      rw [indicator_of_mem hp.2]
      exact congrArg v (f.symm_apply_apply p.2)
    change ‖transported a e u (e p.1)‖ * ‖transported a f v (f p.2)‖ /
      (e p.1 + f p.2) = _
    rw [hEu, hFv]
  refine ⟨(hmap.integrable_comp_of_integrable hFshort).congr hEq, ?_⟩
  calc
    _ = ∫ p, F ((e.prodCongr f) p)
        ∂(intervalMeasure a).prod (intervalMeasure a) := (integral_congr_ae hEq).symm
    _ = ∫ p, F p ∂(shortMeasure a).prod (shortMeasure a) := hmap.integral_comp' F
    _ ≤ _ := hShortBound

def plusMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ * ‖v p.2‖ / plusDistance a p

def minusMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ * ‖v p.2‖ / minusDistance a p

private theorem plus_carleman_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (plusMajorant a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, plusMajorant a u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  have ht := transported_carleman_pullback a (shiftEquiv a) (reflectEquiv a)
    (shift_interval_measurePreserving a) (reflect_interval_measurePreserving a) hu hv
  have hfun : (fun p : ℝ × ℝ =>
      ‖u p.1‖ * ‖v p.2‖ / (shiftEquiv a p.1 + reflectEquiv a p.2)) =
      plusMajorant a u v := by
    funext p
    unfold plusMajorant
    rw [plus_distance_coordinates]
    rfl
  simpa only [hfun] using ht

private theorem minus_carleman_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (minusMajorant a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, minusMajorant a u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  have ht := transported_carleman_pullback a (reflectEquiv a) (shiftEquiv a)
    (reflect_interval_measurePreserving a) (shift_interval_measurePreserving a) hu hv
  have hfun : (fun p : ℝ × ℝ =>
      ‖u p.1‖ * ‖v p.2‖ / (reflectEquiv a p.1 + shiftEquiv a p.2)) =
      minusMajorant a u v := by
    funext p
    unfold minusMajorant
    rw [minus_distance_coordinates]
    rfl
  simpa only [hfun] using ht

end D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

def gammaCk : ℝ := (1 - Real.exp (-2))⁻¹

private theorem gamma_delta_pos : 0 < 1 - Real.exp (-2) := by
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))

theorem gammaCk_pos : 0 < gammaCk := inv_pos.mpr gamma_delta_pos

theorem actual_density_pos {t : ℝ} (ht : 0 < t) : 0 < actualDensity t := by
  change 0 < Real.exp (-t / 2) / (1 - Real.exp (-2 * t))
  have hden : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  exact div_pos (Real.exp_pos _) hden

theorem actual_density_le_gammaCk_div {t : ℝ} (ht : 0 < t) :
    actualDensity t ≤ gammaCk / t := by
  let δ : ℝ := 1 - Real.exp (-2)
  have hδ : 0 < δ := gamma_delta_pos
  by_cases ht1 : t ≤ 1
  · have hconv : Real.exp ((1 - t) • (0 : ℝ) + t • (-2 : ℝ)) ≤
        (1 - t) • Real.exp 0 + t • Real.exp (-2) :=
      convexOn_exp.2 (mem_univ _) (mem_univ _)
        (sub_nonneg.mpr ht1) ht.le (by ring)
    simp only [smul_eq_mul] at hconv
    rw [show (1 - t) * 0 + t * (-2) = -2 * t by ring,
      Real.exp_zero, mul_one] at hconv
    have hden : t * δ ≤ 1 - Real.exp (-2 * t) := by
      dsimp only [δ]
      linarith
    have hnum : Real.exp (-t / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      actualDensity t = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := rfl
      _ ≤ 1 / (t * δ) := div_le_div₀ zero_le_one hnum (mul_pos ht hδ) hden
      _ = gammaCk / t := by
        dsimp only [gammaCk, δ]
        simp only [one_div, mul_inv_rev, div_eq_mul_inv]
        ring
  · have htge : 1 ≤ t := (lt_of_not_ge ht1).le
    have hexp : Real.exp (-2 * t) ≤ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hden : δ ≤ 1 - Real.exp (-2 * t) := sub_le_sub_left hexp 1
    have htwo : 2 * Real.exp (-1) ≤ 1 := by
      rw [Real.exp_neg]
      change 2 / Real.exp 1 ≤ 1
      exact (div_le_iff₀ (Real.exp_pos 1)).2 (by
        have hx := Real.add_one_le_exp (1 : ℝ)
        linarith)
    have hmul : t * Real.exp (-t / 2) ≤ 1 := by
      calc
        _ = 2 * ((t / 2) * Real.exp (-(t / 2))) := by rw [neg_div]; ring
        _ ≤ 2 * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left
            (Real.mul_exp_neg_le_exp_neg_one (t / 2)) (by norm_num)
        _ ≤ 1 := htwo
    have hnum : Real.exp (-t / 2) ≤ 1 / t :=
      (le_div_iff₀ ht).2 (by nlinarith)
    calc
      actualDensity t = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := rfl
      _ ≤ (1 / t) / δ :=
        div_le_div₀ (div_nonneg zero_le_one ht.le) hnum hδ hden
      _ = gammaCk / t := by
        dsimp only [gammaCk, δ]
        simp only [one_div, div_eq_mul_inv]
        ring

theorem actual_density_measurable : Measurable actualDensity := by
  change Measurable (fun t : ℝ => Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))
  fun_prop

private theorem plusPair_aestronglyMeasurable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (plusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : Measurable (fun p : ℝ × ℝ => actualDensity (plusDistance a p)) :=
    actual_density_measurable.comp (by unfold plusDistance; fun_prop)
  have hKc : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (actualDensity (plusDistance a p) : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hKc).mul
    hv.aestronglyMeasurable.comp_snd

private theorem minusPair_aestronglyMeasurable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (minusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : Measurable (fun p : ℝ × ℝ => actualDensity (minusDistance a p)) :=
    actual_density_measurable.comp (by unfold minusDistance; fun_prop)
  have hKc : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (actualDensity (minusDistance a p) : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hKc).mul
    hv.aestronglyMeasurable.comp_snd

private theorem plusPair_norm_le {a : ℝ} {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖plusPair a u v p‖ ≤ gammaCk * plusMajorant a u v p := by
  have hd : 0 < plusDistance a p := (distances_pos hx hy).1
  have hk0 : 0 ≤ actualDensity (plusDistance a p) := (actual_density_pos hd).le
  have hk := actual_density_le_gammaCk_div hd
  dsimp only [plusPair, plusMajorant]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hk0]
  calc
    _ ≤ ‖u p.1‖ * (gammaCk / plusDistance a p) * ‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem minusPair_norm_le {a : ℝ} {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖minusPair a u v p‖ ≤ gammaCk * minusMajorant a u v p := by
  have hd : 0 < minusDistance a p := (distances_pos hx hy).2
  have hk0 : 0 ≤ actualDensity (minusDistance a p) := (actual_density_pos hd).le
  have hk := actual_density_le_gammaCk_div hd
  dsimp only [minusPair, minusMajorant]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hk0]
  calc
    _ ≤ ‖u p.1‖ * (gammaCk / minusDistance a p) * ‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem plus_actual_corner_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (plusPair a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, ‖plusPair a u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      gammaCk * (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) := by
  have hc := plus_carleman_integrable_and_le a hu hv
  have hDom : Integrable (fun p => gammaCk * plusMajorant a u v p)
      ((intervalMeasure a).prod (intervalMeasure a)) := hc.1.const_mul gammaCk
  have hLe : ∀ᵐ p ∂(intervalMeasure a).prod (intervalMeasure a),
      ‖plusPair a u v p‖ ≤ gammaCk * plusMajorant a u v p := by
    filter_upwards [interval_product_membership a] with p hp
    exact plusPair_norm_le hp.1 hp.2
  have hInt : Integrable (plusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    hDom.mono' (plusPair_aestronglyMeasurable a hu hv) hLe
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ p, gammaCk * plusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) :=
      integral_mono_ae hInt.norm hDom hLe
    _ = gammaCk * ∫ p, plusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.2 gammaCk_pos.le

private theorem minus_actual_corner_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (minusPair a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, ‖minusPair a u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      gammaCk * (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) := by
  have hc := minus_carleman_integrable_and_le a hu hv
  have hDom : Integrable (fun p => gammaCk * minusMajorant a u v p)
      ((intervalMeasure a).prod (intervalMeasure a)) := hc.1.const_mul gammaCk
  have hLe : ∀ᵐ p ∂(intervalMeasure a).prod (intervalMeasure a),
      ‖minusPair a u v p‖ ≤ gammaCk * minusMajorant a u v p := by
    filter_upwards [interval_product_membership a] with p hp
    exact minusPair_norm_le hp.1 hp.2
  have hInt : Integrable (minusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    hDom.mono' (minusPair_aestronglyMeasurable a hu hv) hLe
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ p, gammaCk * minusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) :=
      integral_mono_ae hInt.norm hDom hLe
    _ = gammaCk * ∫ p, minusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.2 gammaCk_pos.le

end D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

open Filter
open scoped Topology

private def twoCornerPair (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  plusPair a u v p + minusPair a u v p

def twoCornerMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  gammaCk * (plusMajorant a u v p + minusMajorant a u v p)

theorem twoCornerMajorant_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerMajorant a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact ((plus_carleman_integrable_and_le a hu hv).1.add
    (minus_carleman_integrable_and_le a hu hv).1).const_mul gammaCk

/-- Quantitative original-corner majorant used by the full image-boundary bound. -/
theorem twoCornerMajorant_integral_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    (∫ p, twoCornerMajorant a u v p
      ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      2 * gammaCk * Real.pi *
        Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  have hp := plus_carleman_integrable_and_le a hu hv
  have hm := minus_carleman_integrable_and_le a hu hv
  calc
    _ = gammaCk * ((∫ p, plusMajorant a u v p
          ∂(intervalMeasure a).prod (intervalMeasure a)) +
        ∫ p, minusMajorant a u v p
          ∂(intervalMeasure a).prod (intervalMeasure a)) := by
      simp only [twoCornerMajorant, integral_const_mul, integral_add hp.1 hm.1]
    _ ≤ gammaCk * ((Real.pi *
          Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
          Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) +
        (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
          Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a))) :=
      mul_le_mul_of_nonneg_left (add_le_add hp.2 hm.2) gammaCk_pos.le
    _ = _ := by ring

private theorem twoCornerPair_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact (plus_actual_corner_integrable_and_le a hu hv).1.add
    (minus_actual_corner_integrable_and_le a hu hv).1

private theorem twoCornerCutoffPair_integrable (a ε : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerCutoffPair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hDp : Measurable (plusDistance a) := by unfold plusDistance; fun_prop
  have hDm : Measurable (minusDistance a) := by unfold minusDistance; fun_prop
  exact ((plus_actual_corner_integrable_and_le a hu hv).1.indicator
    (measurableSet_lt measurable_const hDp)).add
      ((minus_actual_corner_integrable_and_le a hu hv).1.indicator
        (measurableSet_lt measurable_const hDm))

theorem twoCornerCutoffPair_norm_le {a ε : ℝ} {u v : ℝ → ℂ}
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖twoCornerCutoffPair a ε u v p‖ ≤ twoCornerMajorant a u v p := by
  calc
    _ ≤ ‖{q | ε < plusDistance a q}.indicator (plusPair a u v) p‖ +
        ‖{q | ε < minusDistance a q}.indicator (minusPair a u v) p‖ :=
      norm_add_le _ _
    _ ≤ ‖plusPair a u v p‖ + ‖minusPair a u v p‖ :=
      add_le_add
        (norm_indicator_le_norm_self (s := {q | ε < plusDistance a q})
          (plusPair a u v) p)
        (norm_indicator_le_norm_self (s := {q | ε < minusDistance a q})
          (minusPair a u v) p)
    _ ≤ gammaCk * plusMajorant a u v p + gammaCk * minusMajorant a u v p :=
      add_le_add (plusPair_norm_le hx hy) (minusPair_norm_le hx hy)
    _ = twoCornerMajorant a u v p := by unfold twoCornerMajorant; ring

private theorem indicator_sub_norm_le {s : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) :
    ‖s.indicator f p - f p‖ ≤ ‖f p‖ := by
  by_cases hp : p ∈ s <;> simp [hp]

private theorem twoCornerCutoffPair_sub_norm_le {a ε : ℝ} {u v : ℝ → ℂ}
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖ ≤
      twoCornerMajorant a u v p := by
  have heq : twoCornerCutoffPair a ε u v p - twoCornerPair a u v p =
      ({q | ε < plusDistance a q}.indicator (plusPair a u v) p -
        plusPair a u v p) +
      ({q | ε < minusDistance a q}.indicator (minusPair a u v) p -
        minusPair a u v p) := by
    unfold twoCornerCutoffPair twoCornerPair
    ring
  rw [heq]
  calc
    _ ≤ ‖{q | ε < plusDistance a q}.indicator (plusPair a u v) p -
          plusPair a u v p‖ +
        ‖{q | ε < minusDistance a q}.indicator (minusPair a u v) p -
          minusPair a u v p‖ := norm_add_le _ _
    _ ≤ ‖plusPair a u v p‖ + ‖minusPair a u v p‖ :=
      add_le_add (indicator_sub_norm_le (plusPair a u v) p)
        (indicator_sub_norm_le (minusPair a u v) p)
    _ ≤ gammaCk * plusMajorant a u v p + gammaCk * minusMajorant a u v p :=
      add_le_add (plusPair_norm_le hx hy) (minusPair_norm_le hx hy)
    _ = twoCornerMajorant a u v p := by unfold twoCornerMajorant; ring

private theorem twoCornerCutoffPair_tendsto {a : ℝ} {u v : ℝ → ℂ}
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Tendsto (fun ε : ℝ => twoCornerCutoffPair a ε u v p)
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (twoCornerPair a u v p)) := by
  have hd := distances_pos hx hy
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      ε < min (plusDistance a p) (minusDistance a p) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hd.1 hd.2))
  apply tendsto_const_nhds.congr'
  filter_upwards [hsmall] with ε hε
  have hp : ε < plusDistance a p := lt_of_lt_of_le hε (min_le_left _ _)
  have hm : ε < minusDistance a p := lt_of_lt_of_le hε (min_le_right _ _)
  simp [twoCornerCutoffPair, twoCornerPair, hp, hm]

private theorem twoCornerCutoffPair_integral_tendsto (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Tendsto
      (fun ε : ℝ => ∫ p, twoCornerCutoffPair a ε u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ p, twoCornerPair a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))) := by
  apply tendsto_integral_filter_of_dominated_convergence (twoCornerMajorant a u v)
  · exact Eventually.of_forall fun ε =>
      (twoCornerCutoffPair_integrable a ε hu hv).aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [interval_product_membership a] with p hp
    exact twoCornerCutoffPair_norm_le hp.1 hp.2
  · exact twoCornerMajorant_integrable a hu hv
  · filter_upwards [interval_product_membership a] with p hp
    exact twoCornerCutoffPair_tendsto hp.1 hp.2

private theorem twoCornerCutoffPair_L1_tendsto (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Tendsto
      (fun ε : ℝ => ∫ p,
        ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hFull := (twoCornerPair_integrable a hu hv).aestronglyMeasurable
  have hDCT : Tendsto
      (fun ε : ℝ => ∫ p,
        ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ _p : ℝ × ℝ, (0 : ℝ)
        ∂(intervalMeasure a).prod (intervalMeasure a))) := by
    apply tendsto_integral_filter_of_dominated_convergence (twoCornerMajorant a u v)
    · exact Eventually.of_forall fun ε =>
        ((twoCornerCutoffPair_integrable a ε hu hv).aestronglyMeasurable.sub hFull).norm
    · apply Eventually.of_forall
      intro ε
      filter_upwards [interval_product_membership a] with p hp
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact twoCornerCutoffPair_sub_norm_le hp.1 hp.2
    · exact twoCornerMajorant_integrable a hu hv
    · filter_upwards [interval_product_membership a] with p hp
      have hPoint := twoCornerCutoffPair_tendsto (u := u) (v := v) hp.1 hp.2
      simpa only [sub_self, norm_zero] using (hPoint.sub (tendsto_const_nhds (x := twoCornerPair a u v p))).norm
  simpa only [integral_zero] using hDCT

end D5.S3.Weil.ZetaGamma.FormCore.Corner

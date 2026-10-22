/- GID: D5/S3/Weil/ZetaGamma/FormCore/Carleman
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/Carleman
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Carleman absolute pairing on the positive half-line. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
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
import Mathlib.Analysis.SumIntegralComparisons
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

namespace D5.S3.Weil.ZetaGamma.FormCore.Carleman

abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

def rowKernel (r s : ℝ) : ℝ :=
  Real.sqrt r / (Real.sqrt s * (r + s))

theorem actual_row_integrable_integral {r : ℝ} (hr : 0 < r) :
    Integrable (rowKernel r) positiveMeasure ∧
      (∫ s, rowKernel r s ∂positiveMeasure) = Real.pi := by
  let R := Real.sqrt r
  have hR : 0 < R := Real.sqrt_pos.mpr hr
  have hR2 : R ^ 2 = r := Real.sq_sqrt hr.le
  let g : ℝ → ℝ := fun t => 2 * t * rowKernel r (t ^ 2)
  have hscaled (z : ℝ) (hz : 0 < z) :
      g (R * z) = (2 / R) * (1 + z ^ 2)⁻¹ := by
    change 2 * (R * z) *
      (R / (Real.sqrt ((R * z) ^ 2) * (r + (R * z) ^ 2))) =
        (2 / R) * (1 + z ^ 2)⁻¹
    rw [Real.sqrt_sq (mul_nonneg hR.le hz.le)]
    have hOne : 0 < 1 + z ^ 2 := by positivity
    rw [← hR2]
    have hDen : R ^ 2 + (R * z) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hR.ne', hz.ne', hOne.ne', hDen] <;> ring
  have hscaled_ae :
      (fun z => g (R * z)) =ᵐ[positiveMeasure]
        (fun z => (2 / R) * (1 + z ^ 2)⁻¹) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hscaled z hz
  have hbase : Integrable (fun z : ℝ => (2 / R) * (1 + z ^ 2)⁻¹)
      positiveMeasure :=
    integrable_inv_one_add_sq.integrableOn.const_mul (2 / R)
  have hg : Integrable g positiveMeasure := by
    have hs : IntegrableOn (fun z => g (R * z)) (Ioi 0) :=
      hbase.congr hscaled_ae.symm
    have hi := (integrableOn_Ioi_comp_mul_left_iff g 0 hR).mp hs
    simpa only [mul_zero, IntegrableOn, positiveMeasure] using hi
  have hpow_int :
      Integrable (fun t : ℝ =>
        (|(2 : ℝ)| * t ^ ((2 : ℝ) - 1)) • rowKernel r (t ^ (2 : ℝ)))
        positiveMeasure := by
    simpa only [show |(2 : ℝ)| = 2 by norm_num,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      smul_eq_mul] using hg
  have hrow : Integrable (rowKernel r) positiveMeasure :=
    (integrableOn_Ioi_comp_rpow_iff (rowKernel r) (p := 2) (by norm_num)).mp hpow_int
  have hpow : (∫ t, g t ∂positiveMeasure) =
      ∫ s, rowKernel r s ∂positiveMeasure := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, Real.rpow_two, smul_eq_mul] using
      (integral_comp_rpow_Ioi_of_pos (g := rowKernel r) (p := 2) (by norm_num))
  have hscale : (∫ z, g (R * z) ∂positiveMeasure) =
      R⁻¹ * ∫ t, g t ∂positiveMeasure := by
    simpa only [mul_zero, smul_eq_mul] using integral_comp_mul_left_Ioi g 0 hR
  have hscaled_value : (∫ z, g (R * z) ∂positiveMeasure) =
      (2 / R) * (Real.pi / 2) := by
    rw [integral_congr_ae hscaled_ae, integral_const_mul]
    simp only [positiveMeasure, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero, sub_zero]
  refine ⟨hrow, ?_⟩
  calc
    (∫ s, rowKernel r s ∂positiveMeasure) =
        ∫ t, g t ∂positiveMeasure := hpow.symm
    _ = R * ∫ z, g (R * z) ∂positiveMeasure := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
    _ = R * ((2 / R) * (Real.pi / 2)) := by rw [hscaled_value]
    _ = Real.pi := by field_simp [hR.ne'] <;> ring

theorem row_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 ≤ rowKernel r s := by
  exact div_nonneg (Real.sqrt_nonneg r)
    (mul_nonneg (Real.sqrt_nonneg s) (add_pos hr hs).le)

/-! A finite row is paid against the complete original Carleman row.

This is deliberately stated over `Ioc 0 N`: the endpoint `0` is a null
point where the division-defined value of `rowKernel` is zero, so the
global `Ici 0` antitone API is not applicable.  The `Icc` integrability
needed by the comparison theorem is obtained from the original `Ioi`
integrability through the null-endpoint equivalence. -/
lemma rowKernel_antitoneOn (m : ℕ) (hm : 0 < m) (N : ℕ) :
    AntitoneOn (rowKernel (m : ℝ)) (Ioc (0 : ℝ) (N : ℝ)) := by
  intro x hx y hy hxy
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx0 : 0 < x := hx.1
  have hy0 : 0 < y := hy.1
  have hsqrt : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hsum : (m : ℝ) + x ≤ (m : ℝ) + y := by linarith
  have hden : Real.sqrt x * ((m : ℝ) + x) ≤
      Real.sqrt y * ((m : ℝ) + y) := by
    exact mul_le_mul hsqrt hsum (add_pos hm0 hx0).le (Real.sqrt_nonneg _)
  have hdx : 0 < Real.sqrt x * ((m : ℝ) + x) := by positivity
  have hdy : 0 < Real.sqrt y * ((m : ℝ) + y) := by positivity
  apply (div_le_div_iff₀ hdy hdx).2
  exact mul_le_mul_of_nonneg_left hden (Real.sqrt_nonneg _)

theorem finite_row_sum_le_pi {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Finset.range N, rowKernel (m : ℝ) ((n + 1 : ℕ) : ℝ) ≤ Real.pi := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hfull := actual_row_integrable_integral (r := (m : ℝ)) hm0
  have hIoi : IntegrableOn (rowKernel (m : ℝ)) (Ioi (0 : ℝ)) := by
    simpa only [positiveMeasure, IntegrableOn] using hfull.1
  have hIoc : IntegrableOn (rowKernel (m : ℝ)) (Ioc (0 : ℝ) (N : ℝ)) :=
    hIoi.mono_set Ioc_subset_Ioi_self
  have hIcc : IntegrableOn (rowKernel (m : ℝ)) (Icc (0 : ℝ) (N : ℝ)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 hIoc
  have hsum := AntitoneOn.sum_le_integral_of_integrableOn
    (a := N) (x₀ := (0 : ℝ))
    (by simpa only [zero_add] using rowKernel_antitoneOn m hm N)
    (by simpa only [zero_add] using hIcc)
  simp only [zero_add] at hsum
  have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [intervalIntegral.integral_of_le hN] at hsum
  have hmono :
      (∫ x in Ioc (0 : ℝ) (N : ℝ), rowKernel (m : ℝ) x) ≤
        ∫ x in Ioi (0 : ℝ), rowKernel (m : ℝ) x := by
    apply setIntegral_mono_set hIoi
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact row_nonneg hm0 hx
    · exact Ioc_subset_Ioi_self.eventuallySubset
  calc
    ∑ n ∈ Finset.range N, rowKernel (m : ℝ) ((n + 1 : ℕ) : ℝ) ≤
        ∫ x in Ioc (0 : ℝ) (N : ℝ), rowKernel (m : ℝ) x := by
      simpa only [zero_add, Nat.cast_add, Nat.cast_one] using hsum
    _ ≤ ∫ x in Ioi (0 : ℝ), rowKernel (m : ℝ) x := hmono
    _ = Real.pi := hfull.2

/-! Fin-index form used by the scaled complex-row owner. -/
theorem finite_row_sum_le_pi_fin {m d : ℕ} (hm : 0 < m) :
    ∑ n : Fin d, rowKernel (m : ℝ) (((n.1 + 1 : ℕ) : ℝ)) ≤ Real.pi := by
  classical
  have henum (N : ℕ) :
      (∑ n : Fin N, rowKernel (m : ℝ) (((n.1 + 1 : ℕ) : ℝ))) =
        ∑ n ∈ Finset.range N, rowKernel (m : ℝ) ((n + 1 : ℕ) : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Fin.sum_univ_castSucc, Finset.sum_range_succ]
      change (∑ n : Fin N, rowKernel (m : ℝ) (((n.1 + 1 : ℕ) : ℝ))) +
        rowKernel (m : ℝ) ((N + 1 : ℕ) : ℝ) = _
      rw [ih]
  rw [henum d]
  exact finite_row_sum_le_pi hm d

private def squareMajorant (u : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ ^ 2 * rowKernel p.1 p.2

private theorem square_majorant_integrable_integral
    {u : ℝ → ℂ} (hu : MemLp u 2 positiveMeasure) :
    Integrable (squareMajorant u) (positiveMeasure.prod positiveMeasure) ∧
      (∫ p, squareMajorant u p ∂positiveMeasure.prod positiveMeasure) =
        Real.pi * ∫ r, ‖u r‖ ^ 2 ∂positiveMeasure := by
  have hu2 : Integrable (fun r => ‖u r‖ ^ 2) positiveMeasure :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hK : Measurable (fun p : ℝ × ℝ => rowKernel p.1 p.2) := by
    dsimp [rowKernel]
    fun_prop
  have hM : AEStronglyMeasurable (squareMajorant u)
      (positiveMeasure.prod positiveMeasure) :=
    (hu2.aestronglyMeasurable.comp_fst).mul hK.aestronglyMeasurable
  have hInner (r : ℝ) (hr : 0 < r) :
      (∫ s, squareMajorant u (r, s) ∂positiveMeasure) = Real.pi * ‖u r‖ ^ 2 := by
    dsimp only [squareMajorant]
    rw [integral_const_mul, (actual_row_integrable_integral hr).2, mul_comm]
  have hNormInner (r : ℝ) (hr : 0 < r) :
      (∫ s, ‖squareMajorant u (r, s)‖ ∂positiveMeasure) = Real.pi * ‖u r‖ ^ 2 := by
    calc
      _ = ∫ s, squareMajorant u (r, s) ∂positiveMeasure := by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (row_nonneg hr hs))
      _ = _ := hInner r hr
  have hInt : Integrable (squareMajorant u)
      (positiveMeasure.prod positiveMeasure) := by
    apply (integrable_prod_iff hM).2
    constructor
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact ((actual_row_integrable_integral hr).1).const_mul (‖u r‖ ^ 2)
    · apply (hu2.const_mul Real.pi).congr
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact (hNormInner r hr).symm
  refine ⟨hInt, ?_⟩
  rw [integral_prod _ hInt]
  calc
    _ = ∫ r, Real.pi * ‖u r‖ ^ 2 ∂positiveMeasure := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hInner r hr
    _ = _ := integral_const_mul _ _

private theorem actual_carleman_l2_pairing
    {u v : ℝ → ℂ} (hu : MemLp u 2 positiveMeasure) (hv : MemLp v 2 positiveMeasure) :
    Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2))
      (positiveMeasure.prod positiveMeasure) ∧
    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
      ∂positiveMeasure.prod positiveMeasure) ≤
      (Real.pi / 2) * ((∫ r, ‖u r‖ ^ 2 ∂positiveMeasure) +
        ∫ s, ‖v s‖ ^ 2 ∂positiveMeasure) := by
  let F : ℝ × ℝ → ℝ := fun p => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
  let A := squareMajorant u
  let B : ℝ × ℝ → ℝ := fun p => squareMajorant v p.swap
  have hA := square_majorant_integrable_integral hu
  have hV := square_majorant_integrable_integral hv
  have hB : Integrable B (positiveMeasure.prod positiveMeasure) := hV.1.swap
  have hBI : (∫ p, B p ∂positiveMeasure.prod positiveMeasure) =
      Real.pi * ∫ s, ‖v s‖ ^ 2 ∂positiveMeasure := by
    change (∫ p, squareMajorant v p.swap ∂positiveMeasure.prod positiveMeasure) = _
    rw [integral_prod_swap]
    exact hV.2
  have hPos : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      0 < p.1 ∧ 0 < p.2 := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact ⟨hr, hs⟩
  have hPoint (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
      2 * F (r, s) ≤ A (r, s) + B (r, s) := by
    have hR : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hS : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hD : 0 < Real.sqrt r * Real.sqrt s * (r + s) := by positivity
    have hEq : (A (r, s) + B (r, s) - 2 * F (r, s)) *
        (Real.sqrt r * Real.sqrt s * (r + s)) =
        (‖u r‖ * Real.sqrt r - ‖v s‖ * Real.sqrt s) ^ 2 := by
      dsimp [F, A, B, squareMajorant, rowKernel]
      field_simp [hR.ne', hS.ne', (add_pos hr hs).ne', (add_pos hs hr).ne'] <;> ring
    have hp : 0 ≤ (A (r, s) + B (r, s) - 2 * F (r, s)) *
        (Real.sqrt r * Real.sqrt s * (r + s)) := by
      rw [hEq]
      exact sq_nonneg _
    have hh : 0 ≤ A (r, s) + B (r, s) - 2 * F (r, s) :=
      nonneg_of_mul_nonneg_left hp hD
    linarith
  have hFm : AEStronglyMeasurable F (positiveMeasure.prod positiveMeasure) :=
    (hu.aestronglyMeasurable.norm.comp_fst.mul hv.aestronglyMeasurable.norm.comp_snd).div₀
      (measurable_fst.add measurable_snd).aestronglyMeasurable
  have hDomInt : Integrable (fun p => (1 / 2 : ℝ) * (A p + B p))
      (positiveMeasure.prod positiveMeasure) := (hA.1.add hB).const_mul (1 / 2)
  have hLe : ∀ᵐ p ∂positiveMeasure.prod positiveMeasure,
      F p ≤ (1 / 2 : ℝ) * (A p + B p) := by
    filter_upwards [hPos] with p hp
    have h := hPoint p.1 p.2 hp.1 hp.2
    nlinarith
  have hF : Integrable F (positiveMeasure.prod positiveMeasure) := by
    apply hDomInt.mono' hFm
    filter_upwards [hPos, hLe] with p hp hle
    rw [Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (add_pos hp.1 hp.2).le)]
    exact hle
  refine ⟨hF, (integral_mono_ae hF hDomInt hLe).trans_eq ?_⟩
  rw [integral_const_mul, integral_add hA.1 hB, hA.2, hBI]
  ring

theorem carleman_integrable_and_integral_le
    {u v : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioi 0)))
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :
    Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ≤
      Real.pi * Real.sqrt (∫ r, ‖u r‖ ^ 2 ∂volume.restrict (Ioi 0)) *
        Real.sqrt (∫ s, ‖v s‖ ^ 2 ∂volume.restrict (Ioi 0)) := by
  refine ⟨(actual_carleman_l2_pairing hu hv).1, ?_⟩
  let F : ℝ × ℝ → ℝ := fun p => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
  let J : ℝ := ∫ p, F p ∂positiveMeasure.prod positiveMeasure
  let Eu : ℝ := ∫ r, ‖u r‖ ^ 2 ∂positiveMeasure
  let Ev : ℝ := ∫ s, ‖v s‖ ^ 2 ∂positiveMeasure
  change J ≤ Real.pi * Real.sqrt Eu * Real.sqrt Ev
  have hu2 : Integrable (fun r => ‖u r‖ ^ 2) positiveMeasure :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hv2 : Integrable (fun s => ‖v s‖ ^ 2) positiveMeasure :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hEu0 : 0 ≤ Eu := integral_nonneg (fun r => sq_nonneg ‖u r‖)
  have hEv0 : 0 ≤ Ev := integral_nonneg (fun s => sq_nonneg ‖v s‖)
  by_cases hEu : Eu = 0
  · have huZeroSq : ∀ᵐ r ∂positiveMeasure, ‖u r‖ ^ 2 = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun r => sq_nonneg ‖u r‖) hu2).mp hEu
    have huZero : ∀ᵐ r ∂positiveMeasure, ‖u r‖ = 0 := by
      filter_upwards [huZeroSq] with r hr
      exact sq_eq_zero_iff.mp hr
    have huProdZero : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ‖u p.1‖ = 0 :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae huZero
    have hJ : J = 0 := by
      change (∫ p, F p ∂positiveMeasure.prod positiveMeasure) = 0
      calc
        _ = ∫ _p : ℝ × ℝ, (0 : ℝ) ∂positiveMeasure.prod positiveMeasure := by
          apply integral_congr_ae
          filter_upwards [huProdZero] with p hp
          simp [F, hp]
        _ = 0 := by simp
    rw [hJ, hEu]
    simp
  by_cases hEv : Ev = 0
  · have hvZeroSq : ∀ᵐ s ∂positiveMeasure, ‖v s‖ ^ 2 = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => sq_nonneg ‖v s‖) hv2).mp hEv
    have hvZero : ∀ᵐ s ∂positiveMeasure, ‖v s‖ = 0 := by
      filter_upwards [hvZeroSq] with s hs
      exact sq_eq_zero_iff.mp hs
    have hvProdZero : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ‖v p.2‖ = 0 :=
      MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hvZero
    have hJ : J = 0 := by
      change (∫ p, F p ∂positiveMeasure.prod positiveMeasure) = 0
      calc
        _ = ∫ _p : ℝ × ℝ, (0 : ℝ) ∂positiveMeasure.prod positiveMeasure := by
          apply integral_congr_ae
          filter_upwards [hvProdZero] with p hp
          simp [F, hp]
        _ = 0 := by simp
    rw [hJ, hEv]
    simp
  let a : ℝ := Real.sqrt Eu
  let b : ℝ := Real.sqrt Ev
  have ha : 0 < a := Real.sqrt_pos.mpr (lt_of_le_of_ne hEu0 (Ne.symm hEu))
  have hb : 0 < b := Real.sqrt_pos.mpr (lt_of_le_of_ne hEv0 (Ne.symm hEv))
  have ha2 : a ^ 2 = Eu := Real.sq_sqrt hEu0
  have hb2 : b ^ 2 = Ev := Real.sq_sqrt hEv0
  have hEnergy (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℂ) :
      (∫ r, ‖(c • f) r‖ ^ 2 ∂positiveMeasure) =
        c ^ 2 * ∫ r, ‖f r‖ ^ 2 ∂positiveMeasure := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc, mul_pow]
    exact integral_const_mul _ _
  have hPairScale :
      (∫ p : ℝ × ℝ, ‖(b • u) p.1‖ * ‖(a • v) p.2‖ / (p.1 + p.2)
        ∂positiveMeasure.prod positiveMeasure) = (b * a) * J := by
    calc
      _ = ∫ p, (b * a) * F p ∂positiveMeasure.prod positiveMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          dsimp only [F]
          simp only [Pi.smul_apply, norm_smul,
            Real.norm_of_nonneg hb.le, Real.norm_of_nonneg ha.le]
          ring
      _ = _ := integral_const_mul _ _
  have hBalanced :=
    (actual_carleman_l2_pairing (hu.const_smul b) (hv.const_smul a)).2
  rw [hPairScale, hEnergy b hb.le u, hEnergy a ha.le v] at hBalanced
  change (b * a) * J ≤ (Real.pi / 2) * (b ^ 2 * Eu + a ^ 2 * Ev) at hBalanced
  change J ≤ Real.pi * a * b
  apply (mul_le_mul_iff_of_pos_left (mul_pos hb ha)).mp
  refine hBalanced.trans_eq ?_
  rw [← ha2, ← hb2]
  ring

end D5.S3.Weil.ZetaGamma.FormCore.Carleman

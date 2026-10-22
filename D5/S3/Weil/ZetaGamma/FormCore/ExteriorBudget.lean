/- GID: D5/S3/Weil/ZetaGamma/FormCore/ExteriorBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/ExteriorBudget
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Actual-Gamma exterior mass budget. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CornerTransport
import D5.S3.Weil.ZetaGamma.FormCore.DirectionalEnergy
import D5.S3.Weil.ZetaGamma.FormCore.SmoothCutoff
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

namespace D5.S3.Weil.ZetaGamma.FormCore

open D5.S3.Weil.ZetaGamma.FormCore.Corner

abbrev actualGammaExitMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (actualDensity s))

private theorem actual_gamma_tail_lintegral_eq_ofReal {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ r in Ioi δ, ENNReal.ofReal (actualDensity r)) =
      ENNReal.ofReal (∫ r in Ioi δ, actualDensity r) := by
  have hρ := actualDensity_tail_integrable_for_cutoff hδ
  have hnn : ∀ᵐ r ∂volume.restrict (Ioi δ), 0 ≤ actualDensity r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact (actual_density_pos (hδ.trans hr)).le
  exact (ofReal_integral_eq_lintegral_ofReal hρ hnn).symm

theorem actual_gamma_exteriorPotential_eq_ofReal {a y : ℝ}
    (hy : y ∈ Ioo (-a) a) :
    exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y =
      ENNReal.ofReal (actualExteriorPotential a y) := by
  have hleft : 0 < a + y := by linarith [hy.1]
  have hright : 0 < a - y := sub_pos.mpr hy.2
  have hρ : Measurable (fun r => ENNReal.ofReal (actualDensity r)) :=
    actual_density_measurable.ennreal_ofReal
  have hpair : Measurable (exteriorExitPair (Ioo (-a) a) y) := by
    unfold exteriorExitPair
    have h0 : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)) := measurable_const
    have h1 : Measurable (fun _ : ℝ => (1 : ℝ≥0∞)) := measurable_const
    exact (Measurable.ite (measurableSet_Ioo.preimage (measurable_const.sub measurable_id))
      h0 h1).add
      (Measurable.ite (measurableSet_Ioo.preimage (measurable_const.add measurable_id))
        h0 h1)
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal (actualDensity r) * exteriorExitPair (Ioo (-a) a) y r =
        (Ici (a + y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r +
          (Ici (a - y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    change (0 : ℝ) < r at hr
    have hm : y - r ∈ Ioo (-a) a ↔ r < a + y := by
      constructor
      · intro h
        linarith [h.1]
      · intro h
        constructor <;> linarith [hy.2]
    have hp : y + r ∈ Ioo (-a) a ↔ r < a - y := by
      constructor
      · intro h
        linarith [h.2]
      · intro h
        constructor <;> linarith [hy.1]
    simp only [exteriorExitPair, hm, hp, Set.indicator, mem_Ici, ← not_lt]
    by_cases hm' : r < a + y <;> by_cases hp' : r < a - y <;>
      simp [hm', hp', mul_add]
  have hleft_subset : Ici (a + y) ⊆ Ioi (0 : ℝ) :=
    fun r hr => hleft.trans_le hr
  have hright_subset : Ici (a - y) ⊆ Ioi (0 : ℝ) :=
    fun r hr => hright.trans_le hr
  calc
    exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y =
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (actualDensity r) *
          exteriorExitPair (Ioo (-a) a) y r := by
      unfold exteriorPotential actualGammaExitMeasure
      exact lintegral_withDensity_eq_lintegral_mul _ hρ hpair
    _ = ∫⁻ r in Ioi (0 : ℝ),
        (Ici (a + y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r +
          (Ici (a - y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r :=
      lintegral_congr_ae hpoint
    _ = (∫⁻ r in Ici (a + y), ENNReal.ofReal (actualDensity r)) +
        ∫⁻ r in Ici (a - y), ENNReal.ofReal (actualDensity r) := by
      rw [lintegral_add_left (hρ.indicator measurableSet_Ici),
        lintegral_indicator measurableSet_Ici, lintegral_indicator measurableSet_Ici,
        Measure.restrict_restrict_of_subset hleft_subset,
        Measure.restrict_restrict_of_subset hright_subset]
    _ = (∫⁻ r in Ioi (a + y), ENNReal.ofReal (actualDensity r)) +
        ∫⁻ r in Ioi (a - y), ENNReal.ofReal (actualDensity r) := by
      rw [← restrict_Ioi_eq_restrict_Ici (μ := (volume : Measure ℝ)) (a := a + y),
        ← restrict_Ioi_eq_restrict_Ici (μ := (volume : Measure ℝ)) (a := a - y)]
    _ = ENNReal.ofReal (∫ r in Ioi (a + y), actualDensity r) +
        ENNReal.ofReal (∫ r in Ioi (a - y), actualDensity r) := by
      rw [actual_gamma_tail_lintegral_eq_ofReal hleft,
        actual_gamma_tail_lintegral_eq_ofReal hright]
    _ = ENNReal.ofReal (actualExteriorPotential a y) := by
      rw [actualExteriorPotential,
        ENNReal.ofReal_add (actualDensity_tail_nonneg hright) (actualDensity_tail_nonneg hleft)]
      exact add_comm _ _

private theorem actual_gamma_exterior_budget (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F) (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) :
    (∫⁻ y in Ioo (-a) a, ‖F y‖ₑ ^ 2 * ENNReal.ofReal (actualExteriorPotential a y)) ≤
      directionalEnergy actualGammaExitMeasure F := by
  calc
    _ = ∫⁻ y in Ioo (-a) a,
        ‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
      rw [actual_gamma_exteriorPotential_eq_ofReal hy]
    _ ≤ ∫⁻ y : ℝ,
        ‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ directionalEnergy actualGammaExitMeasure F :=
      exterior_mass_le_directionalEnergy actualGammaExitMeasure (Ioo (-a) a)
        measurableSet_Ioo F hF hzero

private theorem actual_gamma_exteriorPotential_measurable (a : ℝ) :
    Measurable (exteriorPotential actualGammaExitMeasure (Ioo (-a) a)) := by
  have hpair : Measurable (fun p : ℝ × ℝ => exteriorExitPair (Ioo (-a) a) p.1 p.2) := by
    unfold exteriorExitPair
    have h0 : Measurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)) := measurable_const
    have h1 : Measurable (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) := measurable_const
    exact (Measurable.ite (measurableSet_Ioo.preimage (measurable_fst.sub measurable_snd))
      h0 h1).add
      (Measurable.ite (measurableSet_Ioo.preimage (measurable_fst.add measurable_snd))
        h0 h1)
  exact hpair.lintegral_prod_right'

private theorem actual_gamma_exterior_weight_integrable (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (hEnergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    IntegrableOn (fun y => (1 + actualExteriorPotential a y) * ‖F y‖ ^ 2)
      (Ioo (-a) a) := by
  let W : ℝ → ℝ≥0∞ := fun y =>
    ‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y
  have hWm : Measurable W :=
    (hF.enorm.pow_const 2).mul (actual_gamma_exteriorPotential_measurable a)
  have hbudget := actual_gamma_exterior_budget a F hF hzero
  have hWfinite : (∫⁻ y in Ioo (-a) a, W y) < (⊤ : ℝ≥0∞) := by
    have heq : (∫⁻ y in Ioo (-a) a, W y) =
        ∫⁻ y in Ioo (-a) a, ‖F y‖ₑ ^ 2 * ENNReal.ofReal (actualExteriorPotential a y) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
      dsimp only [W]
      rw [actual_gamma_exteriorPotential_eq_ofReal hy]
    rw [heq]
    exact hbudget.trans_lt hEnergy
  have hWi : IntegrableOn (fun y => (W y).toReal) (Ioo (-a) a) :=
    integrable_toReal_of_lintegral_ne_top hWm.aemeasurable.restrict hWfinite.ne
  have hprod : IntegrableOn (fun y => ‖F y‖ ^ 2 * actualExteriorPotential a y)
      (Ioo (-a) a) := by
    apply IntegrableOn.congr_fun hWi _ measurableSet_Ioo
    intro y hy
    have hleft : 0 < a + y := by linarith [hy.1]
    have hright : 0 < a - y := sub_pos.mpr hy.2
    have hV : 0 ≤ actualExteriorPotential a y :=
      add_nonneg (actualDensity_tail_nonneg hright) (actualDensity_tail_nonneg hleft)
    dsimp only [W]
    rw [actual_gamma_exteriorPotential_eq_ofReal hy]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm,
      ENNReal.toReal_ofReal hV]
  have hmass : Integrable (fun y => ‖F y‖ ^ 2) :=
    hF₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply IntegrableOn.congr_fun (hmass.integrableOn.add hprod) _ measurableSet_Ioo
  intro y _hy
  simp only [Pi.add_apply]
  ring

end D5.S3.Weil.ZetaGamma.FormCore

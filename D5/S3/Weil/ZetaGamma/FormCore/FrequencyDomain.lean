/- GID: D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/FrequencyDomain
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Original-Ioc actual-Gamma frequency domain. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
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

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

open MeasureTheory Set
open scoped ENNReal

private theorem actual_gamma_zero_domain_iff_periodic_frequency_sum_finite
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      (∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.phaseGap
              (d := 2 * a) n s)) *
        ENNReal.ofReal
          (‖D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.physicalCoeff
            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < (∞ : ℝ≥0∞) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have huCommon : MemLp u 2
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a)) := by
    simpa only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure, hend] using hu
  have hdensity : Measurable density := by
    unfold density
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hmeas : AEStronglyMeasurable
      (periodicEnergyDensity (2 * a) (-a) u) (volume.restrict (Ioi (0 : ℝ))) := by
    have h := hdensity.aestronglyMeasurable.mul
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy_aestronglyMeasurable
        (2 * a) (-a) u huCommon)
    exact h.restrict
  have hnonneg : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ periodicEnergyDensity (2 * a) (-a) u s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hMass (s : ℝ) :
      D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.windowGapMass
        (d := 2 * a) (-a) u s =
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy
        (2 * a) (-a) u s := by
    simp only [D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.windowGapMass,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicExtension,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure,
      Complex.normSq_eq_norm_sq]
  have hEnergy :=
    D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.extended_window_energy_eq_tsum
      density hdensity (-a) u huCommon
  have hLinear :
      (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (periodicEnergyDensity (2 * a) (-a) u s)) =
      ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.windowGapMass
              (d := 2 * a) (-a) u s) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [hMass]
    exact ENNReal.ofReal_mul (density_nonneg hs)
  rw [(actual_centered_gamma_full_domain_equivalence a ha u hu).1]
  rw [← hEnergy, ← hLinear]
  exact ⟨fun h => (hasFiniteIntegral_iff_ofReal hnonneg).mp h.2,
    fun h => ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).mpr h⟩⟩

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

open MeasureTheory Set
open scoped ENNReal

theorem actual_gamma_zero_domain_iff_digamma_weighted_sum_finite
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      (∑' n : ℤ,
        ENNReal.ofReal
          (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaIncrement
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.angularFrequency
              (d := 2 * a) n)) *
        ENNReal.ofReal
          (‖D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.physicalCoeff
            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < (∞ : ℝ≥0∞) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hweight (n : ℤ) :
      (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.phaseGap
              (d := 2 * a) n s)) =
        ENNReal.ofReal
          (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaIncrement
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.angularFrequency
              (d := 2 * a) n)) := by
    simpa only [density,
      D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaDensity] using
      D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight
        (d := 2 * a) n
  simpa only [hweight] using
    actual_gamma_zero_domain_iff_periodic_frequency_sum_finite a ha u hu

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
open AddCircle
open D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy
variable {d : ℝ} [hd : Fact (0 < d)]

private def finiteFourierPolynomial (f : AddCircle d → ℂ) (S : Finset ℤ) :
    AddCircle d → ℂ := fun x => ∑ n ∈ S, fourierCoeff f n * fourier n x

private theorem finiteFourierPolynomial_memLp (f : AddCircle d → ℂ) (S : Finset ℤ) :
    MemLp (finiteFourierPolynomial f S) 2 haarAddCircle := by
  exact memLp_finsetSum S (fun n _ =>
    ((fourier n).memLp haarAddCircle ℂ).const_mul (fourierCoeff f n))

private theorem finiteFourierPolynomial_coeff (f : AddCircle d → ℂ)
    (S : Finset ℤ) (k : ℤ) :
    fourierCoeff (finiteFourierPolynomial f S) k =
      if k ∈ S then fourierCoeff f k else 0 := by
  have hfun : finiteFourierPolynomial f S =
      ∑ n ∈ S, (fun x => fourierCoeff f n * fourier n x) := by
    ext x
    simp [finiteFourierPolynomial]
  rw [hfun, fourierCoeff.sum S _ (fun n _ =>
    (((fourier n).memLp (p := 2) haarAddCircle ℂ).integrable (by norm_num)).const_mul
      (fourierCoeff f n))]
  simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply]
  simp [mul_ite]

/-- The literal finite Fourier sum, with probability-Haar coefficients. -/
def actualFourierTruncation (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (S : Finset ℤ) : ℝ → ℂ := fun x =>
  finiteFourierPolynomial (AddCircle.liftIoc d t u) S (x : AddCircle d)

theorem actualFourierTruncation_memLp (t : ℝ) (u : ℝ → ℂ) (S : Finset ℤ) :
    MemLp (actualFourierTruncation d t u S) 2
      (volume.restrict (Ioc t (t + d))) :=
  (finiteFourierPolynomial_memLp (AddCircle.liftIoc d t u) S).of_haarAddCircle.comp_measurePreserving
    (AddCircle.measurePreserving_mk d t)

private theorem liftIoc_truncation (t : ℝ) (u : ℝ → ℂ) (S : Finset ℤ) :
    AddCircle.liftIoc d t (actualFourierTruncation d t u S) =
      finiteFourierPolynomial (AddCircle.liftIoc d t u) S := by
  ext x
  change finiteFourierPolynomial (AddCircle.liftIoc d t u) S
    ((AddCircle.equivIoc d t x : ℝ) : AddCircle d) = _
  rw [AddCircle.coe_equivIoc]

private theorem residual_physicalCoeff (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d))))
    (S : Finset ℤ) (n : ℤ) :
    physicalCoeff (AddCircle.liftIoc d t
      (fun x => u x - actualFourierTruncation d t u S x)) n =
      if n ∈ S then 0 else physicalCoeff (AddCircle.liftIoc d t u) n := by
  have hsub : AddCircle.liftIoc d t
      (fun x => u x - actualFourierTruncation d t u S x) =
      fun x => AddCircle.liftIoc d t u x -
        finiteFourierPolynomial (AddCircle.liftIoc d t u) S x := by
    ext x
    change AddCircle.liftIoc d t u x -
      AddCircle.liftIoc d t (actualFourierTruncation d t u S) x = _
    rw [liftIoc_truncation]
  have hu1 := (hu.memLp_liftIoc.haarAddCircle).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hp1 := (finiteFourierPolynomial_memLp (AddCircle.liftIoc d t u) S).integrable
    (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hcoeff : fourierCoeff (fun x => AddCircle.liftIoc d t u x -
      finiteFourierPolynomial (AddCircle.liftIoc d t u) S x) n =
      fourierCoeff (AddCircle.liftIoc d t u) n -
        fourierCoeff (finiteFourierPolynomial (AddCircle.liftIoc d t u) S) n := by
    simp only [fourierCoeff, smul_eq_mul, mul_sub]
    exact integral_sub (hu1.fourier_smul (-n)) (hp1.fourier_smul (-n))
  rw [physicalCoeff, hsub, hcoeff, finiteFourierPolynomial_coeff]
  split_ifs with hn <;> simp [physicalCoeff, hn]

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
open AddCircle
open D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy
variable {d : ℝ} [hd : Fact (0 < d)]

private theorem physical_mass_eq_tsum (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :
    ENNReal.ofReal (∫ x in Ioc t (t + d), ‖u x‖ ^ 2) =
      ∑' n : ℤ, ENNReal.ofReal
        (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2) := by
  let f := AddCircle.liftIoc d t u
  have hf : MemLp f 2 haarAddCircle := hu.memLp_liftIoc.haarAddCircle
  have hcoef := fourierCoeff_congr_ae hf.coeFn_toLp
  have hmass : (∫ x in Ioc t (t + d), ‖u x‖ ^ 2) =
      d * ∫ x : AddCircle d, ‖f x‖ ^ 2 ∂haarAddCircle := by
    calc
      _ = ∫ x : AddCircle d, ‖f x‖ ^ 2 := by
        rw [← AddCircle.integral_preimage d t]
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
        dsimp only [f]
        rw [AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]
      _ = _ := by
        rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
          ENNReal.toReal_ofReal hd.out.le]
        rfl
  have hlpmass : (∫ x : AddCircle d, ‖hf.toLp f x‖ ^ 2 ∂haarAddCircle) =
      ∫ x : AddCircle d, ‖f x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hp := (hasSum_sq_fourierCoeff (hf.toLp f)).mul_left d
  rw [hcoef, hlpmass, ← hmass] at hp
  have hcoeff (n : ℤ) : ‖physicalCoeff f n‖ ^ 2 = d * ‖fourierCoeff f n‖ ^ 2 := by
    simp only [physicalCoeff, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg d), mul_pow, Real.sq_sqrt hd.out.le]
  have hsum : HasSum (fun n : ℤ => ‖physicalCoeff f n‖ ^ 2)
      (∫ x in Ioc t (t + d), ‖u x‖ ^ 2) := by
    simpa only [hcoeff] using hp
  rw [← hsum.tsum_eq]
  exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum.summable

theorem periodic_energy_eq_weighted_sum (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :
    (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (periodicEnergyDensity d t u s)) =
      ∑' n : ℤ, ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) *
        ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2) := by
  rw [← actual_gamma_periodic_energy_eq_tsum t u hu]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hm : (∫ x : ℝ, Complex.normSq
      (u x - D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicExtension d t u (x - s))
      ∂intervalMeasure d t) = windowGapMass (d := d) t u s := by
    simp only [intervalMeasure, windowGapMass,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicExtension,
      Complex.normSq_eq_norm_sq]
  simp only [periodicEnergyDensity, hm]
  exact ENNReal.ofReal_mul (density_nonneg hs)

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
open AddCircle
open D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy

/-- Finite Fourier sums approximate the actual Ioc zero-extension Gamma form. -/
theorem actual_fourier_truncation_form_core
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) →
      (∀ S : Finset ℤ,
        IntegrableOn (zeroEnergyDensity (2 * a) (-a)
          (actualFourierTruncation (2 * a) (-a) u S)) (Ioi 0) ∧
        IntegrableOn (zeroEnergyDensity (2 * a) (-a)
          (fun x => u x - actualFourierTruncation (2 * a) (-a) u S x)) (Ioi 0)) ∧
      Tendsto (fun S : Finset ℤ =>
        (∫ x in Ioc (-a) a, ‖u x - actualFourierTruncation (2 * a) (-a) u S x‖ ^ 2) +
        ∫ s in Ioi 0, zeroEnergyDensity (2 * a) (-a)
          (fun x => u x - actualFourierTruncation (2 * a) (-a) u S x) s)
        atTop (𝓝 0) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  intro henergy
  have hend : -a + 2 * a = a := by ring
  have hwindow : MemLp u 2 (volume.restrict (Ioc (-a) (-a + 2 * a))) := by
    simpa only [hend] using hu
  let r (S : Finset ℤ) (x : ℝ) := u x - actualFourierTruncation (2 * a) (-a) u S x
  let c (n : ℤ) := physicalCoeff (AddCircle.liftIoc (2 * a) (-a) u) n
  let m (n : ℤ) := ENNReal.ofReal (‖c n‖ ^ 2)
  let w (n : ℤ) := ENNReal.ofReal
    (gammaIncrement (angularFrequency (d := 2 * a) n) * ‖c n‖ ^ 2)
  have hw (n : ℤ) : w n =
      ENNReal.ofReal (gammaIncrement (angularFrequency (d := 2 * a) n)) * m n :=
    ENNReal.ofReal_mul
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.digamma_increment_nonnegative
        (angularFrequency (d := 2 * a) n))
  have hfinite := (actual_gamma_zero_domain_iff_digamma_weighted_sum_finite a ha u hu).mp henergy
  have hwfinite : (∑' n, w n) < (∞ : ℝ≥0∞) := by
    simpa only [hw, m, c] using hfinite
  have hmfinite : (∑' n, m n) < (∞ : ℝ≥0∞) := by
    rw [← physical_mass_eq_tsum (-a) u hwindow]
    exact ENNReal.ofReal_lt_top
  have hreswindow (S : Finset ℤ) :
      MemLp (r S) 2 (volume.restrict (Ioc (-a) (-a + 2 * a))) :=
    hwindow.sub (actualFourierTruncation_memLp (-a) u S)
  have hres (S : Finset ℤ) : MemLp (r S) 2 (volume.restrict (Ioc (-a) a)) := by
    simpa only [hend] using hreswindow S
  have htrunc (S : Finset ℤ) : MemLp (actualFourierTruncation (2 * a) (-a) u S) 2
      (volume.restrict (Ioc (-a) a)) := by
    simpa only [hend] using actualFourierTruncation_memLp (d := 2 * a) (-a) u S
  have hcr (S : Finset ℤ) (n : ℤ) :
      physicalCoeff (AddCircle.liftIoc (2 * a) (-a) (r S)) n =
        if n ∈ S then 0 else c n :=
    residual_physicalCoeff (-a) u hwindow S n
  have hcp (S : Finset ℤ) (n : ℤ) :
      physicalCoeff (AddCircle.liftIoc (2 * a) (-a)
        (actualFourierTruncation (2 * a) (-a) u S)) n =
        if n ∈ S then c n else 0 := by
    rw [physicalCoeff, liftIoc_truncation, finiteFourierPolynomial_coeff]
    by_cases hn : n ∈ S <;> simp [hn, c, physicalCoeff]
  have hresfinite (S : Finset ℤ) :
      (∑' n : ℤ, ENNReal.ofReal (gammaIncrement (angularFrequency (d := 2 * a) n)) *
        ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc (2 * a) (-a) (r S)) n‖ ^ 2)) <
          (∞ : ℝ≥0∞) := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) hfinite
    intro n
    rw [hcr]
    by_cases hn : n ∈ S <;> simp [hn, c]
  have htruncfinite (S : Finset ℤ) :
      (∑' n : ℤ, ENNReal.ofReal (gammaIncrement (angularFrequency (d := 2 * a) n)) *
        ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc (2 * a) (-a)
          (actualFourierTruncation (2 * a) (-a) u S)) n‖ ^ 2)) < (∞ : ℝ≥0∞) := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) hfinite
    intro n
    rw [hcp]
    by_cases hn : n ∈ S <;> simp [hn, c]
  have hresDomain (S : Finset ℤ) :
      IntegrableOn (zeroEnergyDensity (2 * a) (-a) (r S)) (Ioi 0) :=
    (actual_gamma_zero_domain_iff_digamma_weighted_sum_finite a ha (r S) (hres S)).mpr
      (hresfinite S)
  have hresPeriodic (S : Finset ℤ) :
      IntegrableOn (periodicEnergyDensity (2 * a) (-a) (r S)) (Ioi 0) :=
    ((actual_centered_gamma_full_domain_equivalence a ha (r S) (hres S)).1).mp
      (hresDomain S)
  have hmassTail (S : Finset ℤ) :
      ENNReal.ofReal (∫ x in Ioc (-a) a, ‖r S x‖ ^ 2) =
        ∑' n : {n : ℤ // n ∉ S}, m n := by
    have hm := physical_mass_eq_tsum (-a) (r S) (hreswindow S)
    rw [hend] at hm
    calc
      _ = ∑' n : ℤ, {n : ℤ | n ∉ S}.indicator m n := by
        rw [hm]
        apply tsum_congr
        intro n
        rw [hcr]
        by_cases hn : n ∈ S <;> simp [hn, m, c]
      _ = _ := (tsum_subtype {n : ℤ | n ∉ S} m).symm
  have henergyTail (S : Finset ℤ) :
      (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (periodicEnergyDensity (2 * a) (-a) (r S) s)) =
        ∑' n : {n : ℤ // n ∉ S}, w n := by
    calc
      _ = ∑' n : ℤ, {n : ℤ | n ∉ S}.indicator w n := by
        rw [periodic_energy_eq_weighted_sum (-a) (r S) (hreswindow S)]
        apply tsum_congr
        intro n
        rw [hcr]
        by_cases hn : n ∈ S <;> simp [hn, hw, m, c]
      _ = _ := (tsum_subtype {n : ℤ | n ∉ S} w).symm
  have hnn (v : ℝ → ℂ) : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ periodicEnergyDensity (2 * a) (-a) v s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs) (integral_nonneg fun x => Complex.normSq_nonneg _)
  have henergyRealTail (S : Finset ℤ) :
      ENNReal.ofReal (∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) (r S) s) =
        ∑' n : {n : ℤ // n ∉ S}, w n :=
    (ofReal_integral_eq_lintegral_ofReal (hresPeriodic S) (hnn (r S))).trans (henergyTail S)
  have hmass0 : Tendsto (fun S : Finset ℤ => ∫ x in Ioc (-a) a, ‖r S x‖ ^ 2)
      atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (ENNReal.tendsto_tsum_compl_atTop_zero (ne_of_lt hmfinite))
    have htoReal (S : Finset ℤ) : (∑' n : {n : ℤ // n ∉ S}, m n).toReal =
        ∫ x in Ioc (-a) a, ‖r S x‖ ^ 2 := by
      rw [← hmassTail S, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    simpa only [Function.comp_def, htoReal, ENNReal.toReal_zero] using ht
  have hperiodic0 : Tendsto (fun S : Finset ℤ =>
      ∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) (r S) s) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (ENNReal.tendsto_tsum_compl_atTop_zero (ne_of_lt hwfinite))
    have htoReal (S : Finset ℤ) : (∑' n : {n : ℤ // n ∉ S}, w n).toReal =
        ∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) (r S) s := by
      rw [← henergyRealTail S, ENNReal.toReal_ofReal (integral_nonneg_of_ae (hnn (r S)))]
    simpa only [Function.comp_def, htoReal, ENNReal.toReal_zero] using ht
  have hzero0 : Tendsto (fun S : Finset ℤ =>
      ∫ s in Ioi 0, zeroEnergyDensity (2 * a) (-a) (r S) s) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro S
      apply integral_nonneg_of_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact mul_nonneg (density_nonneg hs) (integral_nonneg fun x => Complex.normSq_nonneg _)
    · intro S
      exact actual_centered_gamma_energy_upper_bound a ha (r S) (hres S) (hresPeriodic S)
    · simpa using hperiodic0.add (hmass0.const_mul
        (2 * D5.S3.Weil.ZetaGamma.FormCore.Corner.gammaCk * Real.pi +
          4 * a * Real.exp (-a) / ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a)))))
  refine ⟨?_, ?_⟩
  · intro S
    exact ⟨(actual_gamma_zero_domain_iff_digamma_weighted_sum_finite a ha
      (actualFourierTruncation (2 * a) (-a) u S) (htrunc S)).mpr (htruncfinite S),
      hresDomain S⟩
  · simpa only [r, zero_add] using hmass0.add hzero0

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

/- GID: D5/S3/Observer/MeasureSeparation/FourierModeDetermination
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/FourierModeDetermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Fourier data do not determine a circle measure, while all modes do. -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.ContinuousMap.Compact

/- Library-search audit trail (2026-09-04):
   * Repository searches for finite Fourier-mode cloning, moment-map
     noninjectivity, character determination of measures, circle moments, and
     more general finite expectation-table separation found no theorem pairing
     a finite-mode counterexample with full-mode uniqueness.
   * `OneScaleInformationalCompleteness` proves a related specialized recovery
     result for weighted Cayley pushforwards of real-axis measures; it neither
     constructs equal finite Fourier tables nor states arbitrary circle-measure
     extensionality.
   * Pinned Mathlib supplies `fourierCoeff_fourier`,
     `fourierSubalgebra_separatesPoints`, and finite-measure extensionality by a
     separating star subalgebra. They are applied directly below.
   * The finite counterexample uses the genuine normalized Haar probability
     measure and its nonnegative cosine-density perturbation, not an abstract
     sequence of purported coefficients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AddCircle BoundedContinuousFunction MeasureTheory Set
open scoped ENNReal

namespace D5.S3.Observer.MeasureSeparation.FourierModeDetermination

/-- The circle on which the regulator's integer Fourier modes are read. -/
abbrev RegulatorCircle := AddCircle (2 * Real.pi)

/-- The integer Fourier moment of a regulator measure. -/
def fourierMoment (mu : Measure RegulatorCircle) (n : Int) : Complex :=
  integral mu (fourier n)

private local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Normalized Haar probability measure on the regulator circle. -/
abbrev regulatorHaar : Measure RegulatorCircle :=
  @haarAddCircle (2 * Real.pi) inferInstance

private theorem fourier_integrable (n : Int) :
    Integrable (fun x : RegulatorCircle => fourier n x) regulatorHaar := by
  exact (ContinuousMap.equivBoundedOfCompact _ _ (fourier n)).integrable _

private theorem haar_integral_fourier (n : Int) :
    integral regulatorHaar (fourier n) = if n = 0 then 1 else 0 := by
  have coefficient := congrFun (fourierCoeff_fourier
    (T := 2 * Real.pi) n) 0
  have integralCoefficient :
      integral regulatorHaar (fourier n) =
        (Pi.single n (1 : Complex) : Int -> Complex) 0 := by
    simpa only [regulatorHaar, fourierCoeff, neg_zero, fourier_zero,
      one_smul] using coefficient
  rw [integralCoefficient]
  exact show (Pi.single n (1 : Complex) : Int -> Complex) 0 =
      if n = 0 then 1 else 0 by
    by_cases hn : n = 0
    · subst n
      simp
    · simp [hn]

private theorem haar_integral_re_fourier_smul_fourier (k n : Int) :
    integral regulatorHaar
        (fun x : RegulatorCircle => (fourier k x).re • fourier n x) =
      ((if k + n = 0 then 1 else 0) +
        (if n - k = 0 then 1 else 0)) / 2 := by
  have integrandIdentity (x : RegulatorCircle) :
      (fourier k x).re • fourier n x =
        (fourier (k + n) x + fourier (n - k) x) / 2 := by
    rw [Complex.real_smul, Complex.re_eq_add_conj, ← fourier_neg]
    calc
      ((fourier k x + fourier (-k) x) / 2) * fourier n x =
          (fourier k x * fourier n x +
            fourier (-k) x * fourier n x) / 2 := by ring
      _ = (fourier (k + n) x + fourier (n - k) x) / 2 := by
        rw [← fourier_add, ← fourier_add]
        rw [show -k + n = n - k by ring]
  rw [integral_congr_ae (ae_of_all _ integrandIdentity)]
  rw [integral_div, integral_add (fourier_integrable (k + n))
    (fourier_integrable (n - k))]
  rw [haar_integral_fourier, haar_integral_fourier]

/-- A nonnegative cosine perturbation of the constant Haar density. -/
def perturbationDensity (k : Int) (x : RegulatorCircle) : Real :=
  1 + (fourier k x).re / 2

private theorem perturbationDensity_nonnegative (k : Int) (x : RegulatorCircle) :
    0 <= perturbationDensity k x := by
  have lower : -(1 : Real) <= (fourier k x).re := by
    have hre := neg_le_of_abs_le (Complex.abs_re_le_norm (fourier k x))
    have modeNorm : ‖fourier k x‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rwa [modeNorm] at hre
  dsimp only [perturbationDensity]
  linarith

private theorem perturbationDensity_continuous (k : Int) :
    Continuous (perturbationDensity k) := by
  exact continuous_const.add
    ((Complex.continuous_re.comp (fourier k).continuous).div_const 2)

private theorem perturbationDensity_integrable (k : Int) :
    Integrable (perturbationDensity k) regulatorHaar := by
  let densityMap : C(RegulatorCircle, Real) :=
    ⟨perturbationDensity k, perturbationDensity_continuous k⟩
  exact (ContinuousMap.equivBoundedOfCompact _ _ densityMap).integrable _

/-- Haar measure tilted by one unused cosine mode. -/
def perturbedHaar (k : Int) : Measure RegulatorCircle :=
  regulatorHaar.withDensity
    (ENNReal.ofReal ∘ perturbationDensity k)

private theorem perturbedHaar_isProbability (k : Int) (hk : k ≠ 0) :
    IsProbabilityMeasure (perturbedHaar k) := by
  constructor
  rw [perturbedHaar, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [Function.comp_apply]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (perturbationDensity_integrable k)
    (ae_of_all _ (perturbationDensity_nonnegative k))]
  have modeIntegral :
      integral regulatorHaar (fun x : RegulatorCircle => (fourier k x).re) = 0 := by
    change integral regulatorHaar
      (fun x : RegulatorCircle => RCLike.re (fourier k x)) = 0
    rw [integral_re (fourier_integrable k), haar_integral_fourier]
    simp [hk]
  have realModeIntegrable : Integrable
      (fun x : RegulatorCircle => (fourier k x).re) regulatorHaar := by
    change Integrable (fun x : RegulatorCircle => RCLike.re (fourier k x)) regulatorHaar
    exact (fourier_integrable k).re
  rw [show integral regulatorHaar (perturbationDensity k) = 1 by
    change integral regulatorHaar
      (fun x : RegulatorCircle => 1 + (fourier k x).re / 2) = 1
    rw [integral_add (integrable_const _) (realModeIntegrable.div_const 2),
      integral_const, integral_div, modeIntegral]
    simp [regulatorHaar]]
  exact ENNReal.ofReal_one

private theorem perturbedHaar_moment (k n : Int) :
      fourierMoment (perturbedHaar k) n =
      fourierMoment regulatorHaar n +
        (1 / 2 : Real) •
          (((if k + n = 0 then 1 else 0) +
            (if n - k = 0 then 1 else 0)) / 2 : Complex) := by
  simp only [fourierMoment, perturbedHaar]
  rw [integral_withDensity_eq_integral_toReal_smul
    ((ENNReal.continuous_ofReal.comp
      (perturbationDensity_continuous k)).measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fourier n)]
  have densityToReal (x : RegulatorCircle) :
      (ENNReal.ofReal (perturbationDensity k x)).toReal =
        perturbationDensity k x :=
    ENNReal.toReal_ofReal (perturbationDensity_nonnegative k x)
  simp_rw [Function.comp_apply, densityToReal]
  have weightedIntegrable : Integrable
      (fun x : RegulatorCircle =>
        ((fourier k x).re / 2) • fourier n x) regulatorHaar := by
    let weighted : C(RegulatorCircle, Complex) :=
      ⟨fun x => ((fourier k x).re / 2) • fourier n x, by fun_prop⟩
    exact (ContinuousMap.equivBoundedOfCompact _ _ weighted).integrable _
  rw [show (fun x : RegulatorCircle =>
      perturbationDensity k x • fourier n x) =
      fun x => fourier n x + ((fourier k x).re / 2) • fourier n x by
    funext x
    simp [perturbationDensity, add_smul]]
  rw [integral_add (fourier_integrable n) weightedIntegrable]
  rw [show integral regulatorHaar
      (fun x : RegulatorCircle => ((fourier k x).re / 2) • fourier n x) =
        (1 / 2 : Real) • integral regulatorHaar
          (fun x : RegulatorCircle => (fourier k x).re • fourier n x) by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Complex.real_smul]
    push_cast
    ring]
  rw [haar_integral_re_fourier_smul_fourier]

/-- No finite set of integer Fourier modes determines an arbitrary regulator
probability measure. The returned measures are explicitly distinct and agree
on every requested mode. -/
theorem finite_fourier_modes_do_not_determine_measure (modes : Finset Int) :
    exists mu nu : Measure RegulatorCircle,
      IsProbabilityMeasure mu /\ IsProbabilityMeasure nu /\ mu ≠ nu /\
        forall n, n ∈ modes -> fourierMoment mu n = fourierMoment nu n := by
  let radius : Nat := modes.sup Int.natAbs
  let k : Int := (radius + 1 : Nat)
  have hkPositive : 0 < k := by
    simp [k]
  have hk : k ≠ 0 := hkPositive.ne'
  have hkAbs : k.natAbs = radius + 1 := by
    change (Int.ofNat (radius + 1)).natAbs = radius + 1
    rfl
  have avoids (n : Int) (hn : n ∈ modes) : n ≠ k /\ n ≠ -k := by
    have bounded : n.natAbs <= radius := by
      exact Finset.le_sup (f := Int.natAbs) hn
    constructor <;> intro equality
    · subst n
      rw [hkAbs] at bounded
      omega
    · subst n
      rw [Int.natAbs_neg, hkAbs] at bounded
      omega
  let mu : Measure RegulatorCircle := regulatorHaar
  let nu : Measure RegulatorCircle := perturbedHaar k
  have muProbability : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  have nuProbability : IsProbabilityMeasure nu := by
    dsimp only [nu]
    exact perturbedHaar_isProbability k hk
  have agrees : forall n, n ∈ modes ->
      fourierMoment mu n = fourierMoment nu n := by
    intro n hn
    have hAvoid := avoids n hn
    have hsum : k + n ≠ 0 := by
      intro equality
      apply hAvoid.2
      omega
    have hdiff : n - k ≠ 0 := by
      intro equality
      apply hAvoid.1
      omega
    dsimp only [mu, nu]
    rw [perturbedHaar_moment]
    simp [hsum, hdiff]
  have differsAtUnusedMode :
      fourierMoment mu (-k) ≠ fourierMoment nu (-k) := by
    dsimp only [mu, nu]
    rw [perturbedHaar_moment]
    have hneg : -k ≠ 0 := neg_ne_zero.mpr hk
    have hdouble : -k - k ≠ 0 := by
      intro equality
      apply hk
      omega
    simp [fourierMoment, haar_integral_fourier, hneg, hdouble]
  refine ⟨mu, nu, muProbability, nuProbability, ?_, agrees⟩
  intro equality
  exact differsAtUnusedMode (congrArg (fun measure => fourierMoment measure (-k)) equality)

#print axioms finite_fourier_modes_do_not_determine_measure

end D5.S3.Observer.MeasureSeparation.FourierModeDetermination

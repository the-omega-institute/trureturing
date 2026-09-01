/- GID: D5/S3/Weil/TestFunctions/LiCurvatureFourierRepresentation
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/LiCurvatureFourierRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Li curvature is the Fourier sequence of its symmetric Cayley probability measure. -/

import D5.S3.Weil.TestFunctions.CayleyMomentTransport

/- Library-search audit trail (2026-08-31):
   * D5 searches for Li curvature, Li coefficients, probability-measure Fourier
     coefficients, and the half-scale Cayley body found no exact owner.
   * `CayleyLaguerreMomentTomography.cayleyCharacter` and
     `CayleyMomentTransport.cayleyCircle` are the canonical existing primitives
     reused below; no Cayley or moment definition is redeclared.
   * Pinned Mathlib has no exact Li-curvature Fourier theorem. It supplies
     probability pushforwards, measure-mixture integration, circle integer
     powers, and conjugation under integration.
   * Installed Lake packages and public Lean code searches found no exact
     third-party owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
open D5.S3.Weil.TestFunctions.CayleyMomentTransport

namespace D5.S3.Weil.TestFunctions.LiCurvatureFourierRepresentation

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The positive-ordinate energy distribution determines a symmetric circle
probability measure. The normalized second difference of the Li energy at
every integral mode is exactly the corresponding Fourier coefficient. -/
theorem li_curvature_fourier_representation
    (rho : Measure Real) [IsProbabilityMeasure rho] :
    let phase : Real -> Circle :=
      cayleyCircle (1 / 2 : Real) (by norm_num)
    let reflectedPhase : Real -> Circle := fun xi => (phase xi)⁻¹
    let liEnergy : Int -> Real -> Real := fun n xi =>
      ((4 * xi ^ 2 + 1) / 2) *
        (1 - ((((phase xi) ^ n : Circle) : Complex)).re)
    let normalizedLi : Int -> Real := fun n => ∫ xi, liEnergy n xi ∂rho
    let liCurvature : Int -> Real := fun n =>
      (normalizedLi (n + 1) - 2 * normalizedLi n + normalizedLi (n - 1)) / 2
    let curvatureMeasure : Measure Circle :=
      (1 / 2 : NNReal) • Measure.map phase rho +
        (1 / 2 : NNReal) • Measure.map reflectedPhase rho
    IsProbabilityMeasure curvatureMeasure ∧
      forall n,
        (liCurvature n : Complex) =
          ∫ z : Circle, (((z ^ n : Circle) : Complex)) ∂curvatureMeasure := by
  let phase : Real -> Circle :=
    cayleyCircle (1 / 2 : Real) (by norm_num)
  let reflectedPhase : Real -> Circle := fun xi => (phase xi)⁻¹
  let liEnergy : Int -> Real -> Real := fun n xi =>
    ((4 * xi ^ 2 + 1) / 2) *
      (1 - ((((phase xi) ^ n : Circle) : Complex)).re)
  let normalizedLi : Int -> Real := fun n => ∫ xi, liEnergy n xi ∂rho
  let liCurvature : Int -> Real := fun n =>
    (normalizedLi (n + 1) - 2 * normalizedLi n + normalizedLi (n - 1)) / 2
  let curvatureMeasure : Measure Circle :=
    (1 / 2 : NNReal) • Measure.map phase rho +
      (1 / 2 : NNReal) • Measure.map reflectedPhase rho
  change IsProbabilityMeasure curvatureMeasure ∧
    forall n,
      (liCurvature n : Complex) =
        ∫ z : Circle, (((z ^ n : Circle) : Complex)) ∂curvatureMeasure
  have phaseContinuous : Continuous phase := by
    unfold phase cayleyCircle
    apply Continuous.subtype_mk
    change Continuous (fun xi : Real => cayleyCharacter (1 / 2 : Real) xi)
    unfold cayleyCharacter
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro xi denominatorZero
    have imaginaryPart := congrArg Complex.im denominatorZero
    norm_num at imaginaryPart
  have reflectedPhaseContinuous : Continuous reflectedPhase := by
    unfold reflectedPhase
    fun_prop
  have phaseMeasurable : Measurable phase := phaseContinuous.measurable
  have reflectedPhaseMeasurable : Measurable reflectedPhase :=
    reflectedPhaseContinuous.measurable
  have naturalPowerBound (z : Circle) (k : Nat) :
      ‖(((z ^ k : Circle) : Complex) - 1)‖ ≤
        k * ‖(z : Complex) - 1‖ := by
    have sumNorm :
        ‖∑ i ∈ Finset.range k, (z : Complex) ^ i‖ ≤ k := by
      calc
        ‖∑ i ∈ Finset.range k, (z : Complex) ^ i‖ ≤
            ∑ i ∈ Finset.range k, ‖(z : Complex) ^ i‖ :=
          norm_sum_le _ _
        _ = k := by simp [norm_pow]
    calc
      ‖(((z ^ k : Circle) : Complex) - 1)‖ =
          ‖(∑ i ∈ Finset.range k, (z : Complex) ^ i) *
            ((z : Complex) - 1)‖ := by
              rw [geom_sum_mul]
              rfl
      _ ≤ ‖∑ i ∈ Finset.range k, (z : Complex) ^ i‖ *
            ‖(z : Complex) - 1‖ := norm_mul_le _ _
      _ ≤ k * ‖(z : Complex) - 1‖ := by
            exact mul_le_mul_of_nonneg_right sumNorm (norm_nonneg _)
  have integerPowerBound (z : Circle) (n : Int) :
      ‖(((z ^ n : Circle) : Complex) - 1)‖ ≤
        n.natAbs * ‖(z : Complex) - 1‖ := by
    rcases n.eq_nat_or_neg with ⟨k, rfl | rfl⟩
    · simpa using naturalPowerBound z k
    · have inverseDistance :
          ‖((z⁻¹ : Circle) : Complex) - 1‖ = ‖(z : Complex) - 1‖ := by
        calc
          ‖((z⁻¹ : Circle) : Complex) - 1‖ =
              ‖star ((z : Complex) - 1)‖ := by
                rw [Circle.coe_inv_eq_conj]
                simp only [Complex.star_def, map_sub, map_one]
          _ = ‖(z : Complex) - 1‖ := norm_star _
      have inverseBound := naturalPowerBound z⁻¹ k
      rw [inverseDistance] at inverseBound
      simpa [Circle.coe_inv_eq_conj] using inverseBound
  have phaseDistanceSquare (xi : Real) :
      ‖((phase xi : Circle) : Complex) - 1‖ ^ 2 =
        4 / (4 * xi ^ 2 + 1) := by
    unfold phase
    change ‖cayleyCharacter (1 / 2 : Real) xi - 1‖ ^ 2 =
      4 / (4 * xi ^ 2 + 1)
    have denominatorNeZero :
        ((xi : Complex) - Complex.I * (1 / 2 : Real)) ≠ 0 := by
      intro h
      have imaginaryPart := congrArg Complex.im h
      norm_num at imaginaryPart
    rw [show cayleyCharacter (1 / 2 : Real) xi - 1 =
        Complex.I / ((xi : Complex) - Complex.I * (1 / 2 : Real)) by
      unfold cayleyCharacter
      field_simp [denominatorNeZero]
      apply Complex.ext <;> norm_num]
    rw [norm_div, Complex.norm_I, one_div, inv_pow, Complex.sq_norm]
    norm_num [Complex.normSq_apply]
    field_simp [show 4 * xi ^ 2 + 1 ≠ 0 by positivity]
  have energyIntegrable (n : Int) : Integrable (liEnergy n) rho := by
    apply (integrable_const (μ := rho) ((n.natAbs : Real) ^ 2)).mono'
    · let circlePower : Circle -> Complex := fun z => ((z ^ n : Circle) : Complex)
      have circlePowerContinuous : Continuous circlePower :=
        continuous_subtype_val.comp (continuous_zpow n)
      have energyContinuous : Continuous (liEnergy n) := by
        unfold liEnergy
        change Continuous (fun xi : Real =>
          ((4 * xi ^ 2 + 1) / 2) *
            (1 - (circlePower (phase xi)).re))
        have powerRealContinuous : Continuous (fun xi : Real =>
            (circlePower (phase xi)).re) :=
          Complex.continuous_re.comp
            (circlePowerContinuous.comp phaseContinuous)
        exact (by fun_prop)
      exact energyContinuous.aestronglyMeasurable
    · filter_upwards with xi
      have energyAsSquare :
          liEnergy n xi =
            ((4 * xi ^ 2 + 1) / 4) *
              ‖((((phase xi) ^ n : Circle) : Complex)) - 1‖ ^ 2 := by
        have unitPower := Complex.norm_sub_one_sq_eq_of_norm_eq_one
          (Circle.norm_coe ((phase xi) ^ n))
        unfold liEnergy
        rw [unitPower]
        ring
      have powerBound :
          ‖((((phase xi) ^ n : Circle) : Complex)) - 1‖ ≤
            (n.natAbs : Real) *
              ‖((phase xi : Circle) : Complex) - 1‖ :=
        integerPowerBound (phase xi) n
      have powerSquareBound :
          ‖((((phase xi) ^ n : Circle) : Complex)) - 1‖ ^ 2 ≤
            ((n.natAbs : Real) *
              ‖((phase xi : Circle) : Complex) - 1‖) ^ 2 := by
        nlinarith [norm_nonneg
          (((((phase xi) ^ n : Circle) : Complex)) - 1),
          norm_nonneg (((phase xi : Circle) : Complex) - 1)]
      rw [energyAsSquare, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
      calc
        ((4 * xi ^ 2 + 1) / 4) *
            ‖((((phase xi) ^ n : Circle) : Complex)) - 1‖ ^ 2 ≤
          ((4 * xi ^ 2 + 1) / 4) *
            ((n.natAbs : Real) *
              ‖((phase xi : Circle) : Complex) - 1‖) ^ 2 := by
                gcongr
        _ = (n.natAbs : Real) ^ 2 := by
              rw [mul_pow, phaseDistanceSquare]
              field_simp [show 4 * xi ^ 2 + 1 ≠ 0 by positivity]
  letI phaseProbability : IsProbabilityMeasure (Measure.map phase rho) :=
    Measure.isProbabilityMeasure_map phaseMeasurable.aemeasurable
  letI reflectedPhaseProbability :
      IsProbabilityMeasure (Measure.map reflectedPhase rho) :=
    Measure.isProbabilityMeasure_map reflectedPhaseMeasurable.aemeasurable
  have curvatureMeasureProbability : IsProbabilityMeasure curvatureMeasure := by
    let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
    have halfNNReal : unitInterval.toNNReal half = (1 / 2 : NNReal) := by
      apply NNReal.eq
      rfl
    have halfSymmetric : unitInterval.symm half = half := by
      apply Subtype.ext
      norm_num [half, unitInterval.symm]
    have mixtureProbability : IsProbabilityMeasure
        (unitInterval.toNNReal half • Measure.map phase rho +
          unitInterval.toNNReal (unitInterval.symm half) •
            Measure.map reflectedPhase rho) := by
      infer_instance
    simpa only [curvatureMeasure, halfNNReal, halfSymmetric] using
      mixtureProbability
  refine ⟨curvatureMeasureProbability, ?_⟩
  intro n
  let circlePower : Circle -> Complex := fun z => ((z ^ n : Circle) : Complex)
  have circlePowerContinuous : Continuous circlePower := by
    exact continuous_subtype_val.comp (continuous_zpow n)
  have phasePowerIntegrable :
      Integrable (fun xi => circlePower (phase xi)) rho := by
    apply (integrable_const (μ := rho) (1 : Real)).mono'
    · exact (circlePowerContinuous.comp phaseContinuous).aestronglyMeasurable
    · filter_upwards with xi
      simp [circlePower]
  have reflectedPowerIntegrable :
      Integrable (fun xi => circlePower (reflectedPhase xi)) rho := by
    apply (integrable_const (μ := rho) (1 : Real)).mono'
    · exact
        (circlePowerContinuous.comp reflectedPhaseContinuous).aestronglyMeasurable
    · filter_upwards with xi
      simp [circlePower]
  have phaseMapPowerIntegrable :
      Integrable circlePower (Measure.map phase rho) :=
    (integrable_map_measure circlePowerContinuous.aestronglyMeasurable
      phaseMeasurable.aemeasurable).2 (by
        change Integrable (circlePower ∘ phase) rho at phasePowerIntegrable
        exact phasePowerIntegrable)
  have reflectedMapPowerIntegrable :
      Integrable circlePower (Measure.map reflectedPhase rho) :=
    (integrable_map_measure circlePowerContinuous.aestronglyMeasurable
      reflectedPhaseMeasurable.aemeasurable).2 (by
        change Integrable (circlePower ∘ reflectedPhase) rho at reflectedPowerIntegrable
        exact reflectedPowerIntegrable)
  have phaseReal (xi : Real) :
      (((phase xi : Circle) : Complex)).re =
        (4 * xi ^ 2 - 1) / (4 * xi ^ 2 + 1) := by
    unfold phase cayleyCircle cayleyCharacter
    rw [Complex.div_re]
    norm_num [Complex.normSq_apply]
    field_simp [show 4 * xi ^ 2 + 1 ≠ 0 by positivity]
    ring
  have phaseRecurrence (xi : Real) :
      ((((phase xi) ^ (n + 1) : Circle) : Complex)).re +
          ((((phase xi) ^ (n - 1) : Circle) : Complex)).re =
        2 * ((((phase xi) ^ n : Circle) : Complex)).re *
          (((phase xi : Circle) : Complex)).re := by
    rw [zpow_add_one]
    rw [show n - 1 = n + (-1) by ring, zpow_add]
    simp only [Circle.coe_mul, Circle.coe_zpow, zpow_neg_one,
      Circle.coe_inv_eq_conj, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  have energySecondDifference (xi : Real) :
      (liEnergy (n + 1) xi - 2 * liEnergy n xi +
          liEnergy (n - 1) xi) / 2 =
        ((((phase xi) ^ n : Circle) : Complex)).re := by
    calc
      (liEnergy (n + 1) xi - 2 * liEnergy n xi +
            liEnergy (n - 1) xi) / 2 =
          ((4 * xi ^ 2 + 1) / 4) *
            (2 * ((((phase xi) ^ n : Circle) : Complex)).re -
              (((((phase xi) ^ (n + 1) : Circle) : Complex)).re +
                ((((phase xi) ^ (n - 1) : Circle) : Complex)).re)) := by
            unfold liEnergy
            ring
      _ = ((4 * xi ^ 2 + 1) / 4) *
            (2 * ((((phase xi) ^ n : Circle) : Complex)).re -
              2 * ((((phase xi) ^ n : Circle) : Complex)).re *
                (((phase xi : Circle) : Complex)).re) := by
            rw [phaseRecurrence xi]
      _ = ((((phase xi) ^ n : Circle) : Complex)).re := by
            rw [phaseReal xi]
            field_simp [show 4 * xi ^ 2 + 1 ≠ 0 by positivity]
            ring
  have curvatureIntegral :
      liCurvature n =
        ∫ xi, ((((phase xi) ^ n : Circle) : Complex)).re ∂rho := by
    have combinationIntegral :
        (∫ xi, liEnergy (n + 1) xi - 2 * liEnergy n xi +
            liEnergy (n - 1) xi ∂rho) =
          (∫ xi, liEnergy (n + 1) xi ∂rho) -
            2 * (∫ xi, liEnergy n xi ∂rho) +
              ∫ xi, liEnergy (n - 1) xi ∂rho := by
      have subIntegral :
          (∫ xi, (liEnergy (n + 1) - fun x => 2 * liEnergy n x) xi ∂rho) =
            (∫ xi, liEnergy (n + 1) xi ∂rho) -
              2 * (∫ xi, liEnergy n xi ∂rho) := by
        calc
          (∫ xi, (liEnergy (n + 1) - fun x => 2 * liEnergy n x) xi ∂rho) =
              (∫ xi, liEnergy (n + 1) xi ∂rho) -
                ∫ xi, 2 * liEnergy n xi ∂rho := by
                  simpa only [Pi.sub_apply] using
                    (integral_sub (energyIntegrable (n + 1))
                      ((energyIntegrable n).const_mul 2))
          _ = _ := by rw [integral_const_mul]
      have h := integral_add
        ((energyIntegrable (n + 1)).sub
          ((energyIntegrable n).const_mul 2))
        (energyIntegrable (n - 1))
      calc
        (∫ xi, liEnergy (n + 1) xi - 2 * liEnergy n xi +
            liEnergy (n - 1) xi ∂rho) =
            ∫ xi, ((liEnergy (n + 1) - fun x => 2 * liEnergy n x) +
              liEnergy (n - 1)) xi ∂rho := by rfl
        _ = (∫ xi, (liEnergy (n + 1) - fun x => 2 * liEnergy n x) xi ∂rho) +
              ∫ xi, liEnergy (n - 1) xi ∂rho := h
        _ = _ := by rw [subIntegral]
    calc
      liCurvature n =
          (∫ xi, (liEnergy (n + 1) xi - 2 * liEnergy n xi +
            liEnergy (n - 1) xi) / 2 ∂rho) := by
            unfold liCurvature normalizedLi
            rw [show (fun xi =>
                (liEnergy (n + 1) xi - 2 * liEnergy n xi +
                  liEnergy (n - 1) xi) / 2) =
              fun xi => (1 / 2 : Real) *
                ((liEnergy (n + 1) xi - 2 * liEnergy n xi) +
                  liEnergy (n - 1) xi) by
                funext xi
                ring]
            rw [integral_const_mul]
            rw [combinationIntegral]
            ring
      _ = ∫ xi, ((((phase xi) ^ n : Circle) : Complex)).re ∂rho := by
            apply integral_congr_ae
            filter_upwards with xi
            exact energySecondDifference xi
  have reflectedPowerConjugate (xi : Real) :
      circlePower (reflectedPhase xi) =
        star (circlePower (phase xi)) := by
    unfold circlePower reflectedPhase
    rw [inv_zpow, Circle.coe_inv_eq_conj]
    rfl
  have reflectedIntegralConjugate :
      (∫ xi, circlePower (reflectedPhase xi) ∂rho) =
        star (∫ xi, circlePower (phase xi) ∂rho) := by
    calc
      (∫ xi, circlePower (reflectedPhase xi) ∂rho) =
          ∫ xi, star (circlePower (phase xi)) ∂rho := by
            apply integral_congr_ae
            filter_upwards with xi
            exact reflectedPowerConjugate xi
      _ = star (∫ xi, circlePower (phase xi) ∂rho) := by
            simpa only [Complex.star_def] using
              (integral_conj (μ := rho) (f := fun xi =>
                circlePower (phase xi)))
  have measureMoment :
      (∫ z : Circle, circlePower z ∂curvatureMeasure) =
        (((∫ xi, circlePower (phase xi) ∂rho).re : Real) : Complex) := by
    unfold curvatureMeasure
    rw [integral_add_measure phaseMapPowerIntegrable.smul_measure_nnreal
      reflectedMapPowerIntegrable.smul_measure_nnreal]
    rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    rw [integral_map phaseMeasurable.aemeasurable
      circlePowerContinuous.aestronglyMeasurable]
    rw [integral_map reflectedPhaseMeasurable.aemeasurable
      circlePowerContinuous.aestronglyMeasurable]
    rw [reflectedIntegralConjugate]
    apply Complex.ext
    · norm_num [NNReal.smul_def, Complex.star_def]
      ring
    · norm_num [NNReal.smul_def, Complex.star_def]
  have phaseMomentReal :
      ∫ xi, ((((phase xi) ^ n : Circle) : Complex)).re ∂rho =
        (∫ xi, circlePower (phase xi) ∂rho).re := by
    simpa only [circlePower, RCLike.re_eq_complex_re] using
      (integral_re phasePowerIntegrable)
  rw [curvatureIntegral, phaseMomentReal]
  exact measureMoment.symm

#print axioms li_curvature_fourier_representation

end D5.S3.Weil.TestFunctions.LiCurvatureFourierRepresentation

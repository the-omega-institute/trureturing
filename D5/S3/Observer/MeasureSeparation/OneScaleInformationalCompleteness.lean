/- GID: D5/S3/Observer/MeasureSeparation/OneScaleInformationalCompleteness
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/OneScaleInformationalCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recover a real spectrum from all moments of one weighted Cayley pushforward. -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.ContinuousMap.Compact

/- Library-search audit trail (2026-08-29):
   * Repository searches for one-scale Cayley completeness, weighted Cayley measures,
     circle-measure moments, and the `Measure.map`/`withDensity` body found no exact D5 owner.
   * The fixed-scale `cayley` in `D5.S3.Analytic.LiCausalTrichotomy` is specialized to scale
     `1/2`; the source theorem requires every positive scale, so its formula is constructed here.
   * Pinned Mathlib supplies `fourierSubalgebra_separatesPoints`, finite-measure extensionality
     by a separating star subalgebra, `MeasurableEmbedding.map_injective`, and
     `withDensity_inv_same`. No injective encoder or measure-uniqueness premise is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open BoundedContinuousFunction MeasureTheory Set
open scoped ENNReal

namespace D5.S3.Observer.MeasureSeparation.OneScaleInformationalCompleteness

private lemma cayley_denominator_ne (a : Real) (ha : 0 < a) (xi : Real) :
    (xi : Complex) - (a : Complex) * Complex.I ≠ 0 := by
  intro h
  have imaginary := congrArg Complex.im h
  norm_num at imaginary
  exact ha.ne' imaginary

private lemma cayley_norm (a : Real) (ha : 0 < a) (xi : Real) :
    ‖((xi : Complex) + (a : Complex) * Complex.I) /
        ((xi : Complex) - (a : Complex) * Complex.I)‖ = 1 := by
  have denominatorNe := cayley_denominator_ne a ha xi
  rw [norm_div]
  have equalNorm :
      ‖(xi : Complex) + (a : Complex) * Complex.I‖ =
        ‖(xi : Complex) - (a : Complex) * Complex.I‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero,
      Complex.add_im, mul_one, zero_add, Complex.sub_re, Complex.sub_im, zero_sub]
    ring
  rw [equalNorm, div_self (norm_ne_zero_iff.mpr denominatorNe)]

private lemma continuous_cayley (a : Real) (ha : 0 < a) :
    Continuous (fun xi : Real =>
      ((xi : Complex) + (a : Complex) * Complex.I) /
        ((xi : Complex) - (a : Complex) * Complex.I)) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  exact fun xi => cayley_denominator_ne a ha xi

private lemma injective_cayley (a : Real) (ha : 0 < a) :
    Function.Injective (fun xi : Real =>
      ((xi : Complex) + (a : Complex) * Complex.I) /
        ((xi : Complex) - (a : Complex) * Complex.I)) := by
  intro xi eta equality
  have xiDenominatorNe := cayley_denominator_ne a ha xi
  have etaDenominatorNe := cayley_denominator_ne a ha eta
  field_simp [xiDenominatorNe, etaDenominatorNe] at equality
  have imaginary := congrArg Complex.im equality
  norm_num at imaginary
  nlinarith

/-- All integer moments at one positive Cayley scale uniquely determine the original real-axis
spectrum. The circle measure and every ingredient of its moment sequence are constructed from the
source measures, the resolvent weight, and the canonical scaled Cayley map. -/
theorem one_scale_informational_completeness
    (a : Real) (scalePositive : 0 < a) (nu₁ nu₂ : Measure Real)
    (finiteBudget₁ : HasFiniteIntegral (fun xi : Real => (xi ^ 2 + a ^ 2)⁻¹) nu₁)
    (finiteBudget₂ : HasFiniteIntegral (fun xi : Real => (xi ^ 2 + a ^ 2)⁻¹) nu₂) :
    let density : Real -> ENNReal := fun xi => ENNReal.ofReal ((xi ^ 2 + a ^ 2)⁻¹)
    let cayleyPoint : Real -> Circle := fun xi =>
      ⟨((xi : Complex) + (a : Complex) * Complex.I) /
          ((xi : Complex) - (a : Complex) * Complex.I),
        by
          change dist (((xi : Complex) + (a : Complex) * Complex.I) /
            ((xi : Complex) - (a : Complex) * Complex.I)) 0 = 1
          simpa [dist_eq_norm] using cayley_norm a scalePositive xi⟩
    let cayleyCoordinate : Real -> AddCircle (2 * Real.pi) := fun xi =>
      AddCircle.homeomorphCircle'.symm (cayleyPoint xi)
    let circleMeasure : Measure Real -> Measure (AddCircle (2 * Real.pi)) := fun nu =>
      Measure.map cayleyCoordinate (nu.withDensity density)
    (forall n : Int,
      (∫ theta, fourier n theta ∂circleMeasure nu₁) =
        ∫ theta, fourier n theta ∂circleMeasure nu₂) ->
      nu₁ = nu₂ := by
  dsimp only
  let density : Real -> ENNReal := fun xi => ENNReal.ofReal ((xi ^ 2 + a ^ 2)⁻¹)
  let cayleyPoint : Real -> Circle := fun xi =>
    ⟨((xi : Complex) + (a : Complex) * Complex.I) /
        ((xi : Complex) - (a : Complex) * Complex.I),
      by
        change dist (((xi : Complex) + (a : Complex) * Complex.I) /
          ((xi : Complex) - (a : Complex) * Complex.I)) 0 = 1
        simpa [dist_eq_norm] using cayley_norm a scalePositive xi⟩
  let cayleyCoordinate : Real -> AddCircle (2 * Real.pi) := fun xi =>
    AddCircle.homeomorphCircle'.symm (cayleyPoint xi)
  let weighted₁ : Measure Real := nu₁.withDensity density
  let weighted₂ : Measure Real := nu₂.withDensity density
  let circle₁ : Measure (AddCircle (2 * Real.pi)) := Measure.map cayleyCoordinate weighted₁
  let circle₂ : Measure (AddCircle (2 * Real.pi)) := Measure.map cayleyCoordinate weighted₂
  intro momentEquality
  have densityMeasurable : Measurable density := by
    dsimp only [density]
    fun_prop
  have cayleyPointContinuous : Continuous cayleyPoint := by
    apply Continuous.subtype_mk
    exact continuous_cayley a scalePositive
  have cayleyPointInjective : Function.Injective cayleyPoint := by
    intro xi eta equality
    exact injective_cayley a scalePositive (congrArg Subtype.val equality)
  have coordinateContinuous : Continuous cayleyCoordinate :=
    AddCircle.homeomorphCircle'.symm.continuous.comp cayleyPointContinuous
  have coordinateInjective : Function.Injective cayleyCoordinate :=
    AddCircle.homeomorphCircle'.symm.injective.comp cayleyPointInjective
  have coordinateEmbedding : MeasurableEmbedding cayleyCoordinate :=
    coordinateContinuous.measurableEmbedding coordinateInjective
  letI : IsFiniteMeasure weighted₁ :=
    isFiniteMeasure_withDensity_ofReal finiteBudget₁
  letI : IsFiniteMeasure weighted₂ :=
    isFiniteMeasure_withDensity_ofReal finiteBudget₂
  letI : IsFiniteMeasure circle₁ := weighted₁.isFiniteMeasure_map cayleyCoordinate
  letI : IsFiniteMeasure circle₂ := weighted₂.isFiniteMeasure_map cayleyCoordinate
  letI : Fact (0 < (2 * Real.pi : Real)) := ⟨by positivity⟩
  have circleEquality : circle₁ = circle₂ := by
    let A : StarSubalgebra Complex
        (BoundedContinuousFunction (AddCircle (2 * Real.pi)) Complex) :=
      fourierSubalgebra.comap (toContinuousMapStarₐ Complex)
    have mappedAlgebra : A.map (toContinuousMapStarₐ Complex) = fourierSubalgebra := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hf
        refine ⟨ContinuousMap.equivBoundedOfCompact _ _ f, ?_, ?_⟩
        · exact hf
        · ext theta
          rfl
    apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (𝕜 := Complex)
    · rw [mappedAlgebra]
      exact fourierSubalgebra_separatesPoints
    · intro g hg
      have spanMembership :
          g.toContinuousMap ∈ Submodule.span Complex (Set.range (@fourier (2 * Real.pi))) := by
        change (toContinuousMapStarₐ Complex) g ∈ fourierSubalgebra at hg
        have hg' : g.toContinuousMap ∈ fourierSubalgebra.toSubalgebra.toSubmodule := hg
        rw [fourierSubalgebra_coe] at hg'
        exact hg'
      refine Submodule.span_induction (p := fun f _ =>
          (∫ theta, f theta ∂circle₁) = ∫ theta, f theta ∂circle₂)
        ?_ ?_ ?_ ?_ spanMembership
      · intro f hf
        obtain ⟨n, rfl⟩ := hf
        exact momentEquality n
      · simp
      · intro f g hf hg fEquality gEquality
        have fIntegrable₁ : Integrable f circle₁ := by
          exact (BoundedContinuousFunction.integrable circle₁
            (ContinuousMap.equivBoundedOfCompact _ _ f)).congr
              (ae_of_all _ fun theta => by rfl)
        have gIntegrable₁ : Integrable g circle₁ := by
          exact (BoundedContinuousFunction.integrable circle₁
            (ContinuousMap.equivBoundedOfCompact _ _ g)).congr
              (ae_of_all _ fun theta => by rfl)
        have fIntegrable₂ : Integrable f circle₂ := by
          exact (BoundedContinuousFunction.integrable circle₂
            (ContinuousMap.equivBoundedOfCompact _ _ f)).congr
              (ae_of_all _ fun theta => by rfl)
        have gIntegrable₂ : Integrable g circle₂ := by
          exact (BoundedContinuousFunction.integrable circle₂
            (ContinuousMap.equivBoundedOfCompact _ _ g)).congr
              (ae_of_all _ fun theta => by rfl)
        simp only [ContinuousMap.add_apply]
        rw [integral_add fIntegrable₁ gIntegrable₁, integral_add fIntegrable₂ gIntegrable₂,
          fEquality, gEquality]
      · intro scalar f hf fEquality
        simpa only [ContinuousMap.coe_smul, Pi.smul_apply, integral_smul] using
          congrArg (fun value => scalar • value) fEquality
  have weightedEquality : weighted₁ = weighted₂ :=
    coordinateEmbedding.map_injective circleEquality
  have densityNonzero (nu : Measure Real) : ∀ᵐ xi ∂nu, density xi ≠ 0 := by
    filter_upwards [] with xi
    dsimp only [density]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have densityFinite (nu : Measure Real) : ∀ᵐ xi ∂nu, density xi ≠ ∞ := by
    filter_upwards [] with xi
    exact ENNReal.ofReal_ne_top
  calc
    nu₁ = weighted₁.withDensity (fun xi => (density xi)⁻¹) :=
      (withDensity_inv_same densityMeasurable (densityNonzero nu₁) (densityFinite nu₁)).symm
    _ = weighted₂.withDensity (fun xi => (density xi)⁻¹) := by rw [weightedEquality]
    _ = nu₂ :=
      withDensity_inv_same densityMeasurable (densityNonzero nu₂) (densityFinite nu₂)

#print axioms one_scale_informational_completeness

end D5.S3.Observer.MeasureSeparation.OneScaleInformationalCompleteness

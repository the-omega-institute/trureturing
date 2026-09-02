/- GID: D5/S3/Analytic/ZetaObservation/ChristoffelSupportDecay
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaObservation/ChristoffelSupportDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit-circle support gives explicit exterior witnesses and exponential cost decay. -/

import D5.S3.Analytic.ZetaObservation.ChristoffelAtomFloor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-09-02):
   * Repository searches found the canonical `christoffelEvaluationCost` in
     `ChristoffelAtomFloor`, but no theorem giving the exterior support bound
     or its limit. This module imports that owner and introduces no definition.
   * Pinned Mathlib contains no Christoffel whole-theorem hit. The exact
     ingredients used below are `support_mem_ae`, `eval_monomial`,
     `natDegree_monomial_le`, and the ENNReal geometric-power limit.
   * The third-party dependency route is unnecessary: the repository owner
     and pinned Mathlib provide the canonical objects and proof ingredients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ZetaObservation.ChristoffelSupportDecay

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

open D5.S3.Analytic.ZetaObservation.ChristoffelAtomFloor

/-- A finite positive measure supported on the unit circle admits the explicit
polynomial witness `w⁻ᴺ zᴺ` at every exterior point. Its Christoffel evaluation
cost is bounded by the total circle mass times `|w|⁻²ᴺ`, and hence tends to
zero. Nonnegativity is encoded by the `ENNReal` codomain of the canonical cost. -/
theorem christoffel_support_decay
    (measure : Measure Complex) [IsFiniteMeasure measure]
    (point : Complex) (outside : 1 < ‖point‖)
    (supported : Measure.support measure ⊆ sphere (0 : Complex) 1) :
    (∀ degree : Nat,
      let witness : Polynomial Complex :=
        Polynomial.monomial degree (point⁻¹ ^ degree)
      witness.natDegree ≤ degree ∧
      witness.eval point = 1 ∧
      (∀ z ∈ sphere (0 : Complex) 1,
        ‖witness.eval z‖ = ‖point‖⁻¹ ^ degree) ∧
      christoffelEvaluationCost measure point degree ≤
        measure (sphere (0 : Complex) 1) *
          (ENNReal.ofReal ‖point‖)⁻¹ ^ (2 * degree)) ∧
    Tendsto (fun degree => christoffelEvaluationCost measure point degree)
      atTop (𝓝 0) := by
  have pointNormPositive : 0 < ‖point‖ := lt_trans zero_lt_one outside
  have pointNonzero : point ≠ 0 := norm_ne_zero_iff.mp pointNormPositive.ne'
  let ratio : ENNReal := (ENNReal.ofReal ‖point‖)⁻¹
  have ratioLessThanOne : ratio < 1 := by
    exact ENNReal.inv_lt_one.mpr (ENNReal.one_lt_ofReal.mpr outside)
  have supportAlmostEverywhere :
      ∀ᵐ z ∂measure, z ∈ Measure.support measure :=
    Measure.support_mem_ae
  have sphereAlmostEverywhere : ∀ᵐ z ∂measure, z ∈ sphere (0 : Complex) 1 :=
    supportAlmostEverywhere.mono fun _ hz => supported hz
  have sphereMeasure : measure (sphere (0 : Complex) 1) = measure Set.univ :=
    (MeasureTheory.ae_mem_iff_measure_eq
      (isClosed_sphere.measurableSet.nullMeasurableSet)).mp sphereAlmostEverywhere
  have witnessValue (degree : Nat) :
      (Polynomial.monomial degree (point⁻¹ ^ degree)).eval point = 1 := by
    rw [Polynomial.eval_monomial, ← mul_pow]
    simp [pointNonzero]
  have witnessNorm (degree : Nat) (z : Complex)
      (hz : z ∈ sphere (0 : Complex) 1) :
      ‖(Polynomial.monomial degree (point⁻¹ ^ degree)).eval z‖ =
        ‖point‖⁻¹ ^ degree := by
    have normZ : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere] using hz
    rw [Polynomial.eval_monomial, norm_mul, norm_pow, norm_inv, norm_pow,
      normZ, one_pow, mul_one]
  have witnessEnergy (degree : Nat) :
      ∫⁻ z, ENNReal.ofReal
          (Complex.normSq
            ((Polynomial.monomial degree (point⁻¹ ^ degree)).eval z)) ∂measure =
        measure (sphere (0 : Complex) 1) * ratio ^ (2 * degree) := by
    have integrandAlmostEverywhere :
        (fun z => ENNReal.ofReal
          (Complex.normSq
            ((Polynomial.monomial degree (point⁻¹ ^ degree)).eval z))) =ᵐ[measure]
          fun _ => ratio ^ (2 * degree) :=
      sphereAlmostEverywhere.mono fun z hz => by
        change ENNReal.ofReal
          (Complex.normSq
            ((Polynomial.monomial degree (point⁻¹ ^ degree)).eval z)) = _
        rw [Complex.normSq_eq_norm_sq, witnessNorm degree z hz]
        calc
          ENNReal.ofReal ((‖point‖⁻¹ ^ degree) ^ 2) =
              (ENNReal.ofReal (‖point‖⁻¹ ^ degree)) ^ 2 :=
            ENNReal.ofReal_pow (by positivity) 2
          _ = ((ENNReal.ofReal ‖point‖)⁻¹ ^ degree) ^ 2 := by
            rw [ENNReal.ofReal_pow (by positivity)]
            rw [ENNReal.ofReal_inv_of_pos pointNormPositive]
          _ = ratio ^ (2 * degree) := by
            simp only [ratio]
            rw [← pow_mul, Nat.mul_comm]
    calc
      ∫⁻ z, ENNReal.ofReal
          (Complex.normSq
            ((Polynomial.monomial degree (point⁻¹ ^ degree)).eval z)) ∂measure =
          ∫⁻ _ : Complex, ratio ^ (2 * degree) ∂measure :=
        lintegral_congr_ae integrandAlmostEverywhere
      _ = ratio ^ (2 * degree) * measure Set.univ := lintegral_const _
      _ = measure (sphere (0 : Complex) 1) * ratio ^ (2 * degree) := by
        rw [← sphereMeasure, mul_comm]
  have costBound (degree : Nat) :
      christoffelEvaluationCost measure point degree ≤
        measure (sphere (0 : Complex) 1) * ratio ^ (2 * degree) := by
    unfold christoffelEvaluationCost
    refine iInf_le_of_le
      (⟨Polynomial.monomial degree (point⁻¹ ^ degree),
        Polynomial.natDegree_monomial_le _, witnessValue degree⟩) ?_
    exact (witnessEnergy degree).le
  constructor
  · intro degree
    exact ⟨Polynomial.natDegree_monomial_le _, witnessValue degree,
      witnessNorm degree, costBound degree⟩
  · have ratioSquaredLessThanOne : ratio ^ 2 < 1 :=
      pow_lt_one₀ bot_le ratioLessThanOne two_ne_zero
    have geometricLimit :
        Tendsto (fun degree : Nat => ratio ^ (2 * degree)) atTop (𝓝 0) := by
      simpa [pow_mul] using
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ratioSquaredLessThanOne)
    have boundLimit :
        Tendsto
          (fun degree : Nat =>
            measure (sphere (0 : Complex) 1) * ratio ^ (2 * degree))
          atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul geometricLimit
        (Or.inr (measure_ne_top measure (sphere (0 : Complex) 1)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds boundLimit (fun _ => bot_le) costBound

#print axioms christoffel_support_decay

end D5.S3.Analytic.ZetaObservation.ChristoffelSupportDecay

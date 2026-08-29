/- GID: D5/S3/Observer/Tomography/RationalContactSupport
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/RationalContactSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Kernel contact polynomials vanish on the residual support of a rational Gram floor. -/

import D5.S3.Weil.Budget.FullCirclePrimalAttainment
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Algebra.Polynomial

/- Library-search audit trail (2026-08-29):
   * Exact D5 searches for rational contact support, polynomial contact
     numerators, and Gram-kernel support localization found no existing owner.
   * Body-shape searches for rational feature quotients and conjugate-weighted
     numerator sums found no canonical D5 primitive. No new definition or
     abbreviation is introduced; the public statement constructs these objects.
   * `FullCirclePrimalAttainment.normalizedCircleHaar` is the canonical normalized
     circle Haar measure and is imported rather than redeclared.
   * Pinned Mathlib's `integral_add_measure`, `integral_smul_nnreal_measure`,
     `integral_eq_zero_iff_of_nonneg`, and `Measure.support_subset_of_isClosed`
     supply the decomposition, zero-integral, and support steps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal
open D5.S3.Weil.Budget.FullCirclePrimalAttainment

namespace D5.S3.Observer.Tomography.RationalContactSupport

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- A finite rational feature family is constructed from polynomial numerators
and a denominator with no unit-circle zeros. Add an arbitrary finite positive
residual measure to a nonnegative normalized-Haar floor and form the two Gram
matrices. Every vector in the kernel of the Gram difference has a contact
polynomial that vanishes throughout the residual support. -/
theorem rational_contact_support
    (n : Nat)
    (numerator : Fin n -> Polynomial Complex)
    (denominator : Polynomial Complex)
    (denominatorNonzero : ∀ z : Circle,
      denominator.eval (z : Complex) ≠ 0)
    (alpha : NNReal)
    (residual : FiniteMeasure Circle) :
    let feature : Circle -> Fin n -> Complex := fun z i =>
      (numerator i).eval (z : Complex) / denominator.eval (z : Complex)
    let completion : FiniteMeasure Circle :=
      alpha • normalizedCircleHaar + residual
    let gram : Matrix (Fin n) (Fin n) Complex := fun i j =>
      ∫ z, feature z i * star (feature z j) ∂(completion : Measure Circle)
    let haarGram : Matrix (Fin n) (Fin n) Complex := fun i j =>
      ∫ z, feature z i * star (feature z j)
        ∂(normalizedCircleHaar : Measure Circle)
    let contactPolynomial : (Fin n -> Complex) -> Polynomial Complex := fun c =>
      ∑ i, Polynomial.C (star (c i)) * numerator i
    ∀ c : Fin n -> Complex,
      (gram - alpha • haarGram) *ᵥ c = 0 ->
      (((completion : Measure Circle) -
          ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)).support
        ⊆ {z : Circle | (contactPolynomial c).eval (z : Complex) = 0}) := by
  dsimp only
  let feature : Circle -> Fin n -> Complex := fun z i =>
    (numerator i).eval (z : Complex) / denominator.eval (z : Complex)
  let completion : FiniteMeasure Circle :=
    alpha • normalizedCircleHaar + residual
  let gram : Matrix (Fin n) (Fin n) Complex := fun i j =>
    ∫ z, feature z i * star (feature z j) ∂(completion : Measure Circle)
  let haarGram : Matrix (Fin n) (Fin n) Complex := fun i j =>
    ∫ z, feature z i * star (feature z j)
      ∂(normalizedCircleHaar : Measure Circle)
  let contactPolynomial : (Fin n -> Complex) -> Polynomial Complex := fun c =>
    ∑ i, Polynomial.C (star (c i)) * numerator i
  change ∀ c : Fin n -> Complex,
    (gram - alpha • haarGram) *ᵥ c = 0 ->
    (((completion : Measure Circle) -
        ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)).support
      ⊆ {z : Circle | (contactPolynomial c).eval (z : Complex) = 0})
  intro c kernel
  let residualGram : Matrix (Fin n) (Fin n) Complex := fun i j =>
    ∫ z, feature z i * star (feature z j) ∂(residual : Measure Circle)
  have denominatorContinuous :
      Continuous (fun z : Circle => denominator.eval (z : Complex)) :=
    denominator.continuous.comp continuous_subtype_val
  have featureContinuous (i : Fin n) : Continuous (fun z => feature z i) := by
    exact ((numerator i).continuous.comp continuous_subtype_val).div
      denominatorContinuous denominatorNonzero
  have integrandContinuous (i j : Fin n) :
      Continuous (fun z => feature z i * star (feature z j)) := by
    fun_prop
  have integrandIntegrable (measure : FiniteMeasure Circle) (i j : Fin n) :
      Integrable (fun z => feature z i * star (feature z j))
        (measure : Measure Circle) := by
    simpa using (integrandContinuous i j).continuousOn.integrableOn_compact
      (μ := (measure : Measure Circle)) isCompact_univ
  have gramDecomposition : gram = alpha • haarGram + residualGram := by
    ext i j
    change
      (∫ z, feature z i * star (feature z j)
        ∂((alpha • normalizedCircleHaar + residual : FiniteMeasure Circle) : Measure Circle)) =
        alpha •
          (∫ z, feature z i * star (feature z j)
            ∂(normalizedCircleHaar : Measure Circle)) +
          ∫ z, feature z i * star (feature z j) ∂(residual : Measure Circle)
    rw [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul]
    have floorIntegrable :
        Integrable (fun z => feature z i * star (feature z j))
          (alpha • (normalizedCircleHaar : Measure Circle)) := by
      simpa only [FiniteMeasure.toMeasure_smul] using
        (integrandIntegrable (alpha • normalizedCircleHaar) i j)
    rw [integral_add_measure
      floorIntegrable
      (integrandIntegrable residual i j)]
    simp
  have residualKernel : residualGram *ᵥ c = 0 := by
    rw [gramDecomposition] at kernel
    simpa using kernel
  let contact : Circle -> Complex := fun z =>
    ∑ i, star (c i) * feature z i
  have contactContinuous : Continuous contact := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (featureContinuous i)
  have contactPolynomialEval (z : Circle) :
      (contactPolynomial c).eval (z : Complex) =
        denominator.eval (z : Complex) * contact z := by
    simp only [contactPolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, contact, feature]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [denominatorNonzero z]
  have residualQuadraticZero :
      ∫ z, contact z * star (contact z) ∂(residual : Measure Circle) = 0 := by
    calc
      ∫ z, contact z * star (contact z) ∂(residual : Measure Circle) =
          ∫ z, ∑ i, ∑ j,
            star (c i) *
              (feature z i * star (feature z j)) * c j
            ∂(residual : Measure Circle) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
              change
                (∑ i, star (c i) * feature z i) *
                    star (∑ j, star (c j) * feature z j) = _
              rw [star_sum]
              simp only [star_mul, star_star]
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              ring_nf
      _ = ∑ i, ∑ j,
          star (c i) * residualGram i j * c j := by
            rw [integral_finsetSum Finset.univ]
            · apply Finset.sum_congr rfl
              intro i _
              rw [integral_finsetSum Finset.univ]
              · apply Finset.sum_congr rfl
                intro j _
                simp only [residualGram]
                simp only [integral_const_mul, integral_mul_const]
              · intro j _
                exact ((integrandIntegrable residual i j).const_mul (star (c i))).mul_const (c j)
            · intro i _
              exact integrable_finsetSum Finset.univ fun j _ =>
                ((integrandIntegrable residual i j).const_mul (star (c i))).mul_const (c j)
      _ = star c ⬝ᵥ (residualGram *ᵥ c) := by
            simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
            ring_nf
      _ = 0 := by rw [residualKernel]; simp
  have residualNormSqZero :
      ∫ z, Complex.normSq (contact z) ∂(residual : Measure Circle) = 0 := by
    have complexIntegral :
        (∫ z, (Complex.normSq (contact z) : Complex)
          ∂(residual : Measure Circle)) = 0 := by
      rw [Complex.star_def] at residualQuadraticZero
      simpa only [Complex.mul_conj] using residualQuadraticZero
    rw [integral_complex_ofReal] at complexIntegral
    exact Complex.ofReal_injective complexIntegral
  have normSqIntegrable :
      Integrable (fun z => Complex.normSq (contact z))
        (residual : Measure Circle) := by
    have normSqContinuous : Continuous (fun z => Complex.normSq (contact z)) := by
      fun_prop
    simpa using normSqContinuous.continuousOn.integrableOn_compact
      (μ := (residual : Measure Circle)) isCompact_univ
  have contactZeroAlmostEverywhere : contact =ᵐ[(residual : Measure Circle)] 0 := by
    have normSqZeroAlmostEverywhere :=
      (integral_eq_zero_iff_of_nonneg
        (fun z => Complex.normSq_nonneg (contact z)) normSqIntegrable).1
        residualNormSqZero
    filter_upwards [normSqZeroAlmostEverywhere] with z hz
    change contact z = 0
    exact Complex.normSq_eq_zero.mp hz
  have polynomialZeroAlmostEverywhere :
      (fun z : Circle => (contactPolynomial c).eval (z : Complex))
        =ᵐ[(residual : Measure Circle)] 0 := by
    filter_upwards [contactZeroAlmostEverywhere] with z hz
    change contact z = 0 at hz
    simpa [hz] using contactPolynomialEval z
  have polynomialZeroClosed :
      IsClosed {z : Circle | (contactPolynomial c).eval (z : Complex) = 0} := by
    exact isClosed_eq
      ((contactPolynomial c).continuous.comp continuous_subtype_val)
      continuous_const
  have residualSupport :
      (residual : Measure Circle).support ⊆
        {z : Circle | (contactPolynomial c).eval (z : Complex) = 0} :=
    Measure.support_subset_of_isClosed polynomialZeroClosed
      polynomialZeroAlmostEverywhere
  have completionResidual :
      (completion : Measure Circle) -
          ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) =
        (residual : Measure Circle) := by
    change
      (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
          (residual : Measure Circle)) -
        ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) =
          (residual : Measure Circle)
    simpa only [add_comm] using
      (Measure.add_sub_cancel
        (μ := (residual : Measure Circle))
        (ν := ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)))
  rw [completionResidual]
  exact residualSupport

#print axioms rational_contact_support

end D5.S3.Observer.Tomography.RationalContactSupport

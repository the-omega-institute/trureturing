/- GID: D5/S3/Observer/BlockStructure/RationalToeplitzCollapse
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/RationalToeplitzCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A common denominator turns the feature Gram matrix into one moment congruence. -/

import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 searches for rational Gram matrices, common-denominator moment matrices,
     and the feature-integral body found no exact owner or reusable definition.
   * Body-shape searches for polynomial-evaluation quotients and norm-square
     `withDensity` measures found no canonical D5 primitive.
   * Pinned Mathlib supplies integration against `withDensity`, finite-sum
     integration, polynomial continuity, and matrix conjugate transpose, but no
     packaged rational-feature congruence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators ENNReal

namespace D5.S3.Observer.BlockStructure.RationalToeplitzCollapse

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- A feature family built from a common polynomial denominator has Gram matrix
equal to the congruence of its weighted monomial moment matrix. -/
theorem rational_toeplitz_collapse
    (n : Nat) (mu : FiniteMeasure Circle)
    (coefficient : Matrix (Fin n) (Fin n) Complex)
    (denominator : Polynomial Complex)
    (denominatorNonzero : forall z : Circle,
      denominator.eval (z : Complex) ≠ 0) :
    let monomial : Circle -> Fin n -> Complex := fun z j =>
      (z : Complex) ^ (j : Nat)
    let feature : Circle -> Fin n -> Complex := fun z i =>
      (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
    let weighted : Measure Circle :=
      (mu : Measure Circle).withDensity fun z =>
        ENNReal.ofReal (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let gram : Matrix (Fin n) (Fin n) Complex := fun i j =>
      ∫ z, feature z i * star (feature z j) ∂(mu : Measure Circle)
    let moment : Matrix (Fin n) (Fin n) Complex := fun i j =>
      ∫ z, monomial z i * star (monomial z j) ∂weighted
    gram = coefficient * moment * coefficientᴴ := by
  dsimp only
  let monomial : Circle -> Fin n -> Complex := fun z j =>
    (z : Complex) ^ (j : Nat)
  let density : Circle -> Real := fun z =>
    (Complex.normSq (denominator.eval (z : Complex)))⁻¹
  let weighted : Measure Circle :=
    (mu : Measure Circle).withDensity fun z => ENNReal.ofReal (density z)
  let moment : Matrix (Fin n) (Fin n) Complex := fun i j =>
    ∫ z, monomial z i * star (monomial z j) ∂weighted
  change ((fun i j =>
      ∫ z, (coefficient *ᵥ monomial z) i /
          denominator.eval (z : Complex) *
        star ((coefficient *ᵥ monomial z) j /
          denominator.eval (z : Complex)) ∂(mu : Measure Circle)) :
      Matrix (Fin n) (Fin n) Complex) =
    coefficient * moment * coefficientᴴ
  have evalContinuous : Continuous fun z : Circle =>
      denominator.eval (z : Complex) :=
    denominator.continuous.comp continuous_subtype_val
  have normSqContinuous : Continuous fun z : Circle =>
      Complex.normSq (denominator.eval (z : Complex)) := by
    fun_prop
  have normSqNonzero : forall z : Circle,
      Complex.normSq (denominator.eval (z : Complex)) ≠ 0 := by
    intro z normSqZero
    exact denominatorNonzero z (Complex.normSq_eq_zero.mp normSqZero)
  have densityContinuous : Continuous density := by
    exact normSqContinuous.inv₀ normSqNonzero
  have densityNonnegative : forall z : Circle, 0 <= density z := by
    intro z
    exact inv_nonneg.mpr (Complex.normSq_nonneg _)
  have densityIntegrable : Integrable density (mu : Measure Circle) := by
    apply integrableOn_univ.mp
    exact
      densityContinuous.continuousOn.integrableOn_compact
        (μ := (mu : Measure Circle)) isCompact_univ
  letI : IsFiniteMeasure weighted := by
    dsimp only [weighted]
    exact isFiniteMeasure_withDensity_ofReal densityIntegrable.hasFiniteIntegral
  have monomialContinuous (j : Fin n) : Continuous fun z => monomial z j := by
    dsimp only [monomial]
    fun_prop
  have weightedTermIntegrable (i j : Fin n) :
      Integrable (fun z => density z *
        (monomial z i * star (monomial z j))) (mu : Measure Circle) := by
    have continuousTerm : Continuous fun z => density z *
        (monomial z i * star (monomial z j)) := by
      fun_prop
    apply integrableOn_univ.mp
    exact
      continuousTerm.continuousOn.integrableOn_compact
        (μ := (mu : Measure Circle)) isCompact_univ
  have momentIdentity (i j : Fin n) :
      (∫ z, monomial z i * star (monomial z j) ∂weighted) =
        ∫ z, density z * (monomial z i * star (monomial z j))
          ∂(mu : Measure Circle) := by
    rw [show weighted = (mu : Measure Circle).withDensity
        (fun z => ENNReal.ofReal (density z)) by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards [] with z
      rw [ENNReal.toReal_ofReal (densityNonnegative z)]
      rw [Complex.real_smul]
    · exact densityContinuous.measurable.ennreal_ofReal
    · filter_upwards [] with z
      exact ENNReal.ofReal_lt_top
  ext i j
  change (∫ z, (coefficient *ᵥ monomial z) i /
      denominator.eval (z : Complex) *
        star ((coefficient *ᵥ monomial z) j /
          denominator.eval (z : Complex)) ∂(mu : Measure Circle)) =
    ∑ k, (∑ l, coefficient i l *
      (∫ z, monomial z l * star (monomial z k) ∂weighted)) *
        star (coefficient j k)
  simp_rw [momentIdentity]
  have termIntegral (l k : Fin n) :
      coefficient i l *
          (∫ z, density z * (monomial z l * star (monomial z k))
            ∂(mu : Measure Circle)) * star (coefficient j k) =
        ∫ z, coefficient i l *
            (density z * (monomial z l * star (monomial z k))) *
              star (coefficient j k) ∂(mu : Measure Circle) := by
    let term : Circle -> Complex := fun z =>
      density z * (monomial z l * star (monomial z k))
    have leftIdentity :
        coefficient i l * (∫ z, term z ∂(mu : Measure Circle)) =
          ∫ z, coefficient i l * term z ∂(mu : Measure Circle) :=
      (integral_const_mul (μ := (mu : Measure Circle))
        (coefficient i l) term).symm
    calc
      coefficient i l *
          (∫ z, density z * (monomial z l * star (monomial z k))
            ∂(mu : Measure Circle)) * star (coefficient j k) =
        (∫ z, coefficient i l * term z ∂(mu : Measure Circle)) *
          star (coefficient j k) := by rw [leftIdentity]
      _ = ∫ z, coefficient i l * term z * star (coefficient j k)
          ∂(mu : Measure Circle) :=
        (integral_mul_const_of_integrable
          ((weightedTermIntegrable l k).const_mul (coefficient i l))).symm
      _ = ∫ z, coefficient i l *
          (density z * (monomial z l * star (monomial z k))) *
            star (coefficient j k) ∂(mu : Measure Circle) := by rfl
  have rhsTerms :
      (∑ k, (∑ l, coefficient i l *
        (∫ z, density z * (monomial z l * star (monomial z k))
          ∂(mu : Measure Circle))) * star (coefficient j k)) =
        ∑ k, ∑ l, ∫ z, coefficient i l *
          (density z * (monomial z l * star (monomial z k))) *
            star (coefficient j k) ∂(mu : Measure Circle) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    exact termIntegral l k
  rw [rhsTerms]
  have innerIntegral (k : Fin n) :
      (∑ l, ∫ z, coefficient i l *
          (density z * (monomial z l * star (monomial z k))) *
            star (coefficient j k) ∂(mu : Measure Circle)) =
        ∫ z, ∑ l, coefficient i l *
          (density z * (monomial z l * star (monomial z k))) *
            star (coefficient j k) ∂(mu : Measure Circle) := by
    exact (integral_finsetSum Finset.univ fun l _ =>
      ((weightedTermIntegrable l k).const_mul (coefficient i l)).mul_const
        (star (coefficient j k))).symm
  have rhsInner :
      (∑ k, ∑ l, ∫ z, coefficient i l *
          (density z * (monomial z l * star (monomial z k))) *
            star (coefficient j k) ∂(mu : Measure Circle)) =
        ∑ k, ∫ z, ∑ l, coefficient i l *
          (density z * (monomial z l * star (monomial z k))) *
            star (coefficient j k) ∂(mu : Measure Circle) := by
    apply Finset.sum_congr rfl
    intro k _
    exact innerIntegral k
  rw [rhsInner]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with z
    let d : Complex := denominator.eval (z : Complex)
    have densityIdentity :
        ((density z : Real) : Complex) = (d * star d)⁻¹ := by
      dsimp only [density, d]
      rw [Complex.ofReal_inv, Complex.star_def, Complex.mul_conj]
    simp only [div_eq_mul_inv, mulVec, dotProduct]
    rw [star_mul, star_inv₀, star_sum]
    simp only [star_mul]
    rw [densityIdentity, _root_.mul_inv_rev]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    dsimp only [d]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro k _
    exact integrable_finsetSum Finset.univ fun l _ =>
      ((weightedTermIntegrable l k).const_mul (coefficient i l)).mul_const
        (star (coefficient j k))

#print axioms rational_toeplitz_collapse

end D5.S3.Observer.BlockStructure.RationalToeplitzCollapse

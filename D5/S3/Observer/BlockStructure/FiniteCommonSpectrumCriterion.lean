/- GID: D5/S3/Observer/BlockStructure/FiniteCommonSpectrumCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/FiniteCommonSpectrumCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize finite rational feature Grams by positive Hermitian Toeplitz transforms. -/

import D5.S3.Observer.BlockStructure.RationalToeplitzCollapse
import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge

/- Library-search audit trail (2026-09-04):
   * D5 name and body-shape searches found no exact owner for the inverse-
     congruence criterion. RationalToeplitzCollapse owns the forward rational
     Gram congruence, while TruncatedCircleMomentBridge owns the finite
     representing-measure converse; both are applied below.
   * Pinned Mathlib supplies reciprocal withDensity cancellation and
     nonsingular matrix inverse identities, but no truncated Toeplitz moment
     representation theorem.
   * Searches across the installed non-Mathlib Lake packages found no matching
     rational Gram or truncated Toeplitz representation declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal MatrixOrder
open D5.S3.Observer.BlockStructure.RationalToeplitzCollapse
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge

namespace D5.S3.Observer.BlockStructure.FiniteCommonSpectrumCriterion

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private theorem rational_gram_eq_reflected_moment_congruence
    (N : Nat) (mu : FiniteMeasure Circle)
    (coefficient : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (denominator : Polynomial Complex)
    (denominatorNonzero : forall z : Circle,
      denominator.eval (z : Complex) ≠ 0) :
    let monomial : Circle -> Fin (N + 1) -> Complex := fun z j =>
      (z : Complex) ^ (j : Nat)
    let feature : Circle -> Fin (N + 1) -> Complex := fun z i =>
      (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
    let rationalGram : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun i j =>
      ∫ z, feature z i * star (feature z j) ∂(mu : Measure Circle)
    let density : Circle -> ENNReal := fun z =>
      ENNReal.ofReal
        (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let weightedReflected : Measure Circle :=
      ((mu : Measure Circle).withDensity density).map Inv.inv
    rationalGram = coefficient *
      toeplitzMatrix (circleMoment weightedReflected) N * coefficientᴴ := by
  classical
  dsimp only
  have collapse := rational_toeplitz_collapse (N + 1) mu coefficient
    denominator denominatorNonzero
  dsimp only at collapse
  rw [collapse]
  congr 1
  congr 1
  ext i j
  let weighted : Measure Circle :=
    (mu : Measure Circle).withDensity fun z =>
      ENNReal.ofReal
        (Complex.normSq (denominator.eval (z : Complex)))⁻¹
  have circleMomentMapInv (k : Int) :
      circleMoment (weighted.map Inv.inv) k = circleMoment weighted (-k) := by
    simp only [circleMoment]
    have integrandContinuous : Continuous fun z : Circle =>
        (z : Complex) ^ (-k) :=
      continuous_subtype_val.zpow₀ (-k) fun z => Or.inl (Circle.coe_ne_zero z)
    rw [integral_map measurable_inv.aemeasurable
      integrandContinuous.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [show ((↑(z⁻¹) : Complex)) = (z : Complex)⁻¹ by exact Circle.coe_inv z]
    rw [_root_.inv_zpow']
  simp only [toeplitzMatrix]
  change (∫ z : Circle, (z : Complex) ^ (i : Nat) *
      star ((z : Complex) ^ (j : Nat)) ∂weighted) =
    circleMoment (weighted.map Inv.inv)
      (((i : Nat) : Int) - ((j : Nat) : Int))
  rw [circleMomentMapInv]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [neg_sub]
  rw [zpow_sub₀ (Circle.coe_ne_zero z)]
  rw [zpow_natCast, zpow_natCast, div_eq_mul_inv]
  congr 1
  rw [← Circle.coe_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

private theorem circle_moment_hermitian
    (mu : Measure Circle) [IsFiniteMeasure mu] (k : Int) :
    circleMoment mu (-k) = star (circleMoment mu k) := by
  have hHermitian := circle_moment_toeplitz_isHermitian mu k.natAbs
  cases k with
  | ofNat n =>
      let j : Fin (n + 1) := ⟨n, by simp⟩
      have h := hHermitian.apply (0 : Fin (n + 1)) j
      simpa [toeplitzMatrix, j, Int.negSucc_eq] using h.symm
  | negSucc n =>
      let j : Fin (n + 2) := ⟨n + 1, by simp⟩
      have h := hHermitian.apply j (0 : Fin (n + 2))
      simpa [toeplitzMatrix, j, Int.negSucc_eq] using h.symm

private theorem inverse_congruence_cancel
    {N : Nat}
    (A M : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (hA : IsUnit A) :
    A⁻¹ * (A * M * Aᴴ) * (A⁻¹)ᴴ = M := by
  let _ := hA.invertible
  rw [Matrix.conjTranspose_nonsing_inv]
  have hAstar : IsUnit Aᴴ := hA.star
  let _ := hAstar.invertible
  simp [Matrix.mul_assoc]

private theorem congruence_inverse_cancel
    {N : Nat}
    (A M : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (hA : IsUnit A) :
    A * (A⁻¹ * M * (A⁻¹)ᴴ) * Aᴴ = M := by
  let _ := hA.invertible
  rw [Matrix.conjTranspose_nonsing_inv]
  have hAstar : IsUnit Aᴴ := hA.star
  let _ := hAstar.invertible
  simp [Matrix.mul_assoc]

/-- A matrix is the Gram matrix of the full common-denominator rational feature
family exactly when its inverse coefficient congruence is a positive
Hermitian Toeplitz matrix. -/
theorem finite_common_spectrum_criterion
    (N : Nat)
    (coefficient : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex)
    (coefficientUnit : IsUnit coefficient)
    (denominator : Polynomial Complex)
    (denominatorNonzero : forall z : Circle,
      denominator.eval (z : Complex) ≠ 0)
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) :
    let monomial : Circle -> Fin (N + 1) -> Complex := fun z j =>
      (z : Complex) ^ (j : Nat)
    let feature : Circle -> Fin (N + 1) -> Complex := fun z i =>
      (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
    let rationalGram : FiniteMeasure Circle ->
        Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu i j =>
      ∫ z, feature z i * star (feature z j) ∂(mu : Measure Circle)
    let transformed := coefficient⁻¹ * G * (coefficient⁻¹)ᴴ
    (exists mu : FiniteMeasure Circle, G = rationalGram mu) ↔
      transformed.PosSemidef ∧
      exists moment : Int -> Complex,
        (forall k, moment (-k) = star (moment k)) ∧
        transformed = toeplitzMatrix moment N := by
  classical
  dsimp only
  let monomial : Circle -> Fin (N + 1) -> Complex := fun z j =>
    (z : Complex) ^ (j : Nat)
  let feature : Circle -> Fin (N + 1) -> Complex := fun z i =>
    (coefficient *ᵥ monomial z) i / denominator.eval (z : Complex)
  let rationalGram : FiniteMeasure Circle ->
      Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun mu i j =>
    ∫ z, feature z i * star (feature z j) ∂(mu : Measure Circle)
  let transformed : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    coefficient⁻¹ * G * (coefficient⁻¹)ᴴ
  change (exists mu : FiniteMeasure Circle, G = rationalGram mu) ↔
    transformed.PosSemidef ∧
      exists moment : Int -> Complex,
        (forall k, moment (-k) = star (moment k)) ∧
        transformed = toeplitzMatrix moment N
  constructor
  · rintro ⟨mu, gramIdentity⟩
    let densityReal : Circle -> Real := fun z =>
      (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let density : Circle -> ENNReal := fun z => ENNReal.ofReal (densityReal z)
    have densityContinuous : Continuous densityReal := by
      have evalContinuous : Continuous fun z : Circle =>
          denominator.eval (z : Complex) :=
        denominator.continuous.comp continuous_subtype_val
      have normSqContinuous : Continuous fun z : Circle =>
          Complex.normSq (denominator.eval (z : Complex)) := by fun_prop
      exact normSqContinuous.inv₀ fun z h =>
        denominatorNonzero z (Complex.normSq_eq_zero.mp h)
    have densityFinite :
        IsFiniteMeasure ((mu : Measure Circle).withDensity density) := by
      dsimp only [density]
      exact isFiniteMeasure_withDensity_ofReal
        (integrableOn_univ.mp
          (densityContinuous.continuousOn.integrableOn_compact
            (μ := (mu : Measure Circle)) isCompact_univ)).hasFiniteIntegral
    let weightedReflected : Measure Circle :=
      ((mu : Measure Circle).withDensity density).map Inv.inv
    let _ : IsFiniteMeasure weightedReflected := by
      dsimp only [weightedReflected]
      let _ : IsFiniteMeasure ((mu : Measure Circle).withDensity density) := densityFinite
      infer_instance
    let momentMatrix : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      toeplitzMatrix (circleMoment weightedReflected) N
    have gramCongruence :
        rationalGram mu = coefficient * momentMatrix * coefficientᴴ := by
      simpa only [rationalGram, feature, monomial, momentMatrix,
        weightedReflected, density, densityReal] using
        rational_gram_eq_reflected_moment_congruence N mu coefficient
          denominator denominatorNonzero
    have GCongruence : G = coefficient * momentMatrix * coefficientᴴ :=
      gramIdentity.trans gramCongruence
    have transformedMoment : transformed = momentMatrix := by
      dsimp only [transformed]
      rw [GCongruence]
      exact inverse_congruence_cancel coefficient momentMatrix coefficientUnit
    have momentPositive : momentMatrix.PosSemidef := by
      dsimp only [momentMatrix]
      exact circle_moment_toeplitz_posSemidef weightedReflected N
    refine ⟨?_, circleMoment weightedReflected, ?_, ?_⟩
    · rwa [transformedMoment]
    · exact circle_moment_hermitian weightedReflected
    · exact transformedMoment
  · rintro ⟨transformedPositive, moment, momentHermitian, transformedToeplitz⟩
    have toeplitzPositive : (toeplitzMatrix moment N).PosSemidef := by
      rwa [← transformedToeplitz]
    obtain ⟨sigma, sigmaMoments⟩ :=
      truncated_circle_moment_of_posSemidef N moment momentHermitian
        toeplitzPositive
    let tau : FiniteMeasure Circle := sigma.map Inv.inv
    let qReal : Circle -> Real := fun z =>
      Complex.normSq (denominator.eval (z : Complex))
    let q : Circle -> ENNReal := fun z => ENNReal.ofReal (qReal z)
    have qContinuous : Continuous qReal := by
      dsimp only [qReal]
      fun_prop
    have qIntegrable : Integrable qReal (tau : Measure Circle) :=
      integrableOn_univ.mp
        (qContinuous.continuousOn.integrableOn_compact
          (μ := (tau : Measure Circle)) isCompact_univ)
    let rhoMeasure : Measure Circle := (tau : Measure Circle).withDensity q
    let rhoFinite : IsFiniteMeasure rhoMeasure := by
      dsimp only [rhoMeasure, q]
      exact isFiniteMeasure_withDensity_ofReal qIntegrable.hasFiniteIntegral
    let rho : FiniteMeasure Circle := ⟨rhoMeasure, rhoFinite⟩
    let densityReal : Circle -> Real := fun z =>
      (Complex.normSq (denominator.eval (z : Complex)))⁻¹
    let density : Circle -> ENNReal := fun z => ENNReal.ofReal (densityReal z)
    have qMeasurable : Measurable q := qContinuous.measurable.ennreal_ofReal
    have qNeZero : forall z, q z ≠ 0 := by
      intro z
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Complex.normSq_pos.mpr (denominatorNonzero z)
    have qNeTop : forall z, q z ≠ ∞ := fun _ => ENNReal.ofReal_ne_top
    have densityEqInv : density = fun z => (q z)⁻¹ := by
      funext z
      dsimp only [density, densityReal, q, qReal]
      exact ENNReal.ofReal_inv_of_pos
        (Complex.normSq_pos.mpr (denominatorNonzero z))
    have reweightedRho :
        (rho : Measure Circle).withDensity density = (tau : Measure Circle) := by
      change rhoMeasure.withDensity density = (tau : Measure Circle)
      rw [densityEqInv]
      exact withDensity_inv_same qMeasurable
        (Filter.Eventually.of_forall qNeZero)
        (Filter.Eventually.of_forall qNeTop)
    let weightedReflected : Measure Circle :=
      ((rho : Measure Circle).withDensity density).map Inv.inv
    have reflectedRho : weightedReflected = (sigma : Measure Circle) := by
      dsimp only [weightedReflected]
      rw [reweightedRho]
      dsimp only [tau]
      rw [FiniteMeasure.toMeasure_map]
      rw [Measure.map_map measurable_inv measurable_inv]
      simp
    have momentRecovery :
        toeplitzMatrix (circleMoment weightedReflected) N =
          toeplitzMatrix moment N := by
      ext i j
      simp only [reflectedRho, toeplitzMatrix, circleMoment]
      exact sigmaMoments _ (by
        have hi := i.isLt
        have hj := j.isLt
        simp only [Nat.lt_add_one_iff] at hi hj
        omega)
    have gramCongruence :
        rationalGram rho = coefficient *
          toeplitzMatrix (circleMoment weightedReflected) N * coefficientᴴ := by
      simpa only [rationalGram, feature, monomial, weightedReflected,
        density, densityReal] using
        rational_gram_eq_reflected_moment_congruence N rho coefficient
          denominator denominatorNonzero
    refine ⟨rho, ?_⟩
    calc
      G = coefficient * transformed * coefficientᴴ := by
        symm
        dsimp only [transformed]
        exact congruence_inverse_cancel coefficient G coefficientUnit
      _ = coefficient * toeplitzMatrix moment N * coefficientᴴ := by
        rw [transformedToeplitz]
      _ = coefficient *
          toeplitzMatrix (circleMoment weightedReflected) N * coefficientᴴ := by
        rw [momentRecovery]
      _ = rationalGram rho := gramCongruence.symm

#print axioms finite_common_spectrum_criterion

end D5.S3.Observer.BlockStructure.FiniteCommonSpectrumCriterion

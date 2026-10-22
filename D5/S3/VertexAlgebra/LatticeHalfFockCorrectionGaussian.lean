/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGaussian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectionGaussian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian generating law for the original singleton and pair correction. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockDiagonalFusion
import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGaussian

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCurrentCorrection MvPolynomial
open scoped BigOperators

noncomputable section

def linearSource (D : LatticeData) (axes : Finset (Index D))
    (weight : Index D → ℂ) : Oscillator D :=
  ∑ index ∈ axes, weight index • X index

def correctedLinear (D : LatticeData) (charge : Charge D) (axes : Finset (Index D))
    (weight : Index D → ℂ) : CorrectionPolynomial D :=
  ∑ index ∈ axes, weight index • (X (some index) + singletonPolynomial D charge index)

def linearPairDerivation (D : LatticeData) (axes : Finset (Index D))
    (weight : Index D → ℂ) : Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D) :=
  ∑ index ∈ axes, weight index • pairDerivation D index

def pairQuadratic (D : LatticeData) (axes : Finset (Index D))
    (weight : Index D → ℂ) : CorrectionPolynomial D :=
  ∑ index ∈ axes, ∑ other ∈ axes,
    (weight index * weight other) • pairPolynomial D index other

private theorem lift_one (D : LatticeData) (charge : Charge D) :
    correctionLift D charge 1 = 1 := by
  have basis := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)) 0
  simpa [correctionLift, LatticeAllStateField.occurrences, correctionWord] using basis

private theorem lift_linear_mul (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) (polynomial : Oscillator D) :
    correctionLift D charge (polynomial * linearSource D axes weight) =
      correctedLinear D charge axes weight * correctionLift D charge polynomial +
        linearPairDerivation D axes weight (correctionLift D charge polynomial) := by
  classical
  simp only [linearSource, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    correctionLift_X_mul, insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, smul_add, Finset.sum_add_distrib,
    correctedLinear, Finset.sum_mul, smul_mul_assoc, linearPairDerivation,
    Derivation.sum_apply, Derivation.smul_apply]

private theorem pair_derivative_linear (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) :
    linearPairDerivation D axes weight (correctedLinear D charge axes weight) =
      pairQuadratic D axes weight := by
  classical
  have variable (index other : Index D) :
      pairDerivation D index (X (some other) + singletonPolynomial D charge other) =
        pairPolynomial D index other := by
    simp [singletonPolynomial, pairDerivation, mkDerivation_X, Derivation.leibniz,
      smul_eq_mul, Derivation.leibniz_pow]
  simp only [linearPairDerivation, Derivation.sum_apply, Derivation.smul_apply,
    correctedLinear, map_sum, map_smul, variable, Finset.smul_sum,
    smul_smul, pairQuadratic]

private theorem pair_derivative_quadratic (D : LatticeData)
    (axes : Finset (Index D)) (weight : Index D → ℂ) :
    linearPairDerivation D axes weight (pairQuadratic D axes weight) = 0 := by
  classical
  simp [linearPairDerivation, pairQuadratic, Derivation.sum_apply,
    Derivation.smul_apply, pairDerivation_pair]

private theorem lift_power_step (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) (degree : ℕ) :
    correctionLift D charge (linearSource D axes weight ^ (degree + 1)) =
      correctedLinear D charge axes weight *
        correctionLift D charge (linearSource D axes weight ^ degree) +
      linearPairDerivation D axes weight
        (correctionLift D charge (linearSource D axes weight ^ degree)) := by
  rw [pow_succ, lift_linear_mul]

private theorem pair_derivative_power (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) (degree : ℕ) :
    linearPairDerivation D axes weight
        (correctionLift D charge (linearSource D axes weight ^ (degree + 1))) =
      (degree + 1) • (pairQuadratic D axes weight *
        correctionLift D charge (linearSource D axes weight ^ degree)) := by
  induction degree with
  | zero =>
    simp [lift_power_step, lift_one, pair_derivative_linear]
  | succ degree previous =>
    rw [lift_power_step, map_add, Derivation.leibniz,
      pair_derivative_linear, previous, map_smul, Derivation.leibniz,
      pair_derivative_quadratic, zero_smul, zero_add]
    rw [lift_power_step]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem lift_power_recurrence (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) (degree : ℕ) :
    correctionLift D charge (linearSource D axes weight ^ (degree + 2)) =
      correctedLinear D charge axes weight *
        correctionLift D charge (linearSource D axes weight ^ (degree + 1)) +
      (degree + 1) • (pairQuadratic D axes weight *
        correctionLift D charge (linearSource D axes weight ^ degree)) := by
  rw [show degree + 2 = (degree + 1) + 1 by omega,
    lift_power_step, pair_derivative_power]

def correctedExponential (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.mk fun degree => (degree.factorial : ℂ)⁻¹ •
    correctionLift D charge (linearSource D axes weight ^ degree)

def gaussianDriver (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.C (correctedLinear D charge axes weight) * PowerSeries.X +
    PowerSeries.C ((1 / 2 : ℂ) • pairQuadratic D axes weight) * PowerSeries.X ^ 2

/- The coefficientwise object consumed by the native field is Corr itself.  Keeping
   this definition at the Corr boundary prevents the Gaussian calculation from
   silently replacing labelledRemainders by an abstract polynomial correction. -/
def literalCorrCreationCoefficient (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ)
    (degree shift : ℕ) : Oscillator D :=
  (Corr D charge (linearSource D axes weight ^ degree)) shift

private theorem corrected_exponential_derivative (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) :
    PowerSeries.derivative (CorrectionPolynomial D) (correctedExponential D charge axes weight) =
      correctedExponential D charge axes weight *
        (PowerSeries.C (correctedLinear D charge axes weight) +
          PowerSeries.C (pairQuadratic D axes weight) * PowerSeries.X) := by
  apply PowerSeries.ext
  intro degree
  rw [PowerSeries.coeff_derivative, mul_add, map_add,
    PowerSeries.coeff_mul_C, ← mul_assoc]
  cases degree with
  | zero =>
    simp [correctedExponential, lift_power_step, lift_one]
  | succ degree =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp only [correctedExponential, PowerSeries.coeff_mk]
    rw [show degree + 1 + 1 = degree + 2 by omega, lift_power_recurrence]
    simp only [smul_add, smul_smul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have factorial : (degree.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero degree
    have successor : (degree + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero degree
    have next : (degree + 2 : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : degree + 2 ≠ 0)
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [Algebra.smul_def]
    push_cast
    field_simp
    ring

theorem correction_gaussian (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) :
    correctedExponential D charge axes weight =
      (PowerSeries.exp (CorrectionPolynomial D)).subst
        (gaussianDriver D charge axes weight) := by
  let driver := PowerSeries.C (correctedLinear D charge axes weight) +
    PowerSeries.C (pairQuadratic D axes weight) * PowerSeries.X
  have constant : PowerSeries.constantCoeff (gaussianDriver D charge axes weight) = 0 := by
    simp [gaussianDriver]
  have derivative : PowerSeries.derivative (CorrectionPolynomial D)
      (gaussianDriver D charge axes weight) = driver := by
    dsimp [gaussianDriver, driver]
    simp only [map_add, Derivation.leibniz, PowerSeries.derivative_C,
      PowerSeries.derivative_X, zero_mul, mul_one, zero_add,
      PowerSeries.derivative_pow]
    simp only [pow_one, Algebra.smul_def]
    push_cast
    ring
  have equation : PowerSeries.derivative (CorrectionPolynomial D)
      ((PowerSeries.exp (CorrectionPolynomial D)).subst
        (gaussianDriver D charge axes weight)) =
      (PowerSeries.exp (CorrectionPolynomial D)).subst
        (gaussianDriver D charge axes weight) * driver := by
    rw [PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' constant),
      PowerSeries.derivative_exp, derivative]
  apply (originalCreationSupplier% solution_unique) _ _ driver
    (corrected_exponential_derivative D charge axes weight) equation
  rw [PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' constant), finsum_eq_single _ 0]
  · simp [correctedExponential, lift_one]
  · intro degree nonzero
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constant]
    simp [nonzero]

/- This is the coefficient form used by the native Corr field.  It is deliberately
   stated against the substituted exponential, so the later charged chart proof
   can consume the exact source coefficient without introducing a new correction
   map or an arbitrary truncation. -/
theorem correction_gaussian_coeff (D : LatticeData) (charge : Charge D)
    (axes : Finset (Index D)) (weight : Index D → ℂ) (degree : ℕ) :
    PowerSeries.coeff degree
        ((PowerSeries.exp (CorrectionPolynomial D)).subst
          (gaussianDriver D charge axes weight)) =
      (degree.factorial : ℂ)⁻¹ •
        correctionLift D charge (linearSource D axes weight ^ degree) := by
  rw [← correction_gaussian D charge axes weight]
  rfl

theorem literalCorr_creation_coefficient_gaussian
    (D : LatticeData) (charge : Charge D) (axes : Finset (Index D))
    (weight : Index D → ℂ) (degree shift : ℕ) :
    (degree.factorial : ℂ)⁻¹ •
        literalCorrCreationCoefficient D charge axes weight degree shift =
      (shiftCoefficients D)
          (optionEquivLeft ℂ (Index D)
            (PowerSeries.coeff degree
              ((PowerSeries.exp (CorrectionPolynomial D)).subst
                (gaussianDriver D charge axes weight)))) shift := by
  rw [correction_gaussian_coeff]
  simp [literalCorrCreationCoefficient, Corr, correctionPolynomial,
    correctedExponential, correctionLift, shiftCoefficients,
    LinearMap.comp_apply]

/- The bridge retains the statewise finite-support fact needed for every later
   finsum regrouping.  The premise is the exact weighted degree bound supplied
   by the source polynomial; no global cutoff is introduced. -/
theorem literalCorr_creation_coefficient_zero_of_excess_shift
    (D : LatticeData) (charge : Charge D) (axes : Finset (Index D))
    (weight : Index D → ℂ) (degree shift : ℕ)
    (excess : MvPolynomial.weightedTotalDegree (sourceWeight D)
        (linearSource D axes weight ^ degree) < shift) :
    literalCorrCreationCoefficient D charge axes weight degree shift = 0 := by
  by_contra nonzero
  have member : shift ∈
      (Corr D charge (linearSource D axes weight ^ degree)).support :=
    Finsupp.mem_support_iff.mpr nonzero
  exact (not_lt_of_ge (Corr_shift_bound D charge
    (linearSource D axes weight ^ degree) shift member)) excess

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGaussian

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGaussian.correction_gaussian

/- GID: D5/S3/VertexAlgebra/LatticeHalfFockScalarLabelledGaussian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockScalarLabelledGaussian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian recurrence of the actual finite labelled correction on source powers. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open LatticeHalfFockCorrectionTranslation
open scoped BigOperators

noncomputable section

local macro "source_mul_supplier" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
  `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.correctedSource_X_mul))

local macro "source_one_supplier" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
  `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.correctedSource_one))

local macro "pair_variable_supplier" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
  `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairDerivation_variable))

local macro "pair_singleton_supplier" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
  `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairDerivation_singleton))

def sourceDirection (D : LatticeData) (weights : Index D →₀ ℂ) : Oscillator D :=
  weights.sum (fun index scalar => scalar • X index)

def retainedLinear (D : LatticeData) (charge : Charge D) (weights : Index D →₀ ℂ) :
    CorrectionPolynomial D :=
  weights.sum (fun index scalar => scalar • (X (some index) + singletonPolynomial D charge index))

def retainedDerivation (D : LatticeData) (weights : Index D →₀ ℂ) :
    Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D) :=
  weights.sum (fun index scalar => scalar • pairDerivation D index)

def retainedPairs (D : LatticeData) (weights : Index D →₀ ℂ) : CorrectionPolynomial D :=
  weights.sum (fun first firstScalar => weights.sum (fun second secondScalar =>
    (firstScalar * secondScalar) • pairPolynomial D first second))

def retainedInsertion (D : LatticeData) (charge : Charge D) (weights : Index D →₀ ℂ) :
    Module.End ℂ (CorrectionPolynomial D) :=
  LinearMap.mulLeft ℂ (retainedLinear D charge weights) +
    (retainedDerivation D weights).toLinearMap

def correctedSourcePower (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (degree : ℕ) : CorrectionPolynomial D :=
  correctedSource D charge (sourceDirection D weights ^ degree)

private theorem retained_derivation_apply (D : LatticeData) (weights : Index D →₀ ℂ)
    (polynomial : CorrectionPolynomial D) :
    retainedDerivation D weights polynomial =
      weights.sum (fun index scalar => scalar • pairDerivation D index polynomial) := by
  classical
  have distribution := congrFun (map_sum
    (Derivation.coeFnAddMonoidHom (R := ℂ) (A := CorrectionPolynomial D)
      (M := CorrectionPolynomial D))
    (fun index => weights index • pairDerivation D index) weights.support) polynomial
  simpa only [retainedDerivation, Finsupp.sum, Derivation.coeFnAddMonoidHom_apply,
    Finset.sum_apply, Derivation.smul_apply] using distribution

private theorem insertion_sum (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (polynomial : CorrectionPolynomial D) :
    retainedInsertion D charge weights polynomial =
      weights.sum (fun index scalar => scalar • insertion D charge index polynomial) := by
  classical
  simp only [retainedInsertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, retained_derivation_apply, insertion,
    smul_add, Finsupp.sum, Finset.sum_add_distrib]
  congr 1
  simp only [retainedLinear, Finsupp.sum, Finset.sum_mul, smul_mul_assoc]

private theorem lift_direction_mul (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (polynomial : Oscillator D) :
    correctedSource D charge (sourceDirection D weights * polynomial) =
      retainedInsertion D charge weights (correctedSource D charge polynomial) := by
  classical
  simp only [sourceDirection, Finsupp.sum, Finset.sum_mul, smul_mul_assoc,
    map_sum, map_smul, source_mul_supplier, insertion_sum]

private theorem source_successor (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (degree : ℕ) :
    correctedSourcePower D charge weights (degree + 1) =
      retainedInsertion D charge weights (correctedSourcePower D charge weights degree) := by
  simp only [correctedSourcePower, pow_succ', lift_direction_mul]

private theorem derivation_linear (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) :
    retainedDerivation D weights (retainedLinear D charge weights) = retainedPairs D weights := by
  classical
  rw [retained_derivation_apply]
  simp only [retainedLinear, retainedPairs, Finsupp.sum,
    map_sum, Derivation.map_smul, map_add, pair_variable_supplier, pair_singleton_supplier,
    add_zero, Finset.smul_sum, smul_smul]

private theorem derivation_pairs (D : LatticeData) (weights : Index D →₀ ℂ) :
    retainedDerivation D weights (retainedPairs D weights) = 0 := by
  classical
  simp only [retained_derivation_apply, retainedPairs, Finsupp.sum, map_sum, Derivation.map_smul,
    pairDerivation_pair, smul_zero, Finset.sum_const_zero]

private theorem insert_pairs_mul (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (polynomial : CorrectionPolynomial D) :
    retainedInsertion D charge weights (retainedPairs D weights * polynomial) =
      retainedPairs D weights * retainedInsertion D charge weights polynomial := by
  simp only [retainedInsertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, derivation_pairs,
    zero_mul, zero_add]
  ring

private theorem derivative_insert (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (polynomial : CorrectionPolynomial D) :
    retainedDerivation D weights (retainedInsertion D charge weights polynomial) =
      retainedPairs D weights * polynomial + retainedInsertion D charge weights
        (retainedDerivation D weights polynomial) := by
  simp only [retainedInsertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, Derivation.leibniz, smul_eq_mul, derivation_linear]
  ring

private theorem derivative_source_power (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (degree : ℕ) :
    retainedDerivation D weights (correctedSourcePower D charge weights (degree + 1)) =
      (degree + 1 : ℂ) • (retainedPairs D weights * correctedSourcePower D charge weights degree) := by
  induction degree with
  | zero =>
    rw [source_successor]
    simp only [correctedSourcePower, pow_zero, source_one_supplier, retainedInsertion,
      LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
      Derivation.map_one_eq_zero, mul_one, add_zero, derivation_linear]
    norm_num
  | succ degree inductionProof =>
    rw [source_successor, derivative_insert, inductionProof, map_smul,
      insert_pairs_mul, ← source_successor]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    module

private theorem actual_retained_gaussian_recurrence (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (degree : ℕ) :
    correctedSourcePower D charge weights (degree + 2) =
      retainedLinear D charge weights * correctedSourcePower D charge weights (degree + 1) +
        (degree + 1 : ℂ) •
          (retainedPairs D weights * correctedSourcePower D charge weights degree) := by
  rw [show degree + 2 = (degree + 1) + 1 by omega, source_successor]
  simp only [retainedInsertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, derivative_source_power]

def retainedGaussianLog (D : LatticeData) (charge : Charge D) (weights : Index D →₀ ℂ) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.C (retainedLinear D charge weights) * PowerSeries.X +
    PowerSeries.C ((1 / 2 : ℂ) • retainedPairs D weights) * PowerSeries.X ^ 2

def retainedGaussian (D : LatticeData) (charge : Charge D) (weights : Index D →₀ ℂ) :
    PowerSeries (CorrectionPolynomial D) :=
  (PowerSeries.exp (CorrectionPolynomial D)).subst (retainedGaussianLog D charge weights)

private theorem gaussian_log_zero (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) :
    PowerSeries.constantCoeff (retainedGaussianLog D charge weights) = 0 := by
  simp only [retainedGaussianLog, map_add, map_mul, map_pow,
    PowerSeries.constantCoeff_X, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]

private theorem gaussian_substitution (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) :
    PowerSeries.HasSubst (retainedGaussianLog D charge weights) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  exact gaussian_log_zero D charge weights

private theorem gaussian_derivative (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) :
    PowerSeries.derivative (CorrectionPolynomial D) (retainedGaussian D charge weights) =
      (PowerSeries.C (retainedLinear D charge weights) +
        PowerSeries.C (retainedPairs D weights) * PowerSeries.X) *
          retainedGaussian D charge weights := by
  have logarithm : PowerSeries.derivative (CorrectionPolynomial D)
      (retainedGaussianLog D charge weights) =
        PowerSeries.C (retainedLinear D charge weights) +
          PowerSeries.C (retainedPairs D weights) * PowerSeries.X := by
    have doubled : (2 : ℕ) • ((1 / 2 : ℂ) • retainedPairs D weights) =
        retainedPairs D weights := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      norm_num
    have doubledConstant : (2 : PowerSeries (CorrectionPolynomial D)) *
        PowerSeries.C ((1 / 2 : ℂ) • retainedPairs D weights) =
          PowerSeries.C (retainedPairs D weights) := by
      rw [two_mul, ← map_add]
      congr 1
      rw [← two_smul ℕ, doubled]
    simp only [retainedGaussianLog, map_add, Derivation.leibniz, PowerSeries.derivative_C,
      PowerSeries.derivative_X, PowerSeries.derivative_pow, smul_eq_mul,
      zero_mul, mul_zero, add_zero, mul_one]
    norm_num only [Nat.reduceSub, pow_one]
    rw [← mul_assoc, mul_comm (PowerSeries.C _) (2 : PowerSeries (CorrectionPolynomial D)),
      doubledConstant]
  rw [retainedGaussian, PowerSeries.derivative_subst (gaussian_substitution D charge weights),
    PowerSeries.derivative_exp, logarithm, mul_comm]

private theorem gaussian_initial (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) :
    PowerSeries.coeff 0 (retainedGaussian D charge weights) = 1 := by
  rw [retainedGaussian, PowerSeries.coeff_subst' (gaussian_substitution D charge weights),
    finsum_eq_single _ 0]
  · simp
  · intro degree nonzero
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      gaussian_log_zero, zero_pow nonzero, smul_zero]

private theorem gaussian_first (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) :
    PowerSeries.coeff 1 (retainedGaussian D charge weights) = retainedLinear D charge weights := by
  have coefficient := congrArg (PowerSeries.coeff 0) (gaussian_derivative D charge weights)
  rw [PowerSeries.coeff_derivative, add_mul, map_add, PowerSeries.coeff_C_mul,
    mul_assoc, PowerSeries.coeff_C_mul] at coefficient
  simpa [gaussian_initial, mul_comm (PowerSeries.X : PowerSeries (CorrectionPolynomial D)),
    PowerSeries.coeff_mul_X_pow'] using coefficient

private theorem gaussian_factorial_recurrence (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (degree : ℕ) :
    ((degree + 2).factorial : ℕ) •
        PowerSeries.coeff (degree + 2) (retainedGaussian D charge weights) =
      retainedLinear D charge weights * ((degree + 1).factorial •
        PowerSeries.coeff (degree + 1) (retainedGaussian D charge weights)) +
      (degree + 1 : ℂ) • (retainedPairs D weights * (degree.factorial •
        PowerSeries.coeff degree (retainedGaussian D charge weights))) := by
  have coefficient := congrArg (PowerSeries.coeff (degree + 1))
    (gaussian_derivative D charge weights)
  rw [PowerSeries.coeff_derivative, add_mul, map_add, PowerSeries.coeff_C_mul,
    mul_assoc, PowerSeries.coeff_C_mul] at coefficient
  have shifted : PowerSeries.coeff (degree + 1)
      (PowerSeries.X * retainedGaussian D charge weights) =
        PowerSeries.coeff degree (retainedGaussian D charge weights) := by
    rw [mul_comm, ← pow_one (PowerSeries.X : PowerSeries (CorrectionPolynomial D)),
      PowerSeries.coeff_mul_X_pow]
  rw [shifted, ← Nat.cast_succ, mul_comm _ ((degree + 1 + 1 : ℕ) : CorrectionPolynomial D),
    ← nsmul_eq_mul] at coefficient
  have scaled := congrArg (fun polynomial : CorrectionPolynomial D =>
    (degree + 1).factorial • polynomial) coefficient
  rw [← Nat.cast_succ]
  simpa only [show degree + 1 + 1 = degree + 2 by omega,
    Nat.factorial_succ, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm,
    Nat.cast_smul_eq_nsmul, Nat.mul_comm] using scaled

private theorem actual_retained_gaussian_closed (D : LatticeData) (charge : Charge D)
    (weights : Index D →₀ ℂ) (degree : ℕ) :
    correctedSourcePower D charge weights degree =
      degree.factorial • PowerSeries.coeff degree (retainedGaussian D charge weights) := by
  induction degree using Nat.strong_induction_on with
  | h degree inductionProof =>
    rcases degree with _ | _ | degree
    · simp [correctedSourcePower, source_one_supplier, gaussian_initial]
    · rw [show 1 = 0 + 1 by omega, source_successor]
      simp [correctedSourcePower, source_one_supplier, retainedInsertion, gaussian_first]
    · rw [actual_retained_gaussian_recurrence,
        inductionProof (degree + 1) (by omega), inductionProof degree (by omega)]
      exact (gaussian_factorial_recurrence D charge weights degree).symm

def nativeCorrectionEvaluation (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    CorrectionPolynomial D →ₗ[ℂ] LatticeHalfFockFockNormalField.NativeField D hu :=
  ((Finsupp.lsum ℂ (fun shift : ℕ =>
    (LatticeHalfFockFockNormalField.shiftLinear D hu shift).comp
      (LatticeHalfFockFockNormalField.normalPolynomial D hu charge))).comp
        (shiftCoefficients D)).comp (optionEquivLeft ℂ (Index D)).toLinearMap

private theorem native_correction_source (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    nativeCorrectionEvaluation D hu charge (correctedSource D charge polynomial) =
      LatticeHalfFockAllStateField.Ytw D hu (Finsupp.single charge polynomial) := by
  simp only [nativeCorrectionEvaluation, correctedSource, LatticeHalfFockAllStateField.Ytw,
    Finsupp.lsum_single, LatticeHalfFockAllStateField.correctedPolynomial, Corr,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]

theorem actual_source_field_gaussian_closed (object : LatticeHalfFockOriginalTwoSheetChartRecurrence.NativeLattice)
    (charge : Charge object.lattice) (weights : Index object.lattice →₀ ℂ) (degree : ℕ) :
    LatticeHalfFockAllStateField.Ytw object.lattice object.native
        (Finsupp.single charge (sourceDirection object.lattice weights ^ degree)) =
      degree.factorial • nativeCorrectionEvaluation object.lattice object.native charge
        (PowerSeries.coeff degree (retainedGaussian object.lattice charge weights)) := by
  have identity := congrArg (nativeCorrectionEvaluation object.lattice object.native charge)
    (actual_retained_gaussian_closed object.lattice charge weights degree)
  simpa only [correctedSourcePower, native_correction_source, map_nsmul] using identity

#print axioms actual_retained_gaussian_recurrence
#print axioms actual_retained_gaussian_closed
#print axioms actual_source_field_gaussian_closed

end

end D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian

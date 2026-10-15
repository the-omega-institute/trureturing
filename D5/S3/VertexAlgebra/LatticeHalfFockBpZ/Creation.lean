/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Creation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Creation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native odd-weight exponential coefficients obey the exact half-current derivative. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Oscillator
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeActualAnnihilation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeActualAnnihilation ActualSeriesDerivation MvPolynomial
open scoped BigOperators

noncomputable section

private theorem half_exponential_derivative (D : LatticeData) (charge : Charge D) :
    PowerSeries.derivative (Oscillator D) (halfCreationExponential D charge) =
      halfCreationExponential D charge *
        PowerSeries.derivative (Oscillator D) (halfCreationSeries D charge) := by
  exact exponential_derivative D charge

theorem half_exponential_derivation (D : LatticeData)
    (derivation : Derivation ℂ (Oscillator D) (Oscillator D)) (charge : Charge D) :
    seriesDerivation D derivation (halfCreationExponential D charge) =
      halfCreationExponential D charge *
        seriesDerivation D derivation (halfCreationSeries D charge) := by
  let exponential := halfCreationExponential D charge
  let logarithm := halfCreationSeries D charge
  let derivative := PowerSeries.derivative (Oscillator D) logarithm
  let residual := seriesDerivation D derivation exponential -
    exponential * seriesDerivation D derivation logarithm
  have differential : PowerSeries.derivative (Oscillator D) exponential =
      exponential * derivative := half_exponential_derivative D charge
  have residualDifferential : PowerSeries.derivative (Oscillator D) residual =
      residual * derivative := by
    dsimp only [residual]
    rw [map_sub, ← derivative_commute, differential,
      (seriesDerivation D derivation).leibniz,
      (PowerSeries.derivative (Oscillator D)).leibniz, differential,
      ← derivative_commute]
    simp only [smul_eq_mul]
    ring
  have initial : PowerSeries.coeff 0 residual = 0 := by
    dsimp only [residual]
    rw [map_sub, series_coeff, exponential_constant, Derivation.map_one_eq_zero,
      PowerSeries.coeff_mul]
    simp [logarithm, halfCreationSeries, series_coeff]
  have vanishes : residual = 0 := by
    apply PowerSeries.ext
    intro degree
    rw [map_zero]
    induction degree using Nat.strong_induction_on with
    | h degree previous =>
      cases degree with
      | zero => exact initial
      | succ degree =>
        have recurrence := congrArg (PowerSeries.coeff degree) residualDifferential
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at recurrence
        have sumZero : (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
            PowerSeries.coeff pair.1 residual * PowerSeries.coeff pair.2 derivative) = 0 := by
          apply Finset.sum_eq_zero
          intro pair membership
          have total := Finset.HasAntidiagonal.mem_antidiagonal.mp membership
          rw [previous pair.1 (by omega), zero_mul]
        rw [sumZero] at recurrence
        have cancelled : (degree + 1) • PowerSeries.coeff (degree + 1) residual =
            (degree + 1) • (0 : Oscillator D) := by
          simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm,
            mul_zero, zero_mul] using recurrence
        exact (smul_right_inj (Nat.succ_ne_zero degree)).mp cancelled
  exact sub_eq_zero.mp vanishes

theorem half_annihilation_logarithm (D : LatticeData) (axis : Fin D.rank)
    (mode : ℕ) (charge : Charge D) :
    seriesDerivation D (annihilationDerivation D axis mode) (halfCreationSeries D charge) =
      PowerSeries.C (((2 / (omega D (axis, mode) : ℂ)) *
        (bilinear D (unitCharge D axis) charge : ℂ)) • (1 : Oscillator D)) *
          PowerSeries.X ^ omega D (axis, mode) := by
  classical
  apply PowerSeries.ext
  intro degree
  simp only [series_coeff, halfCreationSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases odd : degree % 2 = 1
  · rw [if_pos odd, Derivation.map_smul, map_sum]
    simp only [Derivation.map_smul, annihilation_apply, annihilate_X]
    by_cases equalMode : mode = degree / 2
    · have degreeEquation : degree = omega D (axis, mode) := by
        dsimp [omega]
        omega
      subst degree
      simp only [omega, show (2 * mode + 1) / 2 = mode by omega, if_true,
        smul_smul, ← Finset.sum_smul, pairing_sum]
    · have degreeEquation : degree ≠ omega D (axis, mode) := by
        dsimp [omega]
        omega
      simp [equalMode, degreeEquation]
  · rw [if_neg odd, map_zero]
    have degreeEquation : degree ≠ omega D (axis, mode) := by
      dsimp [omega]
      omega
    simp [degreeEquation]

theorem half_annihilation_creation (D : LatticeData) (axis : Fin D.rank)
    (mode : ℕ) (charge : Charge D) (degree : ℤ) :
    annihilate D axis mode (halfCreationCoeff D charge degree) =
      ((2 / (omega D (axis, mode) : ℂ)) *
        (bilinear D (unitCharge D axis) charge : ℂ)) •
          halfCreationCoeff D charge (degree - (omega D (axis, mode) : ℕ)) := by
  by_cases negative : degree < 0
  · simp [halfCreationCoeff, negative,
      show degree - (omega D (axis, mode) : ℕ) < 0 by omega]
  · have coefficient := congrArg (PowerSeries.coeff degree.toNat)
      (half_exponential_derivation D (annihilationDerivation D axis mode) charge)
    rw [series_coeff, annihilation_apply, half_annihilation_logarithm, ← mul_assoc,
      PowerSeries.coeff_mul_X_pow'] at coefficient
    rw [halfCreationCoeff, if_neg negative, coefficient]
    by_cases enough : omega D (axis, mode) ≤ degree.toNat
    · rw [if_pos enough, halfCreationCoeff, if_neg (by omega),
        show (degree - (omega D (axis, mode) : ℕ)).toNat =
          degree.toNat - omega D (axis, mode) by omega,
        PowerSeries.coeff_mul_C, mul_smul_comm, mul_one]
    · rw [if_neg enough, halfCreationCoeff, if_pos (by omega), smul_zero]

theorem half_current_creation (D : LatticeData) (index : Index D)
    (charge : Charge D) (degree : ℤ) :
    LatticeHalfFock.current D index.1 (index.2 : ℤ) (halfCreationCoeff D charge degree) =
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        halfCreationCoeff D charge (degree - (omega D index : ℕ)) := by
  change ((index.2 : ℂ) + 1 / 2) •
    annihilate D index.1 index.2 (halfCreationCoeff D charge degree) = _
  rw [half_annihilation_creation, smul_smul]
  congr 1
  have nonzero : (2 * (index.2 : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * (index.2 : ℝ) + 1))
  dsimp [omega]
  push_cast
  rw [← mul_assoc]
  have factor : ((index.2 : ℂ) + 1 / 2) * (2 / (2 * (index.2 : ℂ) + 1)) = 1 := by
    rw [← mul_div_assoc,
      show ((index.2 : ℂ) + 1 / 2) * 2 = 2 * (index.2 : ℂ) + 1 by ring,
      div_self nonzero]
  rw [factor, one_mul]

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ

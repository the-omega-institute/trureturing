import D5.S3.VertexAlgebra.ChargedNormalPolynomialFactorsTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.ChargedTwoSheetFactorsTransient

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open LatticeHalfFockFormalTwoSheetSubstitution ChargedNormalJetComparisonTransient
open ChargedCreationExponentialTransient ChargedNormalPolynomialFactorsTransient
open scoped BigOperators

noncomputable section

private theorem sheet_parameter_zero (D : LatticeData) :
    PowerSeries.constantCoeff
      (PowerSeries.map (C : ℂ →+* Oscillator D) twoSheetSeries) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff]
  simp [twoSheetSeries]

def oscillatorSheet (D : LatticeData) :
    PowerSeries (Oscillator D) →+* PowerSeries (Oscillator D) :=
  (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero'
    (sheet_parameter_zero D))).toRingHom

def creationSheetShiftHom (D : LatticeData) :
    PowerSeries (Oscillator D) →+* ShiftRing D :=
  (creationShiftHom D).comp (oscillatorSheet D)

def onSheetCreator (D : LatticeData) (charge : Charge D) :
    PowerSeries (ShiftRing D) :=
  PowerSeries.map (creationSheetShiftHom D) (originalCreationExpLift D charge)

def onSheetJet (D : LatticeData) (charge : Charge D) :
    PowerSeries (ShiftRing D) :=
  PowerSeries.map (creationSheetShiftHom D) (originalCreationJetLog D charge)

local macro "scalar_sheet_apply_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
    `D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution.sheet_substitution_apply))

local macro "formal_exp_map_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.ChargedNormalPolynomialFactorsTransient
    `D5.S3.VertexAlgebra.ChargedNormalPolynomialFactorsTransient.formal_exp_map))

theorem actual_creation_root_on_sheet (D : LatticeData) :
    creationSheetShiftHom D (originalCreationRoot D) =
      PowerSeries.rescale (X none : CorrectionPolynomial D)
        (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) (twoSheetLabel 1)) := by
  have zero : PowerSeries.constantCoeff twoSheetSeries = 0 := by simp [twoSheetSeries]
  have mapped := PowerSeries.map_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' zero)
    (h := (C : ℂ →+* Oscillator D)) (halfLabel 1)
  have rootIdentity : oscillatorSheet D (originalCreationRoot D) =
      PowerSeries.map (C : ℂ →+* Oscillator D) (twoSheetLabel 1) := by
    calc
      _ = (PowerSeries.map (C : ℂ →+* Oscillator D) (halfLabel 1)).subst
          (PowerSeries.map (C : ℂ →+* Oscillator D) twoSheetSeries) := by
        exact congrFun (PowerSeries.coe_substAlgHom _) (originalCreationRoot D)
      _ = PowerSeries.map (C : ℂ →+* Oscillator D)
          ((halfLabel 1).subst twoSheetSeries) := mapped.symm
      _ = PowerSeries.map (C : ℂ →+* Oscillator D) (twoSheetLabel 1) := by
        rw [← scalar_sheet_apply_supplier, original_half_integer_all_label_two_sheet]
  rw [creationSheetShiftHom, RingHom.comp_apply, rootIdentity]
  apply PowerSeries.ext
  intro degree
  simp only [creationShiftHom, RingHom.comp_apply, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map]
  change X none ^ degree *
    MvPolynomial.rename some (C (PowerSeries.coeff degree (twoSheetLabel 1))) = _
  rw [MvPolynomial.rename_C]

theorem actual_creation_two_sheet_factorization (D : LatticeData)
    (first second : Charge D) :
    PowerSeries.rescale
        (PowerSeries.rescale (X none : CorrectionPolynomial D)
          (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) (twoSheetLabel 1)))
        (onSheetCreator D first) * onSheetCreator D second =
      onSheetCreator D (first + second) * formalExp (onSheetJet D first) := by
  have identity := congrArg (PowerSeries.map (creationSheetShiftHom D))
    (actual_creation_exponential_factorization D first second)
  rw [map_mul, map_mul,
    ← PowerSeries.rescale_map (creationSheetShiftHom D) (originalCreationRoot D),
    actual_creation_root_on_sheet,
    formal_exp_map_supplier (creationSheetShiftHom D) _
      (by simp [originalCreationJetLog, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])] at identity
  exact identity

theorem actual_creation_two_sheet_finite_joint_coefficients (D : LatticeData)
    (first second : Charge D) (energy order : ℕ) :
    PowerSeries.coeff order (PowerSeries.coeff energy
      (PowerSeries.rescale
        (PowerSeries.rescale (X none : CorrectionPolynomial D)
          (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) (twoSheetLabel 1)))
        (onSheetCreator D first) * onSheetCreator D second)) =
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal energy,
        ∑ exponent ∈ Finset.range (pair.2 + 1),
          PowerSeries.coeff order
            (PowerSeries.coeff pair.1 (onSheetCreator D (first + second)) *
              (algebraMap ℚ (ShiftRing D) (1 / exponent.factorial) *
                PowerSeries.coeff pair.2 (onSheetJet D first ^ exponent))) := by
  have zero : PowerSeries.constantCoeff (onSheetJet D first) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, onSheetJet,
      PowerSeries.coeff_map]
    have sourceZero : PowerSeries.coeff 0 (originalCreationJetLog D first) = 0 := by
      simp [originalCreationJetLog]
    rw [sourceZero, map_zero]
  rw [actual_creation_two_sheet_factorization, PowerSeries.coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro pair member
  rw [formal_exp_finite_coefficient _ zero, Finset.mul_sum, map_sum]

#print axioms actual_creation_root_on_sheet
#print axioms actual_creation_two_sheet_factorization
#print axioms actual_creation_two_sheet_finite_joint_coefficients

end

end D5.S3.VertexAlgebra.ChargedTwoSheetFactorsTransient

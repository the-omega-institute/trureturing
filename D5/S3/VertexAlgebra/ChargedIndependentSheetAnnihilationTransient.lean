import D5.S3.VertexAlgebra.ChargedTwoSheetFactorsTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.ChargedIndependentSheetAnnihilationTransient

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open LatticeHalfFockFormalTwoSheetSubstitution ChargedNormalJetComparisonTransient
open ChargedNormalPolynomialFactorsTransient
open scoped BigOperators

noncomputable section

def independentSheetParameter (D : LatticeData) : ShiftRing D :=
  PowerSeries.mk fun degree => if degree = 0 then 0 else
    C (PowerSeries.coeff degree twoSheetSeries) * (X none : CorrectionPolynomial D) ^ (degree - 1)

private theorem independent_sheet_parameter_zero (D : LatticeData) :
    PowerSeries.constantCoeff (independentSheetParameter D) = 0 := by
  simp [independentSheetParameter, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem actual_independent_sheet_parameter (D : LatticeData) :
    (X none : CorrectionPolynomial D) • independentSheetParameter D =
      PowerSeries.rescale (X none : CorrectionPolynomial D)
        (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) twoSheetSeries) := by
  apply PowerSeries.ext
  intro degree
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, map_smul,
    independentSheetParameter, PowerSeries.coeff_mk]
  cases degree with
  | zero => simp [twoSheetSeries, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ degree =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one, smul_eq_mul,
      pow_succ]
    ring

def independentSheetSubstitution (D : LatticeData) : ShiftRing D →+* ShiftRing D :=
  (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero'
    (independent_sheet_parameter_zero D))).toRingHom

local macro "scalar_sheet_apply_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
    `D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution.sheet_substitution_apply))

theorem actual_independent_rescale_sheet (D : LatticeData) (series : PowerSeries ℂ) :
    independentSheetSubstitution D
        (PowerSeries.rescale (X none : CorrectionPolynomial D)
          (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series)) =
      PowerSeries.rescale (X none : CorrectionPolynomial D)
        (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) (sheetSubstitution series)) := by
  have parameterZero : PowerSeries.constantCoeff
      (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) twoSheetSeries) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff]
    simp [twoSheetSeries]
  have zero : PowerSeries.constantCoeff twoSheetSeries = 0 := by simp [twoSheetSeries]
  have first := PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.smul_X' (R := CorrectionPolynomial D)
      (X none : CorrectionPolynomial D))
    (PowerSeries.HasSubst.of_constantCoeff_zero' (independent_sheet_parameter_zero D))
    (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series)
  have hasParameter := PowerSeries.HasSubst.of_constantCoeff_zero'
    (independent_sheet_parameter_zero D)
  rw [PowerSeries.subst_smul hasParameter, PowerSeries.subst_X hasParameter,
    actual_independent_sheet_parameter] at first
  have second := PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' parameterZero)
    (PowerSeries.HasSubst.smul_X' (R := CorrectionPolynomial D)
      (X none : CorrectionPolynomial D))
    (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series)
  have mapped := PowerSeries.map_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' zero)
    (h := (C : ℂ →+* CorrectionPolynomial D)) series
  calc
    _ = PowerSeries.subst (independentSheetParameter D)
        (PowerSeries.rescale (X none : CorrectionPolynomial D)
          (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series)) := by
      exact congrFun (PowerSeries.coe_substAlgHom _) _
    _ = (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series).subst
        (PowerSeries.rescale (X none : CorrectionPolynomial D)
          (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) twoSheetSeries)) := by
      simpa only [PowerSeries.rescale_eq_subst] using first
    _ = PowerSeries.rescale (X none : CorrectionPolynomial D)
        ((PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series).subst
          (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) twoSheetSeries)) := by
      simpa only [PowerSeries.rescale_eq_subst] using second.symm
    _ = _ := by
      rw [scalar_sheet_apply_supplier]
      exact congrArg (PowerSeries.rescale (X none : CorrectionPolynomial D)) mapped.symm

def annihilationTwoSheetEvaluation (D : LatticeData) :
    PairPolynomial D →+* Polynomial (ShiftRing D) :=
  (Polynomial.mapRingHom (independentSheetSubstitution D)).comp (annihilationSheetEvaluation D)

def annihilationTwoSheetNormalEvaluation (D : LatticeData)
    (first second : Charge D) : Oscillator D →+* Polynomial (ShiftRing D) :=
  (Polynomial.mapRingHom (independentSheetSubstitution D)).comp
    (annihilationNormalEvaluation D first second)

theorem actual_annihilation_two_sheet_all_polynomials (D : LatticeData)
    (first second : Charge D) (polynomial : Oscillator D) :
    annihilationTwoSheetEvaluation D
        (LatticeHalfFockProductKernel.pairTranslation D first second polynomial) =
      annihilationTwoSheetNormalEvaluation D first second polynomial := by
  exact congrArg (Polynomial.mapRingHom (independentSheetSubstitution D))
    (actual_annihilation_all_polynomials D first second polynomial)

theorem actual_annihilation_two_sheet_normal_variable (D : LatticeData)
    (first second : Charge D) (index : Index D) :
    annihilationTwoSheetNormalEvaluation D first second (X index) =
      oscillatorToAnnihilation D (X index) -
        oscillatorToAnnihilation D
          ((LatticeGeneratingFieldLocality.bilinear D (first + second)
            (LatticeGeneratingFieldLocality.unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
            Polynomial.X ^ LatticeHalfFockChargedCoefficients.omega D index +
        Polynomial.C
          (PowerSeries.C
            (C ((LatticeGeneratingFieldLocality.bilinear D first
              (LatticeGeneratingFieldLocality.unitCharge D index.1) : ℂ) *
                ((index.2 : ℂ) + 1 / 2))) *
              PowerSeries.rescale (X none : CorrectionPolynomial D)
                (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D)
                  (sheetSubstitution (integratedJet (index.2 : ℤ))))) *
          Polynomial.X ^ LatticeHalfFockChargedCoefficients.omega D index := by
  simp only [annihilationTwoSheetNormalEvaluation, RingHom.comp_apply,
    annihilationNormalEvaluation, MvPolynomial.eval₂Hom_X', annihilationNormalVariable,
    map_add, map_sub, map_mul, map_pow, Polynomial.coe_mapRingHom,
    Polynomial.map_C, Polynomial.map_X]
  have constant (scalar : CorrectionPolynomial D) :
      independentSheetSubstitution D (PowerSeries.C scalar) = PowerSeries.C scalar := by
    exact (congrFun (PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        (independent_sheet_parameter_zero D))) (PowerSeries.C scalar)).trans
      (PowerSeries.subst_C scalar)
  simp only [oscillatorToAnnihilation, RingHom.comp_apply, Polynomial.map_C, constant,
    shiftedJet, actual_independent_rescale_sheet]

#print axioms actual_independent_sheet_parameter
#print axioms actual_independent_rescale_sheet
#print axioms actual_annihilation_two_sheet_all_polynomials
#print axioms actual_annihilation_two_sheet_normal_variable

end

end D5.S3.VertexAlgebra.ChargedIndependentSheetAnnihilationTransient

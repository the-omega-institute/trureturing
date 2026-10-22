import D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.ChargedNormalJetComparisonTransient

open LatticeHalfFockFockNormalField LatticeHalfFockFormalTwoSheetSubstitution
open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open scoped BigOperators

noncomputable section

def integratedJet (mode : ℤ) : PowerSeries ℂ :=
  PowerSeries.mk fun degree =>
    if degree = 0 then 0 else jetScalar (degree - 1) mode / (degree : ℂ)

private theorem jet_binomial (order : ℕ) (mode : ℤ) :
    jetScalar order mode = Ring.choose (-(mode : ℂ) - 3 / 2) order := by
  have evaluation :
      (descPochhammer ℤ order).smeval (-(mode : ℂ) - 3 / 2) =
        ∏ offset ∈ Finset.range order, (-(mode : ℂ) - 3 / 2 - (offset : ℂ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    have hom : (RingHom.smulOneHom : ℤ →+* ℂ) = Int.castRingHom ℂ := by
      ext scalar
      simp [RingHom.smulOneHom_apply, zsmul_eq_mul]
    rw [hom, ← Polynomial.eval_map, descPochhammer_map,
      descPochhammer_eval_eq_prod_range]
  rw [Ring.choose_eq_smul, smul_eq_mul, evaluation]
  unfold jetScalar
  ring

private theorem binomial_primitive (scalar : ℂ) (order : ℕ) :
    scalar * (Ring.choose (scalar - 1) order / (order + 1 : ℂ)) =
      Ring.choose scalar (order + 1) := by
  have nonzero : (order + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero order
  have factorial : (order.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero order
  have evaluation : (descPochhammer ℤ (order + 1)).smeval scalar =
      scalar * (descPochhammer ℤ order).smeval (scalar - 1) := by
    rw [descPochhammer_succ_left, Polynomial.smeval_mul, Polynomial.smeval_X,
      pow_one, Polynomial.smeval_comp, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_one, pow_zero, one_smul]
    simp only [pow_one]
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, smul_eq_mul, smul_eq_mul,
    evaluation, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

theorem integrated_jet_all_modes (mode : ℤ) :
    PowerSeries.C (-(mode : ℂ) - 1 / 2) * integratedJet mode =
      halfLabel (-(2 * mode + 1)) - 1 := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
    rw [PowerSeries.coeff_C_mul]
    simp [integratedJet, halfLabel]
  | succ order =>
    rw [PowerSeries.coeff_C_mul]
    simp only [integratedJet, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one, map_sub,
      PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, sub_zero,
      halfLabel, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
    rw [jet_binomial]
    have exponent : ((-(2 * mode + 1) : ℤ) : ℂ) / 2 =
        -(mode : ℂ) - 1 / 2 := by push_cast; ring
    rw [exponent]
    have parameter : -(mode : ℂ) - 3 / 2 = (-(mode : ℂ) - 1 / 2) - 1 := by ring
    rw [parameter]
    simpa only [Nat.cast_add, Nat.cast_one] using
      binomial_primitive (-(mode : ℂ) - 1 / 2) order

def shiftedJet (D : LatticeData) (mode : ℤ) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.rescale (X none : CorrectionPolynomial D)
    (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) (integratedJet mode))

def shiftedLabel (D : LatticeData) (label : ℤ) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.rescale (X none : CorrectionPolynomial D)
    (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) (halfLabel label))

private theorem rescale_constant (D : LatticeData) (scalar : CorrectionPolynomial D) :
    PowerSeries.rescale (X none : CorrectionPolynomial D) (PowerSeries.C scalar) =
      PowerSeries.C scalar := by
  apply PowerSeries.ext
  intro degree
  rw [PowerSeries.coeff_rescale]
  by_cases zero : degree = 0 <;> simp [PowerSeries.coeff_C, zero]

theorem independent_shift_jet_all_modes (D : LatticeData) (mode : ℤ) :
    PowerSeries.C (C (-(mode : ℂ) - 1 / 2)) * shiftedJet D mode =
      shiftedLabel D (-(2 * mode + 1)) - 1 := by
  have identity := congrArg
    (fun series : PowerSeries ℂ => PowerSeries.rescale (X none : CorrectionPolynomial D)
      (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series))
    (integrated_jet_all_modes mode)
  rw [map_mul, PowerSeries.map_C, map_mul, rescale_constant] at identity
  simpa only [map_sub, map_one, shiftedJet, shiftedLabel] using identity

theorem integrated_jet_two_sheet (mode : ℤ) :
    PowerSeries.C (-(mode : ℂ) - 1 / 2) * sheetSubstitution (integratedJet mode) =
      twoSheetLabel (-(2 * mode + 1)) - 1 := by
  have scalar : sheetSubstitution (PowerSeries.C (-(mode : ℂ) - 1 / 2)) =
      PowerSeries.C (-(mode : ℂ) - 1 / 2) :=
    sheetSubstitution.commutes (-(mode : ℂ) - 1 / 2)
  calc
    PowerSeries.C (-(mode : ℂ) - 1 / 2) * sheetSubstitution (integratedJet mode) =
        sheetSubstitution (PowerSeries.C (-(mode : ℂ) - 1 / 2) * integratedJet mode) := by
      rw [map_mul, scalar]
    _ = sheetSubstitution (halfLabel (-(2 * mode + 1)) - 1) :=
      congrArg sheetSubstitution (integrated_jet_all_modes mode)
    _ = twoSheetLabel (-(2 * mode + 1)) - 1 := by
      simpa only [map_one, original_half_integer_all_label_two_sheet] using
        (map_sub sheetSubstitution (halfLabel (-(2 * mode + 1))) 1)

private theorem half_label_nat_power (label : ℤ) (degree : ℕ) :
    halfLabel label ^ degree = halfLabel ((degree : ℤ) * label) := by
  induction degree with
  | zero => simp [halfLabel]
  | succ degree inductionProof =>
    rw [pow_succ, inductionProof]
    unfold halfLabel
    rw [← PowerSeries.binomialSeries_add]
    congr 1
    push_cast
    ring

def originalCreationLogLift (D : LatticeData) (charge : Charge D) :
    PowerSeries (PowerSeries (Oscillator D)) :=
  PowerSeries.map (PowerSeries.C : Oscillator D →+* PowerSeries (Oscillator D))
    (LatticeHalfFockChargedCoefficients.halfCreationSeries D charge)

def originalCreationRoot (D : LatticeData) : PowerSeries (Oscillator D) :=
  PowerSeries.map (C : ℂ →+* Oscillator D) (halfLabel 1)

def originalCreationDifference (D : LatticeData) (charge : Charge D) :
    PowerSeries (PowerSeries (Oscillator D)) :=
  PowerSeries.rescale (originalCreationRoot D) (originalCreationLogLift D charge) -
    originalCreationLogLift D charge

def originalCreationJetLog (D : LatticeData) (charge : Charge D) :
    PowerSeries (PowerSeries (Oscillator D)) :=
  PowerSeries.mk fun degree =>
    if degree % 2 = 1 then
      PowerSeries.C (∑ colour : Fin D.rank,
        (charge colour : ℂ) • (X (colour, degree / 2) : Oscillator D)) *
        PowerSeries.map (C : ℂ →+* Oscillator D)
          (integratedJet (-((degree / 2 : ℕ) : ℤ) - 1))
    else 0

theorem actual_creation_log_all_labels (D : LatticeData) (charge : Charge D) :
    originalCreationDifference D charge = originalCreationJetLog D charge := by
  apply PowerSeries.ext
  intro degree
  rw [originalCreationDifference, map_sub, PowerSeries.coeff_rescale,
    originalCreationLogLift, PowerSeries.coeff_map, originalCreationJetLog,
    PowerSeries.coeff_mk]
  unfold LatticeHalfFockChargedCoefficients.halfCreationSeries
  rw [PowerSeries.coeff_mk]
  by_cases odd : degree % 2 = 1
  · rw [if_pos odd, if_pos odd]
    have degreeIdentity : degree = 2 * (degree / 2) + 1 := by omega
    have degreeNonzero : (degree : ℂ) ≠ 0 := by
      exact_mod_cast (show degree ≠ 0 by omega)
    have labelIdentity : -(2 * (-((degree / 2 : ℕ) : ℤ) - 1) + 1) =
        (degree : ℤ) := by omega
    have scalarIdentity :
        -(((-((degree / 2 : ℕ) : ℤ) - 1) : ℤ) : ℂ) - 1 / 2 =
          (degree : ℂ) / 2 := by
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
      have castDegree : (degree : ℂ) = 2 * ((degree / 2 : ℕ) : ℂ) + 1 := by
        exact_mod_cast degreeIdentity
      rw [castDegree]
      ring
    have jetIdentity := congrArg (PowerSeries.map (C : ℂ →+* Oscillator D))
      (integrated_jet_all_modes (-((degree / 2 : ℕ) : ℤ) - 1))
    rw [map_mul, PowerSeries.map_C, labelIdentity, scalarIdentity] at jetIdentity
    have rootPower : originalCreationRoot D ^ degree =
        PowerSeries.map (C : ℂ →+* Oscillator D) (halfLabel (degree : ℤ)) := by
      rw [originalCreationRoot, ← map_pow, half_label_nat_power, mul_one]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, rootPower]
    let scalarSeries : PowerSeries (Oscillator D) := PowerSeries.C (C (2 / (degree : ℂ)))
    let polynomialSeries : PowerSeries (Oscillator D) := PowerSeries.C
      (∑ colour : Fin D.rank, (charge colour : ℂ) • (X (colour, degree / 2) : Oscillator D))
    let jetSeries : PowerSeries (Oscillator D) :=
      PowerSeries.map (C : ℂ →+* Oscillator D)
        (integratedJet (-((degree / 2 : ℕ) : ℤ) - 1))
    have scalarInverse : scalarSeries * PowerSeries.C (C ((degree : ℂ) / 2)) = 1 := by
      dsimp [scalarSeries]
      rw [← map_mul, ← map_mul]
      have cancel : (2 / (degree : ℂ)) * ((degree : ℂ) / 2) = 1 := by
        field_simp
      rw [cancel, map_one, map_one]
    change _ * (scalarSeries * polynomialSeries) - scalarSeries * polynomialSeries =
      polynomialSeries * jetSeries
    calc
      _ = scalarSeries * polynomialSeries *
          (PowerSeries.map (C : ℂ →+* Oscillator D) (halfLabel (degree : ℤ)) - 1) := by
        ring
      _ = scalarSeries * polynomialSeries *
          (PowerSeries.C (C ((degree : ℂ) / 2)) * jetSeries) := by
        rw [← map_one (PowerSeries.map (C : ℂ →+* Oscillator D)), ← map_sub,
          ← jetIdentity]
      _ = (scalarSeries * PowerSeries.C (C ((degree : ℂ) / 2))) *
          (polynomialSeries * jetSeries) := by ring
      _ = polynomialSeries * jetSeries := by rw [scalarInverse, one_mul]
  · rw [if_neg odd, if_neg odd]
    simp

#print axioms integrated_jet_all_modes
#print axioms independent_shift_jet_all_modes
#print axioms integrated_jet_two_sheet
#print axioms actual_creation_log_all_labels

end

end D5.S3.VertexAlgebra.ChargedNormalJetComparisonTransient

import D5.S3.VertexAlgebra.ChargedCreationExponentialTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.ChargedNormalPolynomialFactorsTransient

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockProductKernel LatticeHalfFockFiniteCorrection MvPolynomial
open ChargedNormalJetComparisonTransient ChargedCreationExponentialTransient
open scoped BigOperators

noncomputable section

abbrev ShiftRing (D : LatticeData) := PowerSeries (CorrectionPolynomial D)

def creationShiftHom (D : LatticeData) :
    PowerSeries (Oscillator D) →+* ShiftRing D :=
  (PowerSeries.rescale (X none : CorrectionPolynomial D)).comp
    (PowerSeries.map (MvPolynomial.rename (some : Index D → Option (Index D))).toRingHom)

def shiftedCreationExponential (D : LatticeData) (charge : Charge D) :
    PowerSeries (ShiftRing D) :=
  PowerSeries.map (creationShiftHom D) (originalCreationExpLift D charge)

def shiftedCreationJetLog (D : LatticeData) (charge : Charge D) :
    PowerSeries (ShiftRing D) :=
  PowerSeries.map (creationShiftHom D) (originalCreationJetLog D charge)

private theorem formal_exp_map {Ring Target : Type*}
    [CommRing Ring] [Algebra ℚ Ring] [CommRing Target] [Algebra ℚ Target]
    (hom : Ring →+* Target) (series : PowerSeries Ring)
    (zero : PowerSeries.constantCoeff series = 0) :
    PowerSeries.map hom (formalExp series) = formalExp (PowerSeries.map hom series) := by
  have mapped := PowerSeries.map_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' zero) (h := hom) (PowerSeries.exp Ring)
  change PowerSeries.map hom ((PowerSeries.exp Ring).subst series) =
    (PowerSeries.map hom (PowerSeries.exp Ring)).subst (PowerSeries.map hom series) at mapped
  rw [PowerSeries.map_exp] at mapped
  exact mapped

theorem actual_creation_independent_shift (D : LatticeData) (first second : Charge D) :
    PowerSeries.rescale (creationShiftHom D (originalCreationRoot D))
        (shiftedCreationExponential D first) * shiftedCreationExponential D second =
      shiftedCreationExponential D (first + second) * formalExp (shiftedCreationJetLog D first) := by
  have identity := congrArg (PowerSeries.map (creationShiftHom D))
    (actual_creation_exponential_factorization D first second)
  rw [map_mul, map_mul,
    ← PowerSeries.rescale_map (creationShiftHom D) (originalCreationRoot D),
    formal_exp_map (creationShiftHom D) _
      (by simp [originalCreationJetLog, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])] at identity
  exact identity

theorem actual_creation_joint_coefficients (D : LatticeData) (first second : Charge D)
    (energy order : ℕ) :
    (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal energy,
      PowerSeries.coeff order
        ((creationShiftHom D (originalCreationRoot D)) ^ pair.1 *
          PowerSeries.coeff pair.1 (shiftedCreationExponential D first) *
          PowerSeries.coeff pair.2 (shiftedCreationExponential D second))) =
    ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal energy,
      PowerSeries.coeff order
        (PowerSeries.coeff pair.1 (shiftedCreationExponential D (first + second)) *
          PowerSeries.coeff pair.2 (formalExp (shiftedCreationJetLog D first))) := by
  have identity := congrArg (fun series : PowerSeries (ShiftRing D) =>
    PowerSeries.coeff order (PowerSeries.coeff energy series))
    (actual_creation_independent_shift D first second)
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, map_sum, mul_assoc]
    using identity

def oscillatorToAnnihilation (D : LatticeData) :
    Oscillator D →+* Polynomial (ShiftRing D) :=
  Polynomial.C.comp (PowerSeries.C.comp
    (MvPolynomial.rename (some : Index D → Option (Index D))).toRingHom)

def annihilationSheetEvaluation (D : LatticeData) :
    PairPolynomial D →+* Polynomial (ShiftRing D) :=
  MvPolynomial.eval₂Hom (oscillatorToAnnihilation D)
    (fun label => if label = 0 then
      Polynomial.C (shiftedLabel D (-1)) * Polynomial.X else Polynomial.X)

def annihilationNormalVariable (D : LatticeData) (first second : Charge D)
    (index : Index D) : Polynomial (ShiftRing D) :=
  oscillatorToAnnihilation D (X index) -
    oscillatorToAnnihilation D
      ((bilinear D (first + second) (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
      Polynomial.X ^ omega D index +
    Polynomial.C
      (PowerSeries.C
        (C ((bilinear D first (unitCharge D index.1) : ℂ) * ((index.2 : ℂ) + 1 / 2))) *
          shiftedJet D (index.2 : ℤ)) * Polynomial.X ^ omega D index

local macro "half_label_nat_power_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.ChargedNormalJetComparisonTransient
    `D5.S3.VertexAlgebra.ChargedNormalJetComparisonTransient.half_label_nat_power))

private theorem shifted_label_nat_power (D : LatticeData) (label : ℤ) (degree : ℕ) :
    shiftedLabel D label ^ degree = shiftedLabel D ((degree : ℤ) * label) := by
  have identity := congrArg (fun series : PowerSeries ℂ =>
    PowerSeries.rescale (X none : CorrectionPolynomial D)
      (PowerSeries.map (C : ℂ →+* CorrectionPolynomial D) series))
    (half_label_nat_power_supplier label degree)
  simpa only [map_pow, shiftedLabel] using identity

private theorem oscillator_scalar_image (D : LatticeData) (scalar : ℂ) :
    oscillatorToAnnihilation D (scalar • (1 : Oscillator D)) =
      Polynomial.C (PowerSeries.C (C scalar)) := by
  simp [oscillatorToAnnihilation, Algebra.smul_def]

theorem actual_annihilation_variable (D : LatticeData) (first second : Charge D)
    (index : Index D) :
    annihilationSheetEvaluation D (pairTranslationVariable D first second index) =
      annihilationNormalVariable D first second index := by
  have power : shiftedLabel D (-1) ^ omega D index =
      shiftedLabel D (-(2 * (index.2 : ℤ) + 1)) := by
    rw [shifted_label_nat_power]
    congr 1
    simp [omega]
  have jet := independent_shift_jet_all_modes D (index.2 : ℤ)
  simp only [Int.cast_natCast] at jet
  have pairing : (bilinear D (first + second) (unitCharge D index.1) : ℂ) =
      (bilinear D first (unitCharge D index.1) : ℂ) +
        (bilinear D second (unitCharge D index.1) : ℂ) := by
    unfold bilinear
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Int.cast_add]
  simp only [annihilationSheetEvaluation, pairTranslationVariable,
    map_sub, map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    if_pos rfl, show (1 : Fin 2) ≠ 0 by decide, if_false,
    oscillator_scalar_image, annihilationNormalVariable, pairing, ↓reduceIte, mul_pow]
  rw [← map_pow (Polynomial.C : ShiftRing D →+* Polynomial (ShiftRing D))
    (shiftedLabel D (-1)) (omega D index), power]
  rw [show -(index.2 : ℂ) - 1 / 2 = -((index.2 : ℂ) + 1 / 2) by ring,
    map_neg, map_neg] at jet
  have mappedJet := congrArg (Polynomial.C : ShiftRing D →+* Polynomial (ShiftRing D)) jet
  simp only [map_mul, map_neg, map_sub, map_one] at mappedJet
  simp only [map_add, map_mul] at mappedJet ⊢
  linear_combination Polynomial.C (PowerSeries.C
    (C (bilinear D first (unitCharge D index.1) : ℂ))) *
      Polynomial.X ^ omega D index * mappedJet

def annihilationNormalEvaluation (D : LatticeData) (first second : Charge D) :
    Oscillator D →+* Polynomial (ShiftRing D) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (PowerSeries.C.comp (C : ℂ →+* CorrectionPolynomial D)))
    (annihilationNormalVariable D first second)

theorem actual_annihilation_all_polynomials (D : LatticeData) (first second : Charge D)
    (polynomial : Oscillator D) :
    annihilationSheetEvaluation D (pairTranslation D first second polynomial) =
      annihilationNormalEvaluation D first second polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    simp [pairTranslation, annihilationSheetEvaluation, annihilationNormalEvaluation,
      oscillatorToAnnihilation]
  | add left right leftProof rightProof =>
    simp only [map_add, leftProof, rightProof]
  | mul_X polynomial index previous =>
    have variableLaw : pairTranslation D first second (X index) =
        pairTranslationVariable D first second index :=
      MvPolynomial.eval₂AlgHom_X _ _
    have normalLaw : annihilationNormalEvaluation D first second (X index) =
        annihilationNormalVariable D first second index :=
      MvPolynomial.eval₂Hom_X' _ _ _
    calc
      _ = annihilationSheetEvaluation D (pairTranslation D first second polynomial) *
          annihilationSheetEvaluation D (pairTranslation D first second (X index)) := by
        rw [map_mul, map_mul]
      _ = annihilationNormalEvaluation D first second polynomial *
          annihilationNormalVariable D first second index := by
        rw [previous, variableLaw, actual_annihilation_variable]
      _ = annihilationNormalEvaluation D first second (polynomial * X index) := by
        rw [map_mul, normalLaw]

#print axioms actual_creation_joint_coefficients
#print axioms actual_annihilation_all_polynomials

end

end D5.S3.VertexAlgebra.ChargedNormalPolynomialFactorsTransient

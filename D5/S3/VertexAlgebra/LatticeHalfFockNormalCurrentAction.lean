/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNormalCurrentAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNormalCurrentAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original integer current action inside finite native normal-polynomial fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockCurrentCorrection
open LatticeHalfFockCurrentNormalRecurrence MvPolynomial
open scoped BigOperators

noncomputable section

theorem binomial_product (scalar : ℂ) (degree : ℕ) :
    Ring.choose scalar degree =
      (∏ offset ∈ Finset.range degree, (scalar - (offset : ℂ))) / (degree.factorial : ℂ) := by
  have product : (descPochhammer ℤ degree).smeval scalar =
      ∏ offset ∈ Finset.range degree, (scalar - (offset : ℂ)) := by
    induction degree with
    | zero => simp
    | succ degree previous =>
      simp only [descPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
        pow_zero, pow_one, nsmul_eq_mul, mul_one, previous, Finset.prod_range_succ]
  rw [Ring.choose_eq_smul, product, smul_eq_mul]
  ring

theorem jet_contraction_binomial (mode : ℤ) (degree : ℕ) :
    LatticeHalfFock.frequency mode * jetScalar degree (-mode - 1) =
      (degree + 1 : ℂ) * Ring.choose (LatticeHalfFock.frequency mode) (degree + 1) := by
  rw [binomial_product, Finset.prod_range_succ', jetScalar]
  have product : (∏ offset ∈ Finset.range degree,
      (-((-mode - 1 : ℤ) : ℂ) - 3 / 2 - (offset : ℂ))) =
      ∏ offset ∈ Finset.range degree,
        (LatticeHalfFock.frequency mode - ((offset + 1 : ℕ) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro offset member
    simp only [LatticeHalfFock.frequency, Int.cast_sub, Int.cast_neg,
      Int.cast_one, Nat.cast_add, Nat.cast_one]
    ring
  rw [product, Nat.factorial_succ]
  have factorial : (degree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero degree
  have successor : (degree + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
  field_simp

def coverShiftLinear (D : LatticeData) (hu : IsUnit D.G.det) (shift : ℤ) :
    NativeField D hu →ₗ[ℂ] NativeField D hu where
  toFun := coverShift D hu shift
  map_add' first second := by
    apply HVertexOperator.coeff_inj
    ext exponent vector
    simp only [coverShift, HVertexOperator.coeff_of_coeff]
    rfl
  map_smul' scalar field := by
    apply HVertexOperator.coeff_inj
    ext exponent vector
    simp only [coverShift, HVertexOperator.coeff_of_coeff]
    rfl

theorem normalPolynomial_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : Oscillator D) :
    normalPolynomial D hu charge (polynomial * X index) =
      normalInsertionLinear D hu index (normalPolynomial D hu charge polynomial) := by
  induction polynomial using MvPolynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [add_mul, map_add, firstProof, secondProof]
  | monomial exponent scalar =>
    have scale (exponent : Index D →₀ ℕ) :
        monomial exponent scalar = scalar • monomial exponent 1 := by
      simp [smul_monomial]
    rw [X, monomial_mul, mul_one, scale, map_smul,
      normalPolynomial_monomial_enumeration D hu charge _
        (index :: LatticeAllStateField.occurrences D exponent) (occurrences_cons D index exponent),
      scale, map_smul, map_smul,
      normalPolynomial_monomial_enumeration D hu charge exponent _ (List.Perm.refl _)]
    rfl

theorem Corr_neutralPolynomialMode (D : LatticeData) (charge : Charge D)
    (colour : Fin D.rank) (degree shift : ℕ) (polynomial : Oscillator D) :
    Corr D charge (neutralPolynomialMode D colour charge degree polynomial) shift =
      neutralPolynomialMode D colour charge degree (Corr D charge polynomial shift) := by
  cases degree with
  | zero => simp [neutralPolynomialMode, map_smul]
  | succ degree =>
    simp only [Nat.cast_add, Nat.cast_one, neutralPolynomialMode_positive, weightedPartial,
      LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe, map_smul, map_sum,
      Finsupp.smul_apply, Finsupp.finsetSum_apply, Corr_partial]

theorem neutralPolynomialMode_X_mul (D : LatticeData) (charge : Charge D)
    (colour : Fin D.rank) (degree : ℕ) (index : Index D) (polynomial : Oscillator D) :
    neutralPolynomialMode D colour charge degree (polynomial * X index) =
      neutralPolynomialMode D colour charge degree polynomial * X index +
        if degree = index.2 + 1 then ((degree : ℂ) * (D.G colour index.1 : ℂ)) • polynomial
          else 0 := by
  classical
  cases degree with
  | zero => simp [neutralPolynomialMode, smul_mul_assoc]
  | succ degree =>
    simp only [Nat.cast_add, Nat.cast_one]
    have contraction := LatticeSugawaraCurrents.weightedPartial_X_mul
      D colour index.1 degree index.2 polynomial
    rw [mul_comm polynomial (X index), neutralPolynomialMode_positive, LinearMap.smul_apply,
      contraction, smul_add, LinearMap.smul_apply]
    by_cases same : degree = index.2
    · simp [same, smul_smul, mul_smul_comm, add_comm, mul_comm]
    · simp [same, mul_smul_comm, add_comm, mul_comm]

def deltaTerm (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) (degree : ℕ) :
    NativeField D hu :=
  Ring.choose (LatticeHalfFock.frequency mode) degree •
    coverShiftLinear D hu (-(2 * mode + 1) + 2 * degree)
      (normalPolynomial D hu charge (neutralPolynomialMode D colour charge degree polynomial))

theorem deltaTerm_support (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) :
    Function.support (deltaTerm D hu charge colour mode polynomial) ⊆
      Finset.range (polynomialFrequencyBound D polynomial + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  have vanish := neutralPolynomialMode_vanish D colour charge polynomial degree (by omega)
  exact nonzero (by simp [deltaTerm, vanish])

theorem deltaTerm_finite (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (deltaTerm D hu charge colour mode polynomial) :=
  (Finset.range (polynomialFrequencyBound D polynomial + 1)).finite_toSet.subset
    (deltaTerm_support D hu charge colour mode polynomial)

def nativeDelta (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) : NativeField D hu :=
  ∑ᶠ degree : ℕ, deltaTerm D hu charge colour mode polynomial degree

theorem nativeDelta_add (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (first second : Oscillator D) :
    nativeDelta D hu charge colour mode (first + second) =
      nativeDelta D hu charge colour mode first + nativeDelta D hu charge colour mode second := by
  have terms : deltaTerm D hu charge colour mode (first + second) =
      fun degree => deltaTerm D hu charge colour mode first degree +
        deltaTerm D hu charge colour mode second degree := by
    funext degree
    simp only [deltaTerm, map_add, smul_add]
  rw [nativeDelta, terms, finsum_add_distrib (deltaTerm_finite D hu charge colour mode first)
    (deltaTerm_finite D hu charge colour mode second)]
  rfl

end
end D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction

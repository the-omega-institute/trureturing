/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd-weight native creation coefficients have two-branch contraction. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients

open LatticeGeneratingFieldLocality MvPolynomial
open scoped BigOperators

noncomputable section

def omega (D : LatticeData) (index : Index D) : ℕ := 2 * index.2 + 1

def halfCreationSeries (D : LatticeData) (charge : Charge D) :
    PowerSeries (Oscillator D) :=
  PowerSeries.mk fun degree =>
    if degree % 2 = 1 then
      (2 / (degree : ℂ)) •
        ∑ colour : Fin D.rank, (charge colour : ℂ) • (X (colour, degree / 2) : Oscillator D)
    else 0

def halfCreationExponential (D : LatticeData) (charge : Charge D) :
    PowerSeries (Oscillator D) :=
  (PowerSeries.exp (Oscillator D)).subst (halfCreationSeries D charge)

def halfCreationCoeff (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    Oscillator D :=
  if degree < 0 then 0 else PowerSeries.coeff degree.toNat (halfCreationExponential D charge)

def halfTranslationVariable (D : LatticeData) (charge : Charge D) (index : Index D) :
    Polynomial (Oscillator D) :=
  Polynomial.C (X index : Oscillator D) -
    Polynomial.C ((bilinear D charge (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
      Polynomial.X ^ omega D index

def halfTranslatedPolynomial (D : LatticeData) (charge : Charge D) (polynomial : Oscillator D) :
    Polynomial (Oscillator D) :=
  MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D charge) polynomial

def halfContraction (D : LatticeData) (left right : Charge D) : PowerSeries ℂ :=
  PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.binomialSeries (R := ℤ) ℂ (bilinear D left right)) *
    PowerSeries.binomialSeries (R := ℤ) ℂ (-bilinear D left right)

private theorem series_constant (D : LatticeData) (charge : Charge D) :
    PowerSeries.constantCoeff (halfCreationSeries D charge) = 0 := by
  simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem exponential_derivative (D : LatticeData) (charge : Charge D) :
    PowerSeries.derivative (Oscillator D) (halfCreationExponential D charge) =
      halfCreationExponential D charge *
        PowerSeries.derivative (Oscillator D) (halfCreationSeries D charge) := by
  rw [halfCreationExponential, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' (series_constant D charge)),
    PowerSeries.derivative_exp]

theorem exponential_constant (D : LatticeData) (charge : Charge D) :
    PowerSeries.coeff 0 (halfCreationExponential D charge) = 1 := by
  rw [halfCreationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' (series_constant D charge)),
    finsum_eq_single _ 0]
  · simp
  · intro degree hdegree
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, series_constant]
    simp [hdegree]

private theorem half_annihilation_logarithm (D : LatticeData) (colour : Fin D.rank)
    (mode : ℕ) (charge : Charge D) :
    ActualSeriesDerivation.seriesDerivation D
        (LatticeActualAnnihilation.annihilationDerivation D colour mode)
        (halfCreationSeries D charge) =
      PowerSeries.C (((2 / (2 * mode + 1 : ℂ)) *
        (bilinear D (unitCharge D colour) charge : ℂ)) • (1 : Oscillator D)) *
          PowerSeries.X ^ (2 * mode + 1) := by
  apply PowerSeries.ext
  intro degree
  rw [ActualSeriesDerivation.series_coeff]
  simp only [halfCreationSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases odd : degree % 2 = 1
  · rw [if_pos odd, Derivation.map_smul,
      LatticeActualAnnihilation.annihilation_linear_creation]
    by_cases same : mode = degree / 2
    · have index : degree = 2 * mode + 1 := by omega
      subst degree
      rw [if_pos (by omega : mode = (2 * mode + 1) / 2)]
      simp only [if_pos rfl, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, ite_true, smul_smul, mul_one]
    · have index : degree ≠ 2 * mode + 1 := by omega
      simp [same, index, Ne.symm index]
  · have index : degree ≠ 2 * mode + 1 := by omega
    simp [odd, index, Ne.symm index]

theorem half_annihilation_creation (D : LatticeData) (colour : Fin D.rank)
    (mode : ℕ) (charge : Charge D) (degree : ℤ) :
    LatticeActualAnnihilation.annihilate D colour mode (halfCreationCoeff D charge degree) =
      ((2 / (2 * mode + 1 : ℂ)) * (bilinear D (unitCharge D colour) charge : ℂ)) •
        halfCreationCoeff D charge (degree - (2 * mode + 1 : ℕ)) := by
  have natural_law (degree : ℕ) :
      LatticeActualAnnihilation.annihilate D colour mode
          (PowerSeries.coeff degree (halfCreationExponential D charge)) =
        if 2 * mode + 1 ≤ degree then
          ((2 / (2 * mode + 1 : ℂ)) * (bilinear D (unitCharge D colour) charge : ℂ)) •
            PowerSeries.coeff (degree - (2 * mode + 1)) (halfCreationExponential D charge)
        else 0 := by
    have chain := congrArg (PowerSeries.coeff degree)
      (ActualSeriesDerivation.actual_exponential_derivation_series D
        (LatticeActualAnnihilation.annihilationDerivation D colour mode)
        (halfCreationSeries D charge) (series_constant D charge))
    change PowerSeries.coeff degree (ActualSeriesDerivation.seriesDerivation D
      (LatticeActualAnnihilation.annihilationDerivation D colour mode)
        (halfCreationExponential D charge)) = _ at chain
    rw [ActualSeriesDerivation.series_coeff, LatticeActualAnnihilation.annihilation_apply,
      half_annihilation_logarithm, ← mul_assoc, PowerSeries.coeff_mul_X_pow'] at chain
    rw [chain]
    split_ifs
    · rw [PowerSeries.coeff_mul_C, mul_smul_comm, mul_one]
      rfl
    · rfl
  by_cases negative : degree < 0
  · rw [halfCreationCoeff, if_pos negative, map_zero, halfCreationCoeff,
      if_pos (by omega), smul_zero]
  · rw [halfCreationCoeff, if_neg negative, natural_law]
    by_cases shifted : 2 * mode + 1 ≤ degree.toNat
    · rw [if_pos shifted, halfCreationCoeff, if_neg (by omega),
        show (degree - (2 * mode + 1 : ℕ)).toNat = degree.toNat - (2 * mode + 1) by omega]
    · rw [if_neg shifted, halfCreationCoeff, if_pos (by omega), smul_zero]

theorem half_translated_derivation (D : LatticeData) (colour : Fin D.rank)
    (mode : ℕ) (charge : Charge D) (polynomial : Oscillator D) :
    halfTranslatedPolynomial D charge
        (LatticeActualAnnihilation.annihilate D colour mode polynomial) =
      LatticeActualAnnihilation.polynomialDerivation D colour mode
        (halfTranslatedPolynomial D charge polynomial) := by
  open LatticeActualAnnihilation in
  have variable_law (index : Index D) :
      halfTranslatedPolynomial D charge (annihilate D colour mode (X index)) =
        polynomialDerivation D colour mode (halfTranslatedPolynomial D charge (X index)) := by
    rcases index with ⟨other, level⟩
    have constant_law (scalar : ℂ) : annihilate D colour mode (scalar • (1 : Oscillator D)) = 0 := by
      rw [← annihilation_apply, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
    have translated_constant (scalar : ℂ) :
        halfTranslatedPolynomial D charge (scalar • (1 : Oscillator D)) =
          Polynomial.C (scalar • (1 : Oscillator D)) := by
      simp [halfTranslatedPolynomial, Algebra.smul_def]
    simp only [halfTranslatedPolynomial, MvPolynomial.eval₂AlgHom_X,
      halfTranslationVariable, map_sub, Derivation.leibniz, polynomialDerivation_C,
      constant_law, polynomialDerivation_X, Derivation.leibniz_pow, smul_zero,
      zero_smul, add_zero, zero_add, map_zero, sub_zero]
    change halfTranslatedPolynomial D charge (annihilate D colour mode (X (other, level))) = _
    rw [annihilate_X]
    by_cases same : mode = level
    · simp only [if_pos same]
      exact translated_constant _
    · simp [same, halfTranslatedPolynomial]
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    simp [halfTranslatedPolynomial, LatticeActualAnnihilation.polynomialDerivation_C,
      LatticeActualAnnihilation.annihilate, LatticeSugawaraCurrents.weightedPartial]
  | add left right hleft hright =>
    simp only [map_add, halfTranslatedPolynomial, map_add] at hleft hright ⊢
    rw [hleft, hright]
  | mul_X polynomial index previous =>
    rw [LatticeActualAnnihilation.annihilate_mul]
    simp only [halfTranslatedPolynomial, map_add, map_mul] at previous variable_law ⊢
    rw [previous, variable_law,
      (LatticeActualAnnihilation.polynomialDerivation D colour mode).leibniz]
    simp only [smul_eq_mul]
    ring

theorem series_derivative_coeff (D : LatticeData) (charge : Charge D) (degree : ℕ) :
    PowerSeries.coeff degree (PowerSeries.derivative (Oscillator D)
      (halfCreationSeries D charge)) =
      if degree % 2 = 0 then
        (2 : ℂ) • ∑ colour : Fin D.rank,
          (charge colour : ℂ) • (X (colour, degree / 2) : Oscillator D)
      else 0 := by
  rw [PowerSeries.coeff_derivative]
  by_cases heven : degree % 2 = 0
  · have hodd : (degree + 1) % 2 = 1 := by omega
    have hindex : (degree + 1) / 2 = degree / 2 := by omega
    simp only [halfCreationSeries, PowerSeries.coeff_mk, if_pos hodd, if_pos heven, hindex]
    rw [mul_comm, show (degree + 1 : Oscillator D) =
      algebraMap ℂ (Oscillator D) (degree + 1 : ℂ) by simp,
      ← Algebra.smul_def, smul_smul]
    congr 1
    have hnonzero : (degree + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
    field_simp
    simp
  · have hodd : (degree + 1) % 2 ≠ 1 := by omega
    simp [halfCreationSeries, hodd, heven]

private theorem derivative_map {Ring : Type*} [CommRing Ring]
    {Target : Type*} [CommRing Target] (hom : Ring →+* Target) (series : PowerSeries Ring) :
    PowerSeries.derivative Target (series.map hom) =
      (PowerSeries.derivative Ring series).map hom := by
  apply PowerSeries.ext
  intro degree
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_map, PowerSeries.coeff_map,
    PowerSeries.coeff_derivative, map_mul]
  simp

private theorem choose_recurrence (gram : ℤ) (degree : ℕ) :
    (degree + 1 : ℤ) * Ring.choose gram (degree + 1) =
      (gram - degree) * Ring.choose gram degree := by
  apply (nsmul_right_inj (Nat.factorial_ne_zero degree)).mp
  have recurrence := Ring.descPochhammer_eq_factorial_smul_choose gram (degree + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    pow_one, pow_zero, nsmul_one,
    Ring.descPochhammer_eq_factorial_smul_choose, Nat.factorial_succ] at recurrence
  simp only [nsmul_eq_mul] at recurrence ⊢
  push_cast at recurrence
  nlinarith [recurrence]

private theorem scaled_binomial_derivative {Ring : Type*} [CommRing Ring]
    (gram : ℤ) (scale : Ring) :
    PowerSeries.derivative Ring
        (PowerSeries.rescale scale (PowerSeries.binomialSeries (R := ℤ) Ring gram)) *
        (1 + PowerSeries.C scale * PowerSeries.X) =
      PowerSeries.C ((gram : Ring) * scale) *
        PowerSeries.rescale scale (PowerSeries.binomialSeries (R := ℤ) Ring gram) := by
  let series := PowerSeries.rescale scale (PowerSeries.binomialSeries (R := ℤ) Ring gram)
  have hcoeff (degree : ℕ) : PowerSeries.coeff degree series =
      scale ^ degree * ((_root_.Ring.choose gram degree : ℤ) : Ring) := by
    simp [series, PowerSeries.coeff_rescale, zsmul_eq_mul]
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero =>
    rw [mul_add, mul_one, ← mul_assoc, map_add, PowerSeries.coeff_zero_mul_X,
      add_zero, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]
    norm_num only [Nat.cast_zero, zero_add]
    change PowerSeries.coeff 1 series * 1 =
      (gram : Ring) * scale * PowerSeries.coeff 0 series
    rw [hcoeff, hcoeff]
    simp [mul_comm]
  | succ degree =>
    rw [mul_add, mul_one, ← mul_assoc, map_add, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, hcoeff, hcoeff]
    have recurrence : (degree + 2 : Ring) *
        ((_root_.Ring.choose gram (degree + 2) : ℤ) : Ring) =
        ((gram : Ring) - (degree + 1 : Ring)) *
          ((_root_.Ring.choose gram (degree + 1) : ℤ) : Ring) := by
      have cast := congrArg (Int.castRingHom Ring) (choose_recurrence gram (degree + 1))
      simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_sub, Int.cast_add,
        Int.cast_natCast, Int.cast_one, Int.cast_ofNat, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using cast
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    linear_combination scale ^ (degree + 1) * scale * recurrence

private theorem solution_unique {Ring : Type*} [CommRing Ring] [IsAddTorsionFree Ring]
    (first second driver : PowerSeries Ring)
    (hfirst : PowerSeries.derivative Ring first = first * driver)
    (hsecond : PowerSeries.derivative Ring second = second * driver)
    (hconstant : PowerSeries.coeff 0 first = PowerSeries.coeff 0 second) : first = second := by
  apply PowerSeries.ext
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree previous =>
    cases degree with
    | zero => exact hconstant
    | succ degree =>
      have first_eq := congrArg (PowerSeries.coeff degree) hfirst
      have second_eq := congrArg (PowerSeries.coeff degree) hsecond
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at first_eq second_eq
      have sums : (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
          PowerSeries.coeff pair.1 first * PowerSeries.coeff pair.2 driver) =
          ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
            PowerSeries.coeff pair.1 second * PowerSeries.coeff pair.2 driver := by
        apply Finset.sum_congr rfl
        intro pair hpair
        rw [previous pair.1 (by
          have := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
          omega)]
      have equal : PowerSeries.coeff (degree + 1) first * (degree + 1) =
          PowerSeries.coeff (degree + 1) second * (degree + 1) := by
        rw [first_eq, sums, second_eq]
      rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul] at equal
      exact (smul_right_inj (Nat.succ_ne_zero degree)).mp equal

private theorem binomial_map {Ring Target : Type*} [CommRing Ring] [CommRing Target]
    (hom : Ring →+* Target) (gram : ℤ) :
    (PowerSeries.binomialSeries (R := ℤ) Ring gram).map hom =
      PowerSeries.binomialSeries (R := ℤ) Target gram := by
  apply PowerSeries.ext
  intro degree
  simp [PowerSeries.coeff_map, zsmul_eq_mul]

private theorem two_factor_derivative {Ring : Type*} [CommRing Ring]
    (gram : ℤ) (scale : Ring) :
    let minus := PowerSeries.rescale (-scale) (PowerSeries.binomialSeries (R := ℤ) Ring gram)
    let plus := PowerSeries.rescale scale (PowerSeries.binomialSeries (R := ℤ) Ring (-gram))
    PowerSeries.derivative Ring (minus * plus) *
        (1 - PowerSeries.C (scale ^ 2) * PowerSeries.X ^ 2) =
      -PowerSeries.C (2 * (gram : Ring) * scale) * (minus * plus) := by
  dsimp only
  let minus := PowerSeries.rescale (-scale) (PowerSeries.binomialSeries (R := ℤ) Ring gram)
  let plus := PowerSeries.rescale scale (PowerSeries.binomialSeries (R := ℤ) Ring (-gram))
  have hminus := scaled_binomial_derivative gram (-scale)
  have hplus := scaled_binomial_derivative (-gram) scale
  have factors : (1 + PowerSeries.C (-scale) * PowerSeries.X) *
      (1 + PowerSeries.C scale * PowerSeries.X) =
      1 - PowerSeries.C (scale ^ 2) * PowerSeries.X ^ 2 := by
    rw [map_neg, map_pow]
    ring
  calc
    _ = (PowerSeries.derivative Ring minus *
          (1 + PowerSeries.C (-scale) * PowerSeries.X)) *
          plus * (1 + PowerSeries.C scale * PowerSeries.X) +
        (PowerSeries.derivative Ring plus *
          (1 + PowerSeries.C scale * PowerSeries.X)) *
          minus * (1 + PowerSeries.C (-scale) * PowerSeries.X) := by
      rw [← factors, (PowerSeries.derivative Ring).leibniz]
      ring
    _ = _ := by
      rw [hminus, hplus]
      simp only [Int.cast_neg, mul_neg, neg_mul, map_neg]
      have ctwo : PowerSeries.C (2 : Ring) = (2 : PowerSeries Ring) := by
        rw [show (2 : Ring) = 1 + 1 by norm_num, map_add, map_one]
        norm_num
      rw [show PowerSeries.C (2 * (gram : Ring) * scale) =
        2 * PowerSeries.C ((gram : Ring) * scale) by
          simp only [map_mul, ctwo]
          ring]
      ring

/- proof_shape: half_creation_coefficient_grading: content
   admission_basis: escape-witness
   escape_witness: The actual substituted exponential obeys an odd-weight
   coefficient induction on the unrestricted native polynomial algebra.
   Literature status: classical half-lattice construction; zero novelty. -/
theorem half_creation_coefficient_grading (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    MvPolynomial.IsWeightedHomogeneous (omega D) (halfCreationCoeff D charge degree)
      degree.toNat := by
  classical
  have natural_grading : ∀ degree : ℕ, MvPolynomial.IsWeightedHomogeneous (omega D)
      (PowerSeries.coeff degree (halfCreationExponential D charge)) degree := by
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree previous =>
      cases degree with
      | zero =>
        rw [exponential_constant]
        exact MvPolynomial.isWeightedHomogeneous_one ℂ _
      | succ degree =>
        have recurrence := congrArg (PowerSeries.coeff degree) (exponential_derivative D charge)
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at recurrence
        have homogeneous : MvPolynomial.IsWeightedHomogeneous (omega D)
            (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
              PowerSeries.coeff pair.1 (halfCreationExponential D charge) *
                PowerSeries.coeff pair.2
                  (PowerSeries.derivative (Oscillator D) (halfCreationSeries D charge)))
            (degree + 1) := by
          apply MvPolynomial.IsWeightedHomogeneous.sum
          intro pair hpair
          have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
          have hfirst := previous pair.1 (by omega)
          have hsecond : MvPolynomial.IsWeightedHomogeneous (omega D)
              (PowerSeries.coeff pair.2
                (PowerSeries.derivative (Oscillator D) (halfCreationSeries D charge)))
              (pair.2 + 1) := by
            rw [series_derivative_coeff]
            split_ifs with heven
            · apply (MvPolynomial.weightedHomogeneousSubmodule ℂ (omega D) (pair.2 + 1)).smul_mem
              apply MvPolynomial.IsWeightedHomogeneous.sum
              intro colour hcolour
              have hweight : omega D (colour, pair.2 / 2) = pair.2 + 1 := by
                dsimp [omega]
                omega
              rw [← hweight]
              exact (MvPolynomial.weightedHomogeneousSubmodule ℂ (omega D)
                (omega D (colour, pair.2 / 2))).smul_mem _
                (MvPolynomial.isWeightedHomogeneous_X ℂ (omega D) (colour, pair.2 / 2))
            · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
          simpa only [← Nat.add_assoc, hsum] using hfirst.mul hsecond
        rw [← recurrence] at homogeneous
        intro exponent hexponent
        apply homogeneous
        rw [show (degree + 1 : Oscillator D) = MvPolynomial.C (degree + 1 : ℂ) by simp,
          mul_comm, MvPolynomial.coeff_C_mul]
        exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero degree) hexponent
  by_cases hnegative : degree < 0
  · rw [halfCreationCoeff, if_pos hnegative]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  · rw [halfCreationCoeff, if_neg hnegative]
    exact natural_grading degree.toNat

private theorem translated_degree_le (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (weight : ℕ)
    (homogeneous : MvPolynomial.IsWeightedHomogeneous (omega D) polynomial weight) :
    (halfTranslatedPolynomial D charge polynomial).natDegree ≤ weight := by
  classical
  have variable_bound (index : Index D) :
      (halfTranslationVariable D charge index).natDegree ≤ omega D index := by
    dsimp only [halfTranslationVariable]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  change (MvPolynomial.eval₂ (algebraMap ℂ (Polynomial (Oscillator D)))
    (halfTranslationVariable D charge) polynomial).natDegree ≤ weight
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  have hweight := homogeneous (MvPolynomial.mem_support_iff.mp hexponent)
  apply Polynomial.natDegree_mul_le.trans
  rw [show (algebraMap ℂ (Polynomial (Oscillator D))) (MvPolynomial.coeff exponent polynomial) =
    Polynomial.C ((algebraMap ℂ (Oscillator D)) (MvPolynomial.coeff exponent polynomial)) by rfl,
    Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  rw [← hweight, Finsupp.weight_apply]
  change (∑ index ∈ exponent.support,
    ((halfTranslationVariable D charge index) ^ exponent index).natDegree) ≤
      ∑ index ∈ exponent.support, exponent index * omega D index
  apply Finset.sum_le_sum
  intro index hindex
  exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (variable_bound index))

/- proof_shape: half_creation_coefficient_transport: content
   admission_basis: escape-witness
   escape_witness: Actual finite polynomial translation and the actual odd
   exponential satisfy the same initial-value recurrence as the two binomial
   factors, uniformly for every integer creation index and natural coefficient.
   Literature status: classical half-lattice construction; zero novelty. -/
attribute [-instance] PowerSeries.algebraPolynomial in
theorem half_creation_coefficient_transport (D : LatticeData) (left right : Charge D)
    (degree : ℤ) (translatedDegree : ℕ) :
    (halfTranslatedPolynomial D left (halfCreationCoeff D right degree)).coeff translatedDegree =
      (PowerSeries.coeff translatedDegree (halfContraction D left right)) •
        halfCreationCoeff D right (degree - translatedDegree) := by
  classical
  let coverVariable : Polynomial (Oscillator D) := Polynomial.X
  let gram := bilinear D left right
  let translation : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
    MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D left)
  let logarithm := (halfCreationSeries D right).map translation.toRingHom
  let originalLogarithm := (halfCreationSeries D right).map
    (Polynomial.C : Oscillator D →+* Polynomial (Oscillator D))
  let translated := (halfCreationExponential D right).map translation.toRingHom
  let original := (halfCreationExponential D right).map
    (Polynomial.C : Oscillator D →+* Polynomial (Oscillator D))
  let minus := PowerSeries.rescale (-coverVariable)
    (PowerSeries.binomialSeries (R := ℤ) (Polynomial (Oscillator D)) gram)
  let plus := PowerSeries.rescale coverVariable
    (PowerSeries.binomialSeries (R := ℤ) (Polynomial (Oscillator D)) (-gram))
  let contraction := minus * plus
  let denominator : PowerSeries (Polynomial (Oscillator D)) :=
    1 - PowerSeries.C (coverVariable ^ 2) * PowerSeries.X ^ 2
  have pairing : (∑ colour : Fin D.rank,
      (right colour : ℂ) * (bilinear D left (unitCharge D colour) : ℂ)) = (gram : ℂ) := by
    have integral : (∑ colour : Fin D.rank,
        right colour * bilinear D left (unitCharge D colour)) = gram := by
      simp only [bilinear, unitCharge, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro colour hcolour
      apply Finset.sum_congr rfl
      intro other hother
      ring
    exact_mod_cast integral
  have constant_smul (scalar : ℂ) (polynomial : Oscillator D) :
      Polynomial.C (scalar • polynomial) =
        scalar • (Polynomial.C polynomial : Polynomial (Oscillator D)) :=
    map_smul (Polynomial.CAlgHom : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D))
      scalar polynomial
  have difference_coeff (index : ℕ) :
      PowerSeries.coeff index (PowerSeries.derivative (Polynomial (Oscillator D)) logarithm -
        PowerSeries.derivative (Polynomial (Oscillator D)) originalLogarithm) =
      if index % 2 = 0 then
        -Polynomial.C ((2 * (gram : ℂ)) • (1 : Oscillator D)) * coverVariable ^ (index + 1)
      else 0 := by
    rw [map_sub]
    dsimp only [logarithm, originalLogarithm]
    rw [derivative_map, derivative_map, PowerSeries.coeff_map, PowerSeries.coeff_map,
      series_derivative_coeff]
    by_cases heven : index % 2 = 0
    · simp only [if_pos heven]
      change translation ((2 : ℂ) • ∑ colour : Fin D.rank,
        (right colour : ℂ) • (X (colour, index / 2) : Oscillator D)) -
        Polynomial.C ((2 : ℂ) • ∑ colour : Fin D.rank,
          (right colour : ℂ) • (X (colour, index / 2) : Oscillator D)) = _
      rw [map_smul, constant_smul, ← smul_sub, map_sum, map_sum]
      have weight : ∀ colour : Fin D.rank, omega D (colour, index / 2) = index + 1 := by
        intro colour
        dsimp [omega]
        omega
      simp only [map_smul, translation, MvPolynomial.eval₂AlgHom_X,
        halfTranslationVariable, weight, smul_sub, constant_smul, smul_mul_assoc,
        smul_smul, Finset.sum_sub_distrib]
      rw [sub_sub_cancel_left, ← Finset.sum_smul, pairing]
      simp [smul_smul, smul_mul_assoc, ← constant_smul, coverVariable]
    · simp [heven]
  have difference_equation :
      (PowerSeries.derivative (Polynomial (Oscillator D)) logarithm -
        PowerSeries.derivative (Polynomial (Oscillator D)) originalLogarithm) * denominator =
      -PowerSeries.C (Polynomial.C ((2 * (gram : ℂ)) • (1 : Oscillator D)) * coverVariable) := by
    apply PowerSeries.ext
    intro index
    rw [mul_sub, mul_one, ← mul_assoc, map_sub, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mul_C, difference_coeff, difference_coeff]
    cases index with
    | zero => simp
    | succ index =>
      cases index with
      | zero => simp
      | succ index =>
        have parity : (index + 1 + 1) % 2 = index % 2 := by omega
        have subtraction : index + 1 + 1 - 2 = index := by omega
        simp only [parity, subtraction, show 2 ≤ index + 1 + 1 by omega, if_true,
          map_neg, PowerSeries.coeff_C, Nat.succ_ne_zero, if_false]
        split_ifs <;> simp only [zero_mul, sub_self, pow_succ] <;> ring
  have contraction_equation :
      PowerSeries.derivative (Polynomial (Oscillator D)) contraction * denominator =
      -PowerSeries.C (Polynomial.C ((2 * (gram : ℂ)) • (1 : Oscillator D)) * coverVariable) *
        contraction := by
    have equation := two_factor_derivative gram coverVariable
    have cast : Polynomial.C ((2 * (gram : ℂ)) • (1 : Oscillator D)) =
        2 * (gram : Polynomial (Oscillator D)) := by
      rw [Algebra.smul_def, mul_one, map_mul]
      have two : Polynomial.C (algebraMap ℂ (Oscillator D) (2 : ℂ)) =
          (2 : Polynomial (Oscillator D)) := by
        rw [show (2 : ℂ) = 1 + 1 by norm_num, map_add, map_one, map_add, map_one]
        norm_num
      rw [map_mul, two]
      simp
    simpa only [contraction, minus, plus, denominator, cast] using equation
  have unit_denominator : IsUnit denominator :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [denominator])
  have contraction_derivative :
      PowerSeries.derivative (Polynomial (Oscillator D)) contraction =
        contraction * (PowerSeries.derivative (Polynomial (Oscillator D)) logarithm -
          PowerSeries.derivative (Polynomial (Oscillator D)) originalLogarithm) := by
    apply unit_denominator.mul_right_cancel
    rw [contraction_equation, mul_assoc, difference_equation]
    ring
  have translated_derivative : PowerSeries.derivative (Polynomial (Oscillator D)) translated =
      translated * PowerSeries.derivative (Polynomial (Oscillator D)) logarithm := by
    dsimp only [translated, logarithm]
    rw [derivative_map, exponential_derivative, map_mul, derivative_map]
  have original_derivative : PowerSeries.derivative (Polynomial (Oscillator D)) original =
      original * PowerSeries.derivative (Polynomial (Oscillator D)) originalLogarithm := by
    dsimp only [original, originalLogarithm]
    rw [derivative_map, exponential_derivative, map_mul, derivative_map]
  have product_derivative :
      PowerSeries.derivative (Polynomial (Oscillator D)) (original * contraction) =
        (original * contraction) * PowerSeries.derivative (Polynomial (Oscillator D)) logarithm := by
    rw [(PowerSeries.derivative (Polynomial (Oscillator D))).leibniz,
      contraction_derivative, original_derivative]
    ring
  have same_constant : PowerSeries.coeff 0 translated =
      PowerSeries.coeff 0 (original * contraction) := by
    dsimp only [translated, original, contraction, minus, plus]
    simp only [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, PowerSeries.coeff_map, exponential_constant, map_one,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.binomialSeries_coeff,
      Ring.choose_zero_right, one_smul, mul_one]
  have series_eq := solution_unique translated (original * contraction)
    (PowerSeries.derivative (Polynomial (Oscillator D)) logarithm)
    translated_derivative product_derivative same_constant
  let embedding : ℂ →+* Polynomial (Oscillator D) := algebraMap ℂ (Polynomial (Oscillator D))
  have mapped_contraction : (halfContraction D left right).map embedding =
      PowerSeries.rescale (-1 : Polynomial (Oscillator D))
          (PowerSeries.binomialSeries (R := ℤ) (Polynomial (Oscillator D)) gram) *
        PowerSeries.binomialSeries (R := ℤ) (Polynomial (Oscillator D)) (-gram) := by
    rw [halfContraction, map_mul, ← PowerSeries.rescale_map, binomial_map, binomial_map]
    simp [embedding, gram]
  have contraction_rescale : contraction =
      PowerSeries.rescale coverVariable ((halfContraction D left right).map embedding) := by
    rw [mapped_contraction, map_mul, PowerSeries.rescale_rescale]
    simp [contraction, minus, plus]
  have contraction_coeff (index : ℕ) : PowerSeries.coeff index contraction =
      Polynomial.C ((PowerSeries.coeff index (halfContraction D left right)) •
        (1 : Oscillator D)) * coverVariable ^ index := by
    rw [contraction_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    simp [embedding, Algebra.smul_def, mul_comm]
  have polynomial_eq (index : ℕ) :
      halfTranslatedPolynomial D left (PowerSeries.coeff index (halfCreationExponential D right)) =
      ∑ coefficient ∈ Finset.range (index + 1),
        Polynomial.C ((PowerSeries.coeff coefficient (halfContraction D left right)) •
          PowerSeries.coeff (index - coefficient) (halfCreationExponential D right)) *
          coverVariable ^ coefficient := by
    have coefficient_eq := congrArg (PowerSeries.coeff index) series_eq
    dsimp only [translated, original] at coefficient_eq
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mul] at coefficient_eq
    change halfTranslatedPolynomial D left
      (PowerSeries.coeff index (halfCreationExponential D right)) = _ at coefficient_eq
    calc
      _ = ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal index,
          Polynomial.C (PowerSeries.coeff pair.1 (halfCreationExponential D right)) *
            PowerSeries.coeff pair.2 contraction := by
        simpa only [PowerSeries.coeff_map] using coefficient_eq
      _ = ∑ coefficient ∈ Finset.range (index + 1),
          Polynomial.C (PowerSeries.coeff (index - coefficient) (halfCreationExponential D right)) *
            PowerSeries.coeff coefficient contraction := by
        rw [← Finset.Nat.sum_antidiagonal_swap,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro coefficient hcoefficient
        rw [contraction_coeff]
        simp only [Algebra.smul_def, map_mul, mul_one]
        ring
  have natural_coeff (index coefficient : ℕ) :
      (halfTranslatedPolynomial D left
        (PowerSeries.coeff index (halfCreationExponential D right))).coeff coefficient =
      if coefficient ≤ index then
        (PowerSeries.coeff coefficient (halfContraction D left right)) •
          PowerSeries.coeff (index - coefficient) (halfCreationExponential D right)
      else 0 := by
    rw [polynomial_eq]
    simp [Polynomial.finsetSum_coeff, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial, coverVariable]
  by_cases hnegative : degree < 0
  · have shifted_negative : degree - (translatedDegree : ℤ) < 0 := by omega
    simp [halfCreationCoeff, hnegative, shifted_negative, halfTranslatedPolynomial]
  · by_cases hbound : translatedDegree ≤ degree.toNat
    · rw [halfCreationCoeff, if_neg hnegative, natural_coeff]
      have shifted_nonnegative : ¬ degree - (translatedDegree : ℤ) < 0 := by omega
      have subtraction : (degree - (translatedDegree : ℤ)).toNat =
          degree.toNat - translatedDegree := by omega
      simp [hbound, halfCreationCoeff, shifted_nonnegative, subtraction]
    · have polynomial_bound := translated_degree_le D left (halfCreationCoeff D right degree)
        degree.toNat (half_creation_coefficient_grading D right degree)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (polynomial_bound.trans_lt (lt_of_not_ge hbound))]
      have shifted_negative : degree - (translatedDegree : ℤ) < 0 := by omega
      simp [halfCreationCoeff, shifted_negative]

end

end D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients

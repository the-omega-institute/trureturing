/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectionCreationExponential
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectionCreationExponential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian coefficients and exact finite jets of the original corrected creation exponential. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockDiagonalFusion
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectionCreationExponential

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCurrentCorrection MvPolynomial
open scoped BigOperators

noncomputable section

/- The correction variable records source weight removed by singleton and pair
   contractions.  Retained oscillator variables keep their original weights. -/
private def correctionWeight (D : LatticeData) (coordinate : Option (Index D)) : ℕ :=
  coordinate.elim 1 (sourceWeight D)

private theorem singleton_homogeneous (D : LatticeData) (charge : Charge D)
    (index : Index D) :
    IsWeightedHomogeneous (correctionWeight D) (singletonPolynomial D charge index)
      (sourceWeight D index) := by
  simpa [singletonPolynomial, correctionWeight] using
    ((isWeightedHomogeneous_X ℂ (correctionWeight D) none).pow
      (sourceWeight D index)).C_mul
        (halfBinomial (sourceWeight D index) *
          (bilinear D (unitCharge D index.1) charge : ℂ))

private theorem pair_homogeneous (D : LatticeData) (first second : Index D) :
    IsWeightedHomogeneous (correctionWeight D) (pairPolynomial D first second)
      (sourceWeight D first + sourceWeight D second) := by
  simpa [pairPolynomial, correctionWeight] using
    ((isWeightedHomogeneous_X ℂ (correctionWeight D) none).pow
      (sourceWeight D first + sourceWeight D second)).C_mul
        (pairScalar (sourceWeight D first) (sourceWeight D second) *
          (D.G first.1 second.1 : ℂ))

private theorem homogeneous_list_sum (D : LatticeData)
    (values : List (CorrectionPolynomial D)) (degree : ℕ)
    (homogeneous : ∀ value ∈ values,
      IsWeightedHomogeneous (correctionWeight D) value degree) :
    IsWeightedHomogeneous (correctionWeight D) values.sum degree := by
  induction values with
  | nil => exact isWeightedHomogeneous_zero ℂ _ _
  | cons value tail previous =>
    simp only [List.sum_cons]
    exact (homogeneous value (by simp)).add
      (previous (by intro other member; exact homogeneous other (by simp [member])))

/- The sum remains a list sum over labelled occurrences: equal axes are never
   deduplicated.  Removing either copy of a repeated axis contributes a term. -/
private theorem correction_word_homogeneous (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) :
    IsWeightedHomogeneous (correctionWeight D) (correctionWord D charge word)
      (wordWeight D word) := by
  have all : ∀ count : ℕ, ∀ word : List (Index D), word.length = count →
      IsWeightedHomogeneous (correctionWeight D) (correctionWord D charge word)
        (wordWeight D word) := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count previous =>
      intro word size
      cases word with
      | nil =>
        simpa [correctionWord, wordWeight] using
          isWeightedHomogeneous_one ℂ (correctionWeight D)
      | cons index tail =>
        rw [correctionWord_matching]
        apply IsWeightedHomogeneous.add
        · have tailHomogeneous := previous tail.length (by
            simp only [List.length_cons] at size
            omega) tail rfl
          have variableHomogeneous : IsWeightedHomogeneous (correctionWeight D)
              (X (some index) : CorrectionPolynomial D) (sourceWeight D index) :=
            isWeightedHomogeneous_X ℂ (correctionWeight D) (some index)
          simpa only [wordWeight, List.map_cons, List.sum_cons] using
            (variableHomogeneous.add (singleton_homogeneous D charge index)).mul
              tailHomogeneous
        · apply homogeneous_list_sum
          intro value member
          obtain ⟨entry, member, rfl⟩ := List.mem_map.mp member
          obtain ⟨entrySize, entryWeight⟩ := labelledRemainders_size D tail entry member
          have remainder := previous entry.2.length (by
            simp only [List.length_cons] at size
            omega) entry.2 rfl
          have degrees : (sourceWeight D index + sourceWeight D entry.1) +
              wordWeight D entry.2 = wordWeight D (index :: tail) := by
            simp only [wordWeight, List.map_cons, List.sum_cons] at *
            omega
          simpa only [degrees] using (pair_homogeneous D index entry.1).mul remainder
  exact all word.length word rfl

private theorem correction_lift_homogeneous (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (degree : ℕ)
    (homogeneous : IsWeightedHomogeneous (sourceWeight D) polynomial degree) :
    IsWeightedHomogeneous (correctionWeight D) (correctionLift D charge polynomial)
      degree := by
  classical
  rw [polynomial.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro exponent member
  have sourceDegree := homogeneous (mem_support_iff.mp member)
  have scale : monomial exponent (coeff exponent polynomial) =
      coeff exponent polynomial • monomial exponent 1 := by
    simp [smul_monomial]
  rw [scale, map_smul]
  apply (weightedHomogeneousSubmodule ℂ (correctionWeight D) degree).smul_mem
  have basis := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => correctionWord D charge
      (LatticeAllStateField.occurrences D exponent)) exponent
  change correctionLift D charge (monomial exponent 1) = _ at basis
  rw [basis]
  simpa only [wordWeight_occurrences, sourceDegree] using
    correction_word_homogeneous D charge (LatticeAllStateField.occurrences D exponent)

private theorem correction_weight_split (D : LatticeData)
    (exponent : Index D →₀ ℕ) (shift : ℕ) :
    Finsupp.weight (correctionWeight D) (exponent.optionElim shift) =
      shift + Finsupp.weight (sourceWeight D) exponent := by
  simpa [Finsupp.weight_apply, correctionWeight] using
    Finsupp.sum_option_index_smul (exponent.optionElim shift) (correctionWeight D)

private theorem occurrence_count_le_weight (D : LatticeData)
    (exponent : Index D →₀ ℕ) :
    exponent.sum (fun _ count => count) ≤ Finsupp.weight (sourceWeight D) exponent := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  apply Finset.sum_le_sum
  intro index member
  apply Nat.le_mul_of_pos_right
  exact Nat.succ_pos index.2

/- Every bound is a consequence of the original coefficient degree.  In
   particular, an axis (i,m-1) occurring before correction has 1 ≤ m ≤ n.
   After correction the residual weight is exactly n-shift, rather than merely
   bounded by n.  The final equality is a finite, literal Corr reconstruction. -/
theorem creation_corr_finite_coefficient (D : LatticeData)
    (charge sourceCharge : Charge D) (degree : ℕ) :
    (∀ exponent : Index D →₀ ℕ,
      coeff exponent (creationCoeff D sourceCharge (degree : ℤ)) ≠ 0 →
        Finsupp.weight (sourceWeight D) exponent = degree ∧
        exponent.sum (fun _ count => count) ≤ degree ∧
        ∀ index ∈ exponent.support, sourceWeight D index ≤ degree) ∧
    (∀ (shift : ℕ) (exponent : Index D →₀ ℕ),
      coeff exponent (Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) shift) ≠ 0 →
        Finsupp.weight (sourceWeight D) exponent + shift = degree ∧
        exponent.sum (fun _ count => count) + shift ≤ degree ∧
        ∀ index ∈ exponent.support, sourceWeight D index + shift ≤ degree) ∧
    Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) =
      ∑ shift ∈ Finset.range (degree + 1),
        Finsupp.single shift
          (Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) shift) := by
  classical
  have sourceHomogeneous : IsWeightedHomogeneous (sourceWeight D)
      (creationCoeff D sourceCharge (degree : ℤ)) degree := by
    simpa only [oscillatorWeight, sourceWeight, Int.toNat_natCast] using
      (actual_creation_coefficient_transport D 0 sourceCharge).1 (degree : ℤ)
  have correctedHomogeneous := correction_lift_homogeneous D charge
    (creationCoeff D sourceCharge (degree : ℤ)) degree sourceHomogeneous
  have correctedDegree (shift : ℕ) (exponent : Index D →₀ ℕ)
      (nonzero : coeff exponent
        (Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) shift) ≠ 0) :
      Finsupp.weight (sourceWeight D) exponent + shift = degree := by
    have liftedNonzero : coeff (exponent.optionElim shift)
        (correctionLift D charge (creationCoeff D sourceCharge (degree : ℤ))) ≠ 0 := by
      simpa only [Corr, correctionPolynomial, correctionLift, LinearMap.comp_apply,
        AlgEquiv.toLinearMap_apply, shiftCoefficients, LinearMap.coe_mk,
        AddHom.coe_mk, Polynomial.toFinsupp_apply, optionEquivLeft_coeff_coeff] using nonzero
    have conserved := correctedHomogeneous liftedNonzero
    rw [correction_weight_split] at conserved
    omega
  constructor
  · intro exponent nonzero
    have conserved := sourceHomogeneous nonzero
    refine ⟨conserved, ?_, ?_⟩
    · exact (occurrence_count_le_weight D exponent).trans_eq conserved
    · intro index member
      exact (Finsupp.le_weight_of_ne_zero' (sourceWeight D)
        (Finsupp.mem_support_iff.mp member)).trans_eq conserved
  · constructor
    · intro shift exponent nonzero
      have conserved := correctedDegree shift exponent nonzero
      refine ⟨conserved, ?_, ?_⟩
      · have bounded := occurrence_count_le_weight D exponent
        omega
      · intro index member
        have bounded := Finsupp.le_weight_of_ne_zero' (sourceWeight D)
          (Finsupp.mem_support_iff.mp member)
        omega
    · apply Finsupp.ext
      intro shift
      by_cases inside : shift < degree + 1
      · simp [Finsupp.single_apply, inside]
      · have zero : Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) shift = 0 := by
          apply MvPolynomial.ext
          intro exponent
          by_contra nonzero
          have actualNonzero : coeff exponent
              (Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) shift) ≠ 0 := by
            simpa only [coeff_zero] using nonzero
          have conserved := correctedDegree shift exponent actualNonzero
          omega
        simp [Finsupp.single_apply, inside, zero]

/- Coefficientwise linear maps preserve finite Cauchy sums, but need not
   preserve products.  In particular correctionLift is used only linearly. -/
private def seriesLinear {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (linear : A →ₗ[ℂ] B) :
    PowerSeries A →ₗ[ℂ] PowerSeries B where
  toFun series := PowerSeries.mk fun degree => linear (PowerSeries.coeff degree series)
  map_add' first second := by
    apply PowerSeries.ext
    intro degree
    simp
  map_smul' scalar series := by
    apply PowerSeries.ext
    intro degree
    simp

@[simp] private theorem coeff_seriesLinear {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (linear : A →ₗ[ℂ] B)
    (series : PowerSeries A) (degree : ℕ) :
    PowerSeries.coeff degree (seriesLinear linear series) =
      linear (PowerSeries.coeff degree series) := rfl

private theorem derivative_seriesLinear {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (linear : A →ₗ[ℂ] B) (series : PowerSeries A) :
    PowerSeries.derivative B (seriesLinear linear series) =
      seriesLinear linear (PowerSeries.derivative A series) := by
  apply PowerSeries.ext
  intro degree
  simp only [PowerSeries.coeff_derivative, coeff_seriesLinear]
  calc
    linear (PowerSeries.coeff (degree + 1) series) * (degree + 1 : B) =
        (degree + 1) • linear (PowerSeries.coeff (degree + 1) series) := by
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ = linear ((degree + 1) • PowerSeries.coeff (degree + 1) series) := by
      rw [map_nsmul]
    _ = linear (PowerSeries.coeff (degree + 1) series * (degree + 1 : A)) := by
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

private def seriesDerivation {R : Type*} [CommRing R] [Algebra ℂ R]
    (delta : Derivation ℂ R R) :
    Derivation ℂ (PowerSeries R) (PowerSeries R) where
  toLinearMap := seriesLinear delta.toLinearMap
  map_one_eq_zero' := by
    apply PowerSeries.ext
    intro degree
    simp [seriesLinear, apply_ite]
  leibniz' first second := by
    change seriesLinear delta.toLinearMap (first * second) =
      first * seriesLinear delta.toLinearMap second +
        second * seriesLinear delta.toLinearMap first
    rw [mul_comm second (seriesLinear delta.toLinearMap first)]
    apply PowerSeries.ext
    intro degree
    simp only [coeff_seriesLinear, PowerSeries.coeff_mul, map_sum,
      map_add, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul,
      Finset.sum_add_distrib]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;>
      intro pair member <;> ring

private theorem exp_subst_constant {R : Type*} [CommRing R] [Algebra ℚ R]
    (source : PowerSeries R) (zero : PowerSeries.constantCoeff source = 0) :
    PowerSeries.coeff 0 ((PowerSeries.exp R).subst source) = 1 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' zero),
    finsum_eq_single _ 0]
  · simp
  · intro degree nonzero
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, zero]
    simp [nonzero]

private theorem exp_subst_derivative {R : Type*} [CommRing R] [Algebra ℚ R]
    (source : PowerSeries R) (zero : PowerSeries.constantCoeff source = 0) :
    PowerSeries.derivative R ((PowerSeries.exp R).subst source) =
      (PowerSeries.exp R).subst source * PowerSeries.derivative R source := by
  rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' zero),
    PowerSeries.derivative_exp]

/- This chain rule is for a derivation of the coefficient ring, rather than
   differentiation in an occurrence-count variable.  Both series retain t. -/
private theorem coefficient_derivation_exp {R : Type*} [CommRing R]
    [Algebra ℂ R] [Algebra ℚ R] [IsAddTorsionFree R]
    (delta : Derivation ℂ R R) (source : PowerSeries R)
    (zero : PowerSeries.constantCoeff source = 0) :
    seriesDerivation delta ((PowerSeries.exp R).subst source) =
      (PowerSeries.exp R).subst source * seriesDerivation delta source := by
  let exponential := (PowerSeries.exp R).subst source
  let lifted := seriesDerivation delta
  have exponentialEquation := exp_subst_derivative source zero
  have commute (series : PowerSeries R) :
      PowerSeries.derivative R (lifted series) =
        lifted (PowerSeries.derivative R series) :=
    derivative_seriesLinear delta.toLinearMap series
  have differenceEquation : PowerSeries.derivative R
      (lifted exponential - exponential * lifted source) =
      (lifted exponential - exponential * lifted source) *
        PowerSeries.derivative R source := by
    rw [map_sub, commute, exponentialEquation]
    simp only [Derivation.leibniz, smul_eq_mul, exponentialEquation, commute]
    ring
  have differenceZero : PowerSeries.coeff 0
      (lifted exponential - exponential * lifted source) = 0 := by
    have sourceZero : PowerSeries.coeff 0 source = 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using zero
    have exponentialZero : PowerSeries.coeff 0 exponential = 1 :=
      exp_subst_constant source zero
    simp [PowerSeries.coeff_mul, lifted, seriesDerivation, seriesLinear,
      exponentialZero, sourceZero]
  have unique := (originalCreationSupplier% solution_unique)
    (lifted exponential - exponential * lifted source) 0
    (PowerSeries.derivative R source) differenceEquation (by simp)
    (by simpa using differenceZero)
  exact sub_eq_zero.mp unique

private def originalLinearSource (D : LatticeData) (charge sourceCharge : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.mk fun degree => (degree : ℂ)⁻¹ •
    ∑ i : Fin D.rank, (sourceCharge i : ℂ) •
      (X (some (i, degree - 1)) + singletonPolynomial D charge (i, degree - 1))

private def axisPairSource (D : LatticeData) (sourceCharge : Charge D) (axis : Index D) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.mk fun degree => (degree : ℂ)⁻¹ •
    ∑ j : Fin D.rank, (sourceCharge j : ℂ) • pairPolynomial D axis (j, degree - 1)

private def pairMoment (D : LatticeData) (sourceCharge : Charge D) (first second : ℕ) :
    CorrectionPolynomial D :=
  ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    ((sourceCharge i : ℂ) * (sourceCharge j : ℂ)) •
      pairPolynomial D (i, first - 1) (j, second - 1)

private def originalPairSource (D : LatticeData) (sourceCharge : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.mk fun degree =>
    ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
      ((pair.1 : ℂ)⁻¹ * (pair.2 : ℂ)⁻¹) • pairMoment D sourceCharge pair.1 pair.2

/- Inverse zero is zero in ℂ, so the zero-index summands below vanish.
   The remaining terms are literally the m,l ≥ 1 terms of G_c,a(t), with
   coefficients 1/m and 1/(2*m*l), and the original pairPolynomial. -/
def originalGaussianDriver (D : LatticeData) (charge sourceCharge : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  originalLinearSource D charge sourceCharge + (1 / 2 : ℂ) • originalPairSource D sourceCharge

private def pairDriver (D : LatticeData) (sourceCharge : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.mk fun degree =>
    ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
      ∑ i : Fin D.rank, (sourceCharge i : ℂ) •
        PowerSeries.coeff pair.2 (axisPairSource D sourceCharge (i, pair.1))

private theorem original_driver_zero (D : LatticeData) (charge sourceCharge : Charge D) :
    PowerSeries.constantCoeff (originalGaussianDriver D charge sourceCharge) = 0 := by
  simp [originalGaussianDriver, originalLinearSource, originalPairSource,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem pair_moment_symmetric (D : LatticeData) (sourceCharge : Charge D)
    (first second : ℕ) :
    pairMoment D sourceCharge first second = pairMoment D sourceCharge second first := by
  classical
  unfold pairMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i member
  apply Finset.sum_congr rfl
  intro j member
  rw [pair_symmetric]
  congr 1
  ring

private theorem pair_driver_coeff (D : LatticeData) (sourceCharge : Charge D) (degree : ℕ) :
    PowerSeries.coeff degree (pairDriver D sourceCharge) =
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
        (pair.2 : ℂ)⁻¹ • pairMoment D sourceCharge (pair.1 + 1) pair.2 := by
  classical
  simp only [pairDriver, axisPairSource, PowerSeries.coeff_mk, pairMoment,
    Nat.add_sub_cancel, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro pair member
  apply Finset.sum_congr rfl
  intro i member
  apply Finset.sum_congr rfl
  intro j member
  congr 1
  ring

private theorem original_pair_derivative (D : LatticeData) (sourceCharge : Charge D) :
    PowerSeries.derivative (CorrectionPolynomial D) (originalPairSource D sourceCharge) =
      (2 : ℂ) • pairDriver D sourceCharge := by
  classical
  apply PowerSeries.ext
  intro degree
  simp only [PowerSeries.coeff_derivative, originalPairSource, PowerSeries.coeff_mk,
    PowerSeries.coeff_smul]
  rw [mul_comm, show (degree + 1 : CorrectionPolynomial D) =
      algebraMap ℂ (CorrectionPolynomial D) (degree + 1 : ℂ) by simp,
    ← Algebra.smul_def, Finset.smul_sum]
  let firstTerm := fun pair : ℕ × ℕ =>
    ((pair.1 : ℂ) * (pair.1 : ℂ)⁻¹ * (pair.2 : ℂ)⁻¹) •
      pairMoment D sourceCharge pair.1 pair.2
  let secondTerm := fun pair : ℕ × ℕ =>
    ((pair.1 : ℂ)⁻¹ * (pair.2 : ℂ) * (pair.2 : ℂ)⁻¹) •
      pairMoment D sourceCharge pair.1 pair.2
  have split : (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal (degree + 1),
      (degree + 1 : ℂ) •
        (((pair.1 : ℂ)⁻¹ * (pair.2 : ℂ)⁻¹) •
          pairMoment D sourceCharge pair.1 pair.2)) =
      (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal (degree + 1), firstTerm pair) +
        ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal (degree + 1), secondTerm pair := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pair member
    have total : (degree + 1 : ℂ) = (pair.1 : ℂ) + (pair.2 : ℂ) := by
      exact_mod_cast (Finset.HasAntidiagonal.mem_antidiagonal.mp member).symm
    simp only [firstTerm, secondTerm, total, smul_smul, ← add_smul]
    congr 1
    ring
  rw [split]
  have swap : (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal (degree + 1), secondTerm pair) =
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal (degree + 1), firstTerm pair := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    apply Finset.sum_congr rfl
    intro pair member
    dsimp [firstTerm, secondTerm]
    rw [pair_moment_symmetric]
    congr 1
    ring
  rw [swap]
  have first : (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal (degree + 1), firstTerm pair) =
      PowerSeries.coeff degree (pairDriver D sourceCharge) := by
    rw [Finset.Nat.sum_antidiagonal_succ, pair_driver_coeff]
    simp only [firstTerm, Nat.cast_zero, zero_mul, zero_smul, zero_add]
    apply Finset.sum_congr rfl
    intro pair member
    have nonzero : (pair.1 + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero pair.1
    simp [firstTerm, mul_inv_cancel₀ nonzero]
  rw [first]
  simp only [two_smul]

private theorem original_linear_derivative_coeff (D : LatticeData)
    (charge sourceCharge : Charge D) (degree : ℕ) :
    PowerSeries.coeff degree
        (PowerSeries.derivative (CorrectionPolynomial D)
          (originalLinearSource D charge sourceCharge)) =
      ∑ i : Fin D.rank, (sourceCharge i : ℂ) •
        (X (some (i, degree)) + singletonPolynomial D charge (i, degree)) := by
  rw [PowerSeries.coeff_derivative]
  simp only [originalLinearSource, PowerSeries.coeff_mk, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  rw [mul_comm, show (degree + 1 : CorrectionPolynomial D) =
      algebraMap ℂ (CorrectionPolynomial D) (degree + 1 : ℂ) by simp,
    ← Algebra.smul_def, smul_smul]
  rw [mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero degree), one_smul]

private theorem original_driver_derivative (D : LatticeData)
    (charge sourceCharge : Charge D) :
    PowerSeries.derivative (CorrectionPolynomial D) (originalGaussianDriver D charge sourceCharge) =
      PowerSeries.derivative (CorrectionPolynomial D) (originalLinearSource D charge sourceCharge) +
        pairDriver D sourceCharge := by
  have scale : PowerSeries.derivative (CorrectionPolynomial D)
      ((1 / 2 : ℂ) • originalPairSource D sourceCharge) =
      (1 / 2 : ℂ) • PowerSeries.derivative (CorrectionPolynomial D)
        (originalPairSource D sourceCharge) := by
    apply PowerSeries.ext
    intro degree
    simp [PowerSeries.coeff_derivative, smul_mul_assoc]
  rw [originalGaussianDriver, map_add, scale, original_pair_derivative, smul_smul]
  norm_num

private theorem original_driver_pair_derivation (D : LatticeData)
    (charge sourceCharge : Charge D) (axis : Index D) :
    seriesDerivation (pairDerivation D axis) (originalGaussianDriver D charge sourceCharge) =
      axisPairSource D sourceCharge axis := by
  classical
  have variable (other : Index D) :
      pairDerivation D axis (X (some other) + singletonPolynomial D charge other) =
        pairPolynomial D axis other := by
    simp [pairDerivation, singletonPolynomial, mkDerivation_X,
      Derivation.leibniz, smul_eq_mul, Derivation.leibniz_pow]
  have quadraticZero (degree : ℕ) :
      pairDerivation D axis (PowerSeries.coeff degree (originalPairSource D sourceCharge)) = 0 := by
    simp [originalPairSource, pairMoment, pairDerivation_pair]
  apply PowerSeries.ext
  intro degree
  simp only [seriesDerivation, coeff_seriesLinear, originalGaussianDriver,
    map_add, PowerSeries.coeff_smul, map_smul, quadraticZero, smul_zero, add_zero,
    originalLinearSource, axisPairSource, PowerSeries.coeff_mk, map_sum, variable]

/- Each iterated Cauchy sum has three nonnegative degrees of fixed total.
   Swapping the first two degrees is a bijection of that finite set. -/
private theorem cauchy_swap_first_two {R : Type*} [AddCommMonoid R]
    (degree : ℕ) (term : ℕ → ℕ → ℕ → R) :
    (∑ outer ∈ Finset.HasAntidiagonal.antidiagonal degree,
      ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.2,
        term outer.1 inner.1 inner.2) =
    ∑ outer ∈ Finset.HasAntidiagonal.antidiagonal degree,
      ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.2,
        term inner.1 outer.1 inner.2 := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun entry _ =>
    (⟨(entry.2.1, entry.1.1 + entry.2.2), (entry.1.1, entry.2.2)⟩ :
      (pair : ℕ × ℕ) × (ℕ × ℕ)))
  · intro entry member
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at member ⊢
    omega
  · intro first firstMember second secondMember equal
    have firstTotal := firstMember
    have secondTotal := secondMember
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at
      firstTotal secondTotal
    have equalFirst : first.2.1 = second.2.1 := congrArg (fun entry => entry.1.1) equal
    have equalSecond : first.1.1 = second.1.1 := congrArg (fun entry => entry.2.1) equal
    have equalThird : first.2.2 = second.2.2 := congrArg (fun entry => entry.2.2) equal
    have outerEqual : first.1 = second.1 := by
      apply Prod.ext <;> dsimp at * <;> omega
    have innerEqual : first.2 = second.2 := Prod.ext equalFirst equalThird
    exact Sigma.ext outerEqual (by simpa using innerEqual)
  · intro entry member
    refine ⟨⟨(entry.2.1, entry.1.1 + entry.2.2), (entry.1.1, entry.2.2)⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at member ⊢
      omega
    · have total := member
      simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at total
      apply Sigma.ext
      · apply Prod.ext <;> dsimp <;> omega
      · simp
  · intro entry member
    rfl

private def creationEvolution (D : LatticeData) (charge sourceCharge : Charge D)
    (series : PowerSeries (CorrectionPolynomial D)) (degree : ℕ) : CorrectionPolynomial D :=
  ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
    ∑ i : Fin D.rank, (sourceCharge i : ℂ) •
      insertion D charge (i, pair.1) (PowerSeries.coeff pair.2 series)

private def originalGaussian (D : LatticeData) (charge sourceCharge : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  (PowerSeries.exp (CorrectionPolynomial D)).subst
    (originalGaussianDriver D charge sourceCharge)

private theorem gaussian_pair_eigen (D : LatticeData) (charge sourceCharge : Charge D)
    (axis : Index D) (degree : ℕ) :
    pairDerivation D axis (PowerSeries.coeff degree (originalGaussian D charge sourceCharge)) =
      PowerSeries.coeff degree
        (originalGaussian D charge sourceCharge * axisPairSource D sourceCharge axis) := by
  have chain := coefficient_derivation_exp (pairDerivation D axis)
    (originalGaussianDriver D charge sourceCharge) (original_driver_zero D charge sourceCharge)
  rw [original_driver_pair_derivation] at chain
  exact congrArg (PowerSeries.coeff degree) chain

private theorem gaussian_pair_convolution (D : LatticeData) (charge sourceCharge : Charge D)
    (degree : ℕ) :
    PowerSeries.coeff degree (originalGaussian D charge sourceCharge * pairDriver D sourceCharge) =
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
        ∑ i : Fin D.rank, (sourceCharge i : ℂ) •
          pairDerivation D (i, pair.1)
            (PowerSeries.coeff pair.2 (originalGaussian D charge sourceCharge)) := by
  classical
  simp only [PowerSeries.coeff_mul, pairDriver, PowerSeries.coeff_mk,
    gaussian_pair_eigen, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
  rw [cauchy_swap_first_two]
  apply Finset.sum_congr rfl
  intro outer member
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i member
  rw [Finset.smul_sum]

private theorem gaussian_evolution (D : LatticeData) (charge sourceCharge : Charge D)
    (degree : ℕ) :
    (degree + 1) • PowerSeries.coeff (degree + 1) (originalGaussian D charge sourceCharge) =
      creationEvolution D charge sourceCharge (originalGaussian D charge sourceCharge) degree := by
  classical
  have equation := exp_subst_derivative (originalGaussianDriver D charge sourceCharge)
    (original_driver_zero D charge sourceCharge)
  rw [original_driver_derivative, mul_add] at equation
  have coefficient := congrArg (PowerSeries.coeff degree) equation
  rw [PowerSeries.coeff_derivative, map_add, gaussian_pair_convolution] at coefficient
  have linear : PowerSeries.coeff degree
      (originalGaussian D charge sourceCharge *
        PowerSeries.derivative (CorrectionPolynomial D)
          (originalLinearSource D charge sourceCharge)) =
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
        ∑ i : Fin D.rank, (sourceCharge i : ℂ) •
          ((X (some (i, pair.1)) + singletonPolynomial D charge (i, pair.1)) *
            PowerSeries.coeff pair.2 (originalGaussian D charge sourceCharge)) := by
    rw [mul_comm, PowerSeries.coeff_mul]
    simp only [original_linear_derivative_coeff, Finset.sum_mul, smul_mul_assoc]
  rw [linear, ← Finset.sum_add_distrib] at coefficient
  simp only [creationEvolution, insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  simpa only [originalGaussian, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    mul_comm] using coefficient

private theorem original_creation_derivative_coeff (D : LatticeData)
    (sourceCharge : Charge D) (degree : ℕ) :
    PowerSeries.coeff degree
        (PowerSeries.derivative (Oscillator D) (creationSeries D sourceCharge)) =
      ∑ i : Fin D.rank, (sourceCharge i : ℂ) • (X (i, degree) : Oscillator D) := by
  rw [PowerSeries.coeff_derivative]
  simp only [creationSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceDIte,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [mul_comm, show (degree + 1 : Oscillator D) =
      algebraMap ℂ (Oscillator D) (degree + 1 : ℂ) by simp,
    ← Algebra.smul_def, smul_smul]
  rw [mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero degree), one_smul]

private theorem lifted_creation_evolution (D : LatticeData)
    (charge sourceCharge : Charge D) (degree : ℕ) :
    (degree + 1) • PowerSeries.coeff (degree + 1)
        (seriesLinear (correctionLift D charge) (creationExponential D sourceCharge)) =
      creationEvolution D charge sourceCharge
        (seriesLinear (correctionLift D charge) (creationExponential D sourceCharge)) degree := by
  classical
  have zero : PowerSeries.constantCoeff (creationSeries D sourceCharge) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have equation := exp_subst_derivative (creationSeries D sourceCharge) zero
  rw [mul_comm] at equation
  have recurrence := congrArg (PowerSeries.coeff degree) equation
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at recurrence
  have scale : PowerSeries.coeff (degree + 1)
        ((PowerSeries.exp (Oscillator D)).subst (creationSeries D sourceCharge)) *
        (degree + 1 : Oscillator D) =
      (degree + 1) • PowerSeries.coeff (degree + 1)
        ((PowerSeries.exp (Oscillator D)).subst (creationSeries D sourceCharge)) := by
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [scale] at recurrence
  have mapped := congrArg (correctionLift D charge) recurrence
  simp only [original_creation_derivative_coeff, Finset.sum_mul,
    smul_mul_assoc, map_sum, map_smul, map_nsmul,
    show ∀ (axis : Index D) (polynomial : Oscillator D),
      correctionLift D charge (X axis * polynomial) =
        insertion D charge axis (correctionLift D charge polynomial) from
      fun axis polynomial => by rw [mul_comm, correctionLift_X_mul]] at mapped
  simpa only [creationEvolution, coeff_seriesLinear, creationExponential] using mapped

private theorem lifted_creation_unit (D : LatticeData) (charge : Charge D) :
    correctionLift D charge 1 = 1 := by
  have basis := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)) 0
  simpa [correctionLift, LatticeAllStateField.occurrences, correctionWord] using basis

private theorem original_creation_gaussian_series (D : LatticeData)
    (charge sourceCharge : Charge D) :
    seriesLinear (correctionLift D charge) (creationExponential D sourceCharge) =
      originalGaussian D charge sourceCharge := by
  classical
  apply PowerSeries.ext
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree previous =>
    cases degree with
    | zero =>
      have zero : PowerSeries.constantCoeff (creationSeries D sourceCharge) = 0 := by
        simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [coeff_seriesLinear, creationExponential,
        exp_subst_constant _ zero, lifted_creation_unit, originalGaussian,
        exp_subst_constant _ (original_driver_zero D charge sourceCharge)]
    | succ degree =>
      have first := lifted_creation_evolution D charge sourceCharge degree
      have second := gaussian_evolution D charge sourceCharge degree
      have equalEvolution : creationEvolution D charge sourceCharge
          (seriesLinear (correctionLift D charge) (creationExponential D sourceCharge)) degree =
          creationEvolution D charge sourceCharge (originalGaussian D charge sourceCharge) degree := by
        unfold creationEvolution
        apply Finset.sum_congr rfl
        intro pair member
        have total := Finset.HasAntidiagonal.mem_antidiagonal.mp member
        rw [previous pair.2 (by omega)]
      have equal := first.trans (equalEvolution.trans second.symm)
      exact (smul_right_inj (Nat.succ_ne_zero degree)).mp equal

/- Since the constant term vanishes, k occurrences have t-order at least k.
   Thus the coefficient of t^n sees only k ≤ n and the jet through degree n.
   This is a derived bound for the actual exponential, not a cutoff premise. -/
private theorem exp_coefficient_finite_jet {R : Type*} [CommRing R] [Algebra ℚ R]
    (source : PowerSeries R) (zero : PowerSeries.constantCoeff source = 0) (degree : ℕ) :
    PowerSeries.coeff degree ((PowerSeries.exp R).subst source) =
      ∑ count ∈ Finset.range (degree + 1),
        PowerSeries.coeff count (PowerSeries.exp R) •
          ((PowerSeries.trunc (degree + 1) source) ^ count).coeff degree := by
  classical
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' zero)]
  have support : Function.support (fun count : ℕ =>
      PowerSeries.coeff count (PowerSeries.exp R) • PowerSeries.coeff degree (source ^ count)) ⊆
      Finset.range (degree + 1) := by
    intro count nonzero
    by_contra outside
    have excess : degree < count := by
      have bound : ¬ count < degree + 1 := by
        simpa only [Finset.mem_coe, Finset.mem_range] using outside
      omega
    have vanished : PowerSeries.coeff degree (source ^ count) = 0 :=
      PowerSeries.coeff_of_lt_order degree
        (lt_of_lt_of_le (by exact_mod_cast excess)
          (PowerSeries.le_order_pow_of_constantCoeff_eq_zero count zero))
    exact nonzero (by rw [vanished, smul_zero])
  rw [finsum_eq_sum_of_support_subset _ support]
  apply Finset.sum_congr rfl
  intro count member
  congr 1
  have jet := congrArg (fun polynomial : Polynomial R => polynomial.coeff degree)
    (PowerSeries.trunc_trunc_pow source (degree + 1) count)
  simpa only [PowerSeries.coeff_trunc, Nat.lt_succ_self, if_true,
    ← Polynomial.coe_pow, Polynomial.coeff_coe] using jet.symm

/- P_n is the coefficient of the original creationExponential.  The second
   equality extracts the original correction variable, with no replacement
   of Corr or of its labelled pair multiplicities.  The final two equalities
   give the finite jets of that same source and that same Gaussian. -/
theorem original_creation_coefficient_gaussian (D : LatticeData)
    (charge sourceCharge : Charge D) (degree shift : ℕ) :
    correctionLift D charge (creationCoeff D sourceCharge (degree : ℤ)) =
        PowerSeries.coeff degree
          ((PowerSeries.exp (CorrectionPolynomial D)).subst
            (originalGaussianDriver D charge sourceCharge)) ∧
    Corr D charge (creationCoeff D sourceCharge (degree : ℤ)) shift =
        (optionEquivLeft ℂ (Index D)
          (PowerSeries.coeff degree
            ((PowerSeries.exp (CorrectionPolynomial D)).subst
              (originalGaussianDriver D charge sourceCharge)))).coeff shift ∧
    creationCoeff D sourceCharge (degree : ℤ) =
        ∑ count ∈ Finset.range (degree + 1),
          PowerSeries.coeff count (PowerSeries.exp (Oscillator D)) •
            ((PowerSeries.trunc (degree + 1) (creationSeries D sourceCharge)) ^ count).coeff degree ∧
    correctionLift D charge (creationCoeff D sourceCharge (degree : ℤ)) =
        ∑ count ∈ Finset.range (degree + 1),
          PowerSeries.coeff count (PowerSeries.exp (CorrectionPolynomial D)) •
            ((PowerSeries.trunc (degree + 1)
              (originalGaussianDriver D charge sourceCharge)) ^ count).coeff degree := by
  have equality := congrArg (PowerSeries.coeff degree)
    (original_creation_gaussian_series D charge sourceCharge)
  have originalCoefficient : creationCoeff D sourceCharge (degree : ℤ) =
      PowerSeries.coeff degree (creationExponential D sourceCharge) := by
    simp [creationCoeff]
  have exactEquality : correctionLift D charge (creationCoeff D sourceCharge (degree : ℤ)) =
      PowerSeries.coeff degree (originalGaussian D charge sourceCharge) := by
    simpa only [originalCoefficient, coeff_seriesLinear] using equality
  refine ⟨exactEquality, ?_, ?_, ?_⟩
  · rw [← exactEquality]
    rfl
  · rw [originalCoefficient]
    exact exp_coefficient_finite_jet (creationSeries D sourceCharge)
      (by simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]) degree
  · rw [exactEquality]
    exact exp_coefficient_finite_jet (originalGaussianDriver D charge sourceCharge)
      (original_driver_zero D charge sourceCharge) degree

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectionCreationExponential

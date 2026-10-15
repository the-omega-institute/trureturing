/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectionCreationExponential
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectionCreationExponential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact residual-weight and occurrence bounds for corrected original creation coefficients. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

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

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectionCreationExponential

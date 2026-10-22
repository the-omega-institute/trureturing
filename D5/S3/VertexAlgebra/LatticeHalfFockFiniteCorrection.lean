/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite symmetric singleton and pair corrections for ordinary lattice states. -/

import D5.S3.VertexAlgebra.LatticeAllStateField
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Binomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

open LatticeGeneratingFieldLocality MvPolynomial
open scoped BigOperators

noncomputable section

def halfBinomial (degree : ℕ) : ℂ :=
  (∏ offset ∈ Finset.range degree, (-1 / 2 - (offset : ℂ))) / (degree.factorial : ℂ)

def pairScalar (first second : ℕ) : ℂ :=
  (first : ℂ) * (second : ℂ) * halfBinomial first * halfBinomial second /
    ((first : ℂ) + (second : ℂ))

def sourceWeight (D : LatticeData) (index : Index D) : ℕ := index.2 + 1

abbrev CorrectionPolynomial (D : LatticeData) := MvPolynomial (Option (Index D)) ℂ

def singletonPolynomial (D : LatticeData) (charge : Charge D) (index : Index D) :
    CorrectionPolynomial D :=
  C (halfBinomial (sourceWeight D index) * (bilinear D (unitCharge D index.1) charge : ℂ)) *
    X none ^ sourceWeight D index

def pairPolynomial (D : LatticeData) (first second : Index D) : CorrectionPolynomial D :=
  C (pairScalar (sourceWeight D first) (sourceWeight D second) * (D.G first.1 second.1 : ℂ)) *
    X none ^ (sourceWeight D first + sourceWeight D second)

def pairDerivation (D : LatticeData) (index : Index D) :
    Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D) :=
  mkDerivation ℂ (fun coordinate : Option (Index D) => coordinate.elim 0 (pairPolynomial D index))

def insertion (D : LatticeData) (charge : Charge D) (index : Index D) :
    Module.End ℂ (CorrectionPolynomial D) :=
  LinearMap.mulLeft ℂ (X (some index) + singletonPolynomial D charge index) +
    (pairDerivation D index).toLinearMap

private theorem pair_symmetric (D : LatticeData) (first second : Index D) :
    pairPolynomial D first second = pairPolynomial D second first := by
  unfold pairPolynomial
  congr 1
  · congr 1
    rw [D.symmetric first.1 second.1]
    unfold pairScalar
    rw [add_comm (sourceWeight D first : ℂ) (sourceWeight D second : ℂ)]
    ring
  · rw [Nat.add_comm (sourceWeight D first) (sourceWeight D second)]

theorem pairDerivation_shift (D : LatticeData) (index : Index D) (degree : ℕ) :
    pairDerivation D index (X none ^ degree) = 0 := by
  simp [pairDerivation, Derivation.leibniz_pow, mkDerivation_X]

theorem pairDerivation_pair (D : LatticeData) (index first second : Index D) :
    pairDerivation D index (pairPolynomial D first second) = 0 := by
  simp [pairPolynomial, Derivation.leibniz, smul_eq_mul,
    pairDerivation, mkDerivation_X, MvPolynomial.derivation_C]

private theorem pairDerivation_singleton (D : LatticeData) (charge : Charge D)
    (index other : Index D) :
    pairDerivation D index (singletonPolynomial D charge other) = 0 := by
  simp [singletonPolynomial, Derivation.leibniz, smul_eq_mul,
    pairDerivation, mkDerivation_X, MvPolynomial.derivation_C]

private theorem pairDerivation_variable (D : LatticeData) (index other : Index D) :
    pairDerivation D index (X (some other)) = pairPolynomial D index other := by
  simp [pairDerivation, mkDerivation_X]

private theorem pairDerivation_commute (D : LatticeData) (first second : Index D)
    (polynomial : CorrectionPolynomial D) :
    pairDerivation D first (pairDerivation D second polynomial) =
      pairDerivation D second (pairDerivation D first polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp
  | add left right inductionLeft inductionRight =>
    simp only [map_add, inductionLeft, inductionRight]
  | mul_X polynomial coordinate inductionProof =>
    have shift : ∀ index : Index D, pairDerivation D index (X none) = 0 := by
      intro index
      simpa using pairDerivation_shift D index 1
    cases coordinate with
    | none =>
      simp [Derivation.leibniz, smul_eq_mul, shift, inductionProof]
    | some other =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add,
        pairDerivation_variable, pairDerivation_pair, mul_zero, add_zero]
      rw [inductionProof]
      ring

theorem insertion_commute (D : LatticeData) (charge : Charge D) (first second : Index D)
    (polynomial : CorrectionPolynomial D) :
    insertion D charge first (insertion D charge second polynomial) =
      insertion D charge second (insertion D charge first polynomial) := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, Derivation.leibniz, smul_eq_mul,
    pairDerivation_singleton, pairDerivation_variable, add_zero]
  rw [pairDerivation_commute, pair_symmetric]
  ring

def correctionWord (D : LatticeData) (charge : Charge D) :
    List (Index D) → CorrectionPolynomial D
  | [] => 1
  | index :: tail => insertion D charge index (correctionWord D charge tail)

theorem correctionWord_permutation (D : LatticeData) (charge : Charge D)
    (first second : List (Index D)) (permutation : first.Perm second) :
    correctionWord D charge first = correctionWord D charge second := by
  induction permutation with
  | nil => rfl
  | cons index permutation inductionProof => simp only [correctionWord, inductionProof]
  | swap first second tail =>
    first
    | exact insertion_commute D charge second first (correctionWord D charge tail)
    | exact insertion_commute D charge first second (correctionWord D charge tail)
  | trans first second inductionFirst inductionSecond =>
    exact inductionFirst.trans inductionSecond

def labelledRemainders (D : LatticeData) :
    List (Index D) → List (Index D × List (Index D))
  | [] => []
  | index :: tail => (index, tail) ::
      (labelledRemainders D tail).map (fun entry => (entry.1, index :: entry.2))

def wordWeight (D : LatticeData) (word : List (Index D)) : ℕ :=
  (word.map (sourceWeight D)).sum

private theorem labelledRemainders_size (D : LatticeData) (word : List (Index D))
    (entry : Index D × List (Index D)) (member : entry ∈ labelledRemainders D word) :
    entry.2.length + 1 = word.length ∧
      wordWeight D entry.2 + sourceWeight D entry.1 = wordWeight D word := by
  induction word generalizing entry with
  | nil => simp [labelledRemainders] at member
  | cons index tail inductionProof =>
    simp only [labelledRemainders, List.mem_cons, List.mem_map] at member
    rcases member with equal | ⟨previous, member, equal⟩
    · subst entry
      simp [wordWeight, Nat.add_comm]
    · subst entry
      obtain ⟨size, weight⟩ := inductionProof previous member
      simp only [List.length_cons, wordWeight, List.map_cons, List.sum_cons] at *
      constructor <;> omega

private theorem pairDerivation_insertion (D : LatticeData) (charge : Charge D)
    (index other : Index D) (polynomial : CorrectionPolynomial D) :
    pairDerivation D index (insertion D charge other polynomial) =
      pairPolynomial D index other * polynomial +
        insertion D charge other (pairDerivation D index polynomial) := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, Derivation.leibniz, smul_eq_mul,
    pairDerivation_variable, pairDerivation_singleton, add_zero]
  rw [pairDerivation_commute]
  ring

private theorem insertion_pair_mul (D : LatticeData) (charge : Charge D)
    (index first second : Index D) (polynomial : CorrectionPolynomial D) :
    insertion D charge index (pairPolynomial D first second * polynomial) =
      pairPolynomial D first second * insertion D charge index polynomial := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul,
    pairDerivation_pair, mul_zero, zero_add]
  ring

theorem pairDerivation_matching (D : LatticeData) (charge : Charge D)
    (index : Index D) (word : List (Index D)) :
    pairDerivation D index (correctionWord D charge word) =
      ((labelledRemainders D word).map (fun entry =>
        pairPolynomial D index entry.1 * correctionWord D charge entry.2)).sum := by
  induction word with
  | nil => simp [correctionWord, labelledRemainders]
  | cons other tail inductionProof =>
    rw [correctionWord, pairDerivation_insertion, inductionProof, map_list_sum]
    simp only [labelledRemainders, List.map_cons, List.map_map, List.sum_cons,
      Function.comp_def, correctionWord, insertion_pair_mul]

theorem correctionWord_matching (D : LatticeData) (charge : Charge D)
    (index : Index D) (word : List (Index D)) :
    correctionWord D charge (index :: word) =
      (X (some index) + singletonPolynomial D charge index) * correctionWord D charge word +
        ((labelledRemainders D word).map (fun entry =>
          pairPolynomial D index entry.1 * correctionWord D charge entry.2)).sum := by
  simp only [correctionWord, insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pairDerivation_matching]

private theorem polynomial_list_degree (D : LatticeData)
    (polynomials : List (Polynomial (Oscillator D)))
    (bound : ℕ) (bounded : ∀ polynomial ∈ polynomials, polynomial.natDegree ≤ bound) :
    polynomials.sum.natDegree ≤ bound := by
  induction polynomials with
  | nil => simp
  | cons polynomial tail inductionProof =>
    simp only [List.sum_cons]
    exact Polynomial.natDegree_add_le_of_degree_le
      (bounded polynomial (by simp)) (inductionProof (by
        intro other member
        exact bounded other (by simp [member])))

theorem correctionWord_shift_bound (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) :
    (optionEquivLeft ℂ (Index D) (correctionWord D charge word)).natDegree ≤
      wordWeight D word := by
  have bound : ∀ count : ℕ, ∀ word : List (Index D), word.length = count →
      (optionEquivLeft ℂ (Index D) (correctionWord D charge word)).natDegree ≤
        wordWeight D word := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count inductionProof =>
      intro word size
      cases word with
      | nil => simp [correctionWord, wordWeight]
      | cons index tail =>
        rw [correctionWord_matching, map_add, map_mul, map_list_sum]
        apply Polynomial.natDegree_add_le_of_degree_le
        · apply Polynomial.natDegree_mul_le.trans
          have tailBound := inductionProof tail.length (by
            simp only [List.length_cons] at size
            omega) tail rfl
          have factorBound : (optionEquivLeft ℂ (Index D)
              (X (some index) + singletonPolynomial D charge index)).natDegree ≤
                sourceWeight D index := by
            rw [map_add]
            apply Polynomial.natDegree_add_le_of_degree_le
            · simp
            · rw [singletonPolynomial, map_mul, map_pow,
                optionEquivLeft_C, optionEquivLeft_X_none]
              exact Polynomial.natDegree_mul_le.trans (by
                simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add,
                  le_refl])
          simpa only [wordWeight, List.map_cons, List.sum_cons] using
            Nat.add_le_add factorBound tailBound
        · apply polynomial_list_degree D
          intro polynomial member
          simp only [List.mem_map] at member
          obtain ⟨previous, member, rfl⟩ := member
          obtain ⟨entry, member, rfl⟩ := member
          rw [map_mul]
          apply Polynomial.natDegree_mul_le.trans
          obtain ⟨entrySize, entryWeight⟩ := labelledRemainders_size D tail entry member
          have remainderBound := inductionProof entry.2.length (by
            simp only [List.length_cons] at size
            omega) entry.2 rfl
          have pairBound : (optionEquivLeft ℂ (Index D)
              (pairPolynomial D index entry.1)).natDegree ≤
                sourceWeight D index + sourceWeight D entry.1 := by
            rw [pairPolynomial, map_mul, map_pow,
              optionEquivLeft_C, optionEquivLeft_X_none]
            exact Polynomial.natDegree_mul_le.trans (by
              simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add,
                le_refl])
          have combined := Nat.add_le_add pairBound remainderBound
          simp only [wordWeight, List.map_cons, List.sum_cons] at *
          omega
  exact bound word.length word rfl

def correctionPolynomial (D : LatticeData) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] Polynomial (Oscillator D) :=
  (optionEquivLeft ℂ (Index D)).toLinearMap.comp
    ((basisMonomials (Index D) ℂ).constr ℂ
      (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)))

def shiftCoefficients (D : LatticeData) :
    Polynomial (Oscillator D) →ₗ[ℂ] (ℕ →₀ Oscillator D) where
  toFun polynomial := polynomial.toFinsupp.coeff
  map_add' first second := rfl
  map_smul' scalar polynomial := rfl

def Corr (D : LatticeData) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] (ℕ →₀ Oscillator D) :=
  (shiftCoefficients D).comp (correctionPolynomial D charge)

theorem Corr_monomial_enumeration (D : LatticeData) (charge : Charge D)
    (exponent : Index D →₀ ℕ) (word : List (Index D))
    (enumeration : word.Perm (LatticeAllStateField.occurrences D exponent)) :
    Corr D charge (monomial exponent 1) = shiftCoefficients D
      (optionEquivLeft ℂ (Index D) (correctionWord D charge word)) := by
  have basis := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)) exponent
  change (((basisMonomials (Index D) ℂ).constr ℂ
      (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)))
      (monomial exponent 1)) = _ at basis
  simp only [Corr, correctionPolynomial, LinearMap.comp_apply]
  change shiftCoefficients D
      (optionEquivLeft ℂ (Index D)
        (((basisMonomials (Index D) ℂ).constr ℂ
          (fun exponent => correctionWord D charge
            (LatticeAllStateField.occurrences D exponent))) (monomial exponent 1))) = _
  rw [basis, ← correctionWord_permutation D charge word _ enumeration]

theorem Corr_one (D : LatticeData) (charge : Charge D) :
    Corr D charge 1 = Finsupp.single 0 1 := by
  have source := Corr_monomial_enumeration D charge 0 [] (by
    simp [LatticeAllStateField.occurrences])
  change Corr D charge 1 = _ at source
  rw [source]
  rw [correctionWord, map_one]
  change (1 : Polynomial (Oscillator D)).toFinsupp.coeff = Finsupp.single 0 1
  rfl

theorem Corr_X_zero (D : LatticeData) (index : Index D) :
    Corr D 0 (X index) = Finsupp.single 0 (X index) := by
  have source := Corr_monomial_enumeration D 0 (Finsupp.single index 1) [index] (by
    simp [LatticeAllStateField.occurrences])
  have corrected : correctionWord D 0 [index] = X (some index) := by
    simp [correctionWord, insertion, singletonPolynomial, bilinear]
  change Corr D 0 (X index) = _ at source
  rw [source, corrected, optionEquivLeft_X_some]
  rfl

private theorem wordWeight_occurrences (D : LatticeData) (exponent : Index D →₀ ℕ) :
    wordWeight D (LatticeAllStateField.occurrences D exponent) =
      Finsupp.weight (sourceWeight D) exponent := by
  classical
  rw [wordWeight, LatticeAllStateField.occurrences, Multiset.sum_map_toList]
  induction exponent using Finsupp.induction with
  | zero => simp
  | single_add index count tail absent nonzero inductionProof =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add,
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_singleton, Multiset.sum_singleton, inductionProof, map_add,
      Finsupp.weight_single]

private theorem correctionPolynomial_shift_bound (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    (correctionPolynomial D charge polynomial).natDegree ≤
      MvPolynomial.weightedTotalDegree (sourceWeight D) polynomial := by
  classical
  conv_lhs => rw [polynomial.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent member
  have monomial : MvPolynomial.monomial exponent (MvPolynomial.coeff exponent polynomial) =
      MvPolynomial.coeff exponent polynomial • MvPolynomial.monomial exponent 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [monomial, map_smul]
  apply (Polynomial.natDegree_smul_le _ _).trans
  have basis := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => correctionWord D charge
      (LatticeAllStateField.occurrences D exponent)) exponent
  change (((basisMonomials (Index D) ℂ).constr ℂ
    (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)))
      (MvPolynomial.monomial exponent 1)) = _ at basis
  change (optionEquivLeft ℂ (Index D)
    (((basisMonomials (Index D) ℂ).constr ℂ
      (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)))
        (MvPolynomial.monomial exponent 1))).natDegree ≤ _
  rw [basis]
  exact (correctionWord_shift_bound D charge _).trans (by
    rw [wordWeight_occurrences]
    exact MvPolynomial.le_weightedTotalDegree (sourceWeight D) member)

theorem Corr_shift_bound (D : LatticeData) (charge : Charge D) (polynomial : Oscillator D)
    (shift : ℕ) (member : shift ∈ (Corr D charge polynomial).support) :
    shift ≤ MvPolynomial.weightedTotalDegree (sourceWeight D) polynomial := by
  have nonzero : (correctionPolynomial D charge polynomial).coeff shift ≠ 0 :=
    Finsupp.mem_support_iff.mp member
  exact (Polynomial.le_natDegree_of_ne_zero nonzero).trans
    (correctionPolynomial_shift_bound D charge polynomial)

end
end D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.insertion_commute
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.correctionWord_permutation
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairDerivation_matching
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.correctionWord_matching
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.correctionWord_shift_bound
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr_one
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr_X_zero
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr_shift_bound

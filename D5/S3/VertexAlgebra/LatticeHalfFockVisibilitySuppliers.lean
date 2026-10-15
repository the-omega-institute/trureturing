/- GID: D5/S3/VertexAlgebra/LatticeHalfFockVisibilitySuppliers
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockVisibilitySuppliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Public exact suppliers for the predecessor visibility boundary used by the original theta modules. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum
import D5.S3.VertexAlgebra.LatticeSugawaraConformal

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockVisibilitySuppliers

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeHalfFock
open D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open D5.S3.VertexAlgebra.LatticeSugawaraConformal
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

theorem L_zero_X_mul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeHalfFock.gramComplex D = 1)
    (hGH : LatticeHalfFock.gramComplex D * H = 1)
    (x : Index D) (p : Oscillator D) :
    L D H 0 (X x * p) = X x * L D H 0 p + ((x.2 : ℂ) + 1 / 2) • (X x * p) := by
  have h := congrArg (fun A : Module.End ℂ (Oscillator D) => A p)
    (L_current_commutator D H hHG hGH x.1 0 (-(x.2 : ℤ) - 1))
  simp only [current_negative, zero_add, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply] at h
  have hf : -frequency (-(x.2 : ℤ) - 1) = (x.2 : ℂ) + 1 / 2 := by
    simp only [frequency, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    ring
  rw [hf] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

def nativeCoefficientMap (D : LatticeData) (charge : Charge D) (exponent : ℤ) :
    Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
  Polynomial.lsum fun degree => LinearMap.mulRight (Oscillator D)
    (halfCreationCoeff D charge (exponent + chargeNorm D charge + degree))

theorem nativeCoefficientMap_monomial (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (degree : ℕ) (coefficient : Oscillator D) :
    nativeCoefficientMap D charge exponent (Polynomial.monomial degree coefficient) =
      coefficient * halfCreationCoeff D charge (exponent + chargeNorm D charge + degree) := by
  simp [nativeCoefficientMap, Polynomial.lsum_apply, LinearMap.mulRight_apply]

theorem oscillatorCoefficient_as_sum (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) :
    oscillatorCoefficient D charge exponent polynomial =
      nativeCoefficientMap D charge exponent (halfTranslatedPolynomial D charge polynomial) := by
  change (∑ᶠ degree : ℕ, oscillatorTerm D charge exponent polynomial degree) = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D charge exponent polynomial)]
  rfl

theorem nativeCoefficientMap_C_mul (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (coefficient : Oscillator D) (polynomial : Polynomial (Oscillator D)) :
    nativeCoefficientMap D charge exponent (Polynomial.C coefficient * polynomial) =
      coefficient * nativeCoefficientMap D charge exponent polynomial := by
  rw [← Polynomial.smul_eq_C_mul, map_smul]
  rfl

private theorem nativeCoefficientMap_on_support (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Polynomial (Oscillator D)) (support : Finset ℕ)
    (contained : polynomial.support ⊆ support) :
    nativeCoefficientMap D charge exponent polynomial =
      ∑ degree ∈ support, polynomial.coeff degree *
        halfCreationCoeff D charge (exponent + chargeNorm D charge + degree) := by
  change polynomial.sum (fun degree coefficient => coefficient *
    halfCreationCoeff D charge (exponent + chargeNorm D charge + degree)) = _
  exact Polynomial.sum_eq_of_subset _ (by intro degree; simp) contained

private theorem nativeCoefficientMap_X_pow_mul (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (weight : ℕ) (polynomial : Polynomial (Oscillator D)) :
    nativeCoefficientMap D charge exponent (Polynomial.X ^ weight * polynomial) =
      nativeCoefficientMap D charge (exponent + weight) polynomial := by
  classical
  have contained : (Polynomial.X ^ weight * polynomial).support ⊆
      polynomial.support.image (fun degree => weight + degree) := by
    intro degree nonzero
    have coefficient := Polynomial.mem_support_iff.mp nonzero
    rw [Polynomial.coeff_X_pow_mul'] at coefficient
    split_ifs at coefficient with lower
    · exact Finset.mem_image.mpr ⟨degree - weight,
        Polynomial.mem_support_iff.mpr coefficient, by omega⟩
    · exact (coefficient rfl).elim
  rw [nativeCoefficientMap_on_support D charge exponent _ _ contained,
    Finset.sum_image, nativeCoefficientMap_on_support D charge (exponent + weight)
      polynomial polynomial.support (by rfl)]
  · apply Finset.sum_congr rfl
    intro degree hdegree
    rw [show weight + degree = degree + weight by omega, Polynomial.coeff_X_pow_mul]
    congr 2
    push_cast
    ring
  · intro left hleft right hright same
    change weight + left = weight + right at same
    omega

theorem oscillatorCoefficient_X_mul (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (index : Index D) (polynomial : Oscillator D) :
    oscillatorCoefficient D charge exponent (MvPolynomial.X index * polynomial) =
      MvPolynomial.X index * oscillatorCoefficient D charge exponent polynomial -
        (bilinear D charge (unitCharge D index.1) : ℂ) •
          oscillatorCoefficient D charge (exponent + omega D index) polynomial := by
  have translation : halfTranslatedPolynomial D charge (MvPolynomial.X index * polynomial) =
      Polynomial.C (MvPolynomial.X index : Oscillator D) *
        halfTranslatedPolynomial D charge polynomial -
      Polynomial.C ((bilinear D charge (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
        (Polynomial.X ^ omega D index * halfTranslatedPolynomial D charge polynomial) := by
    simp only [halfTranslatedPolynomial, map_mul, MvPolynomial.eval₂AlgHom_X,
      halfTranslationVariable]
    ring
  let left := Polynomial.C (MvPolynomial.X index : Oscillator D) *
    halfTranslatedPolynomial D charge polynomial
  let right := Polynomial.C ((bilinear D charge (unitCharge D index.1) : ℂ) •
    (1 : Oscillator D)) *
    (Polynomial.X ^ omega D index * halfTranslatedPolynomial D charge polynomial)
  have difference : nativeCoefficientMap D charge exponent (left - right) =
      nativeCoefficientMap D charge exponent left - nativeCoefficientMap D charge exponent right := by
    classical
    have contained : (left - right).support ⊆ left.support ∪ right.support := by
      intro degree hdegree
      by_contra outside
      have left_zero : left.coeff degree = 0 := by
        by_contra nonzero
        exact outside (Finset.mem_union_left _ (Polynomial.mem_support_iff.mpr nonzero))
      have right_zero : right.coeff degree = 0 := by
        by_contra nonzero
        exact outside (Finset.mem_union_right _ (Polynomial.mem_support_iff.mpr nonzero))
      have nonzero := Polynomial.mem_support_iff.mp hdegree
      rw [Polynomial.coeff_sub, left_zero, right_zero, sub_self] at nonzero
      exact nonzero rfl
    rw [nativeCoefficientMap_on_support D charge exponent (left - right)
      (left.support ∪ right.support) contained]
    simp only [Polynomial.coeff_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← nativeCoefficientMap_on_support D charge exponent left _ Finset.subset_union_left,
      ← nativeCoefficientMap_on_support D charge exponent right _ Finset.subset_union_right]
  rw [oscillatorCoefficient_as_sum, translation, difference,
    nativeCoefficientMap_C_mul, nativeCoefficientMap_C_mul,
    nativeCoefficientMap_X_pow_mul, ← oscillatorCoefficient_as_sum,
    ← oscillatorCoefficient_as_sum, smul_mul_assoc, one_mul]

theorem labelledRemainders_size (D : LatticeData) (word : List (Index D))
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

theorem wordWeight_occurrences (D : LatticeData) (exponent : Index D →₀ ℕ) :
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

end
end D5.S3.VertexAlgebra.LatticeHalfFockVisibilitySuppliers

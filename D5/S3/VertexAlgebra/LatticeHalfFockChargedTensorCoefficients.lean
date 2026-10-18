/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native charged tensor Laurent coefficients on the actual twisted ground module. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
import D5.S3.VertexAlgebra.LatticeHalfFockTensorFields
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Lie.OfAssociative

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators TensorProduct

noncomputable section

def groundRank (D : LatticeData) (hu : IsUnit D.G.det) : ℕ :=
  Classical.choose (actual_twisted_ground_representation D hu)

abbrev ActualGround (D : LatticeData) (hu : IsUnit D.G.det) := Ground (groundRank D hu)

def groundRepresentation (D : LatticeData) (hu : IsUnit D.G.det) :
    Representation ℂ (Extension D ⧸ K D) (ActualGround D hu) :=
  Classical.choose (Classical.choose_spec (actual_twisted_ground_representation D hu))

def groundLift (D : LatticeData) (charge : Charge D) : Extension D ⧸ K D :=
  QuotientGroup.mk (⟨0, charge⟩ : Extension D)

def groundAction (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    Module.End ℂ (ActualGround D hu) := groundRepresentation D hu (groundLift D charge)

def chargeNorm (D : LatticeData) (charge : Charge D) : ℤ := bilinear D charge charge

def chargeScalar (D : LatticeData) (charge : Charge D) : ℂ :=
  (2 : ℂ) ^ (-chargeNorm D charge)

def nativeOddWeightedDegree (D : LatticeData) (polynomial : Oscillator D) : ℕ :=
  MvPolynomial.weightedTotalDegree (omega D) polynomial

private theorem translated_native_degree (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    (halfTranslatedPolynomial D charge polynomial).natDegree ≤
      nativeOddWeightedDegree D polynomial := by
  classical
  have variable_bound (index : Index D) :
      (halfTranslationVariable D charge index).natDegree ≤ omega D index := by
    dsimp only [halfTranslationVariable]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  change (MvPolynomial.eval₂ (algebraMap ℂ (Polynomial (Oscillator D)))
    (halfTranslationVariable D charge) polynomial).natDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  apply Polynomial.natDegree_mul_le.trans
  rw [show (algebraMap ℂ (Polynomial (Oscillator D))) (polynomial.coeff exponent) =
    Polynomial.C ((algebraMap ℂ (Oscillator D)) (polynomial.coeff exponent)) by rfl,
    Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans _ (MvPolynomial.le_weightedTotalDegree (omega D) hexponent)
  rw [Finsupp.weight_apply]
  change (∑ index ∈ exponent.support,
    ((halfTranslationVariable D charge index) ^ exponent index).natDegree) ≤
      ∑ index ∈ exponent.support, exponent index * omega D index
  apply Finset.sum_le_sum
  intro index hindex
  exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (variable_bound index))

def oscillatorTerm (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (polynomial : Oscillator D) (degree : ℕ) : Oscillator D :=
  (halfTranslatedPolynomial D charge polynomial).coeff degree *
    halfCreationCoeff D charge (exponent + chargeNorm D charge + degree)

theorem term_support (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (polynomial : Oscillator D) :
    Function.support (oscillatorTerm D charge exponent polynomial) ⊆
      (halfTranslatedPolynomial D charge polynomial).support := by
  intro degree hdegree
  apply Polynomial.mem_support_iff.mpr
  intro hzero
  exact hdegree (by simp [oscillatorTerm, hzero])

theorem charged_term_finite_support (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (polynomial : Oscillator D) :
    Function.HasFiniteSupport (oscillatorTerm D charge exponent polynomial) :=
  (halfTranslatedPolynomial D charge polynomial).support.finite_toSet.subset
    (term_support D charge exponent polynomial)

def oscillatorCoefficient (D : LatticeData) (charge : Charge D) (exponent : ℤ) :
    Module.End ℂ (Oscillator D) where
  toFun polynomial := ∑ᶠ degree : ℕ, oscillatorTerm D charge exponent polynomial degree
  map_add' left right := by
    have terms : oscillatorTerm D charge exponent (left + right) =
        fun degree => oscillatorTerm D charge exponent left degree +
          oscillatorTerm D charge exponent right degree := by
      funext degree
      simp [oscillatorTerm, halfTranslatedPolynomial, add_mul]
    rw [terms]
    exact finsum_add_distrib (charged_term_finite_support D charge exponent left)
      (charged_term_finite_support D charge exponent right)
  map_smul' scalar polynomial := by
    have terms : oscillatorTerm D charge exponent (scalar • polynomial) =
        fun degree => scalar • oscillatorTerm D charge exponent polynomial degree := by
      funext degree
      simp [oscillatorTerm, halfTranslatedPolynomial, smul_mul_assoc]
    rw [terms]
    exact (smul_finsum' scalar (charged_term_finite_support D charge exponent polynomial)).symm

abbrev ActualTensor (D : LatticeData) (hu : IsUnit D.G.det) :=
  Oscillator D ⊗[ℂ] ActualGround D hu

def chargedCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (exponent : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  chargeScalar D charge • TensorProduct.map (oscillatorCoefficient D charge exponent)
    (groundAction D hu charge)

private theorem charged_native_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (polynomial : Oscillator D) (vector : ActualGround D hu) :
    chargedCoefficient D hu charge exponent (polynomial ⊗ₜ[ℂ] vector) =
      chargeScalar D charge •
        ((∑ degree ∈ (halfTranslatedPolynomial D charge polynomial).support,
          oscillatorTerm D charge exponent polynomial degree) ⊗ₜ[ℂ]
            groundAction D hu charge vector) := by
  simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul]
  change chargeScalar D charge • ((∑ᶠ degree : ℕ,
    oscillatorTerm D charge exponent polynomial degree) ⊗ₜ[ℂ] _) = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D charge exponent polynomial)]

/- proof_shape: charged_polynomial_lower_bound: content
   admission_basis: escape-witness
   escape_witness: Translation of every supported native monomial has degree
   bounded by its odd weight, yielding a uniform bound on the actual finite
   coefficient sum for arbitrary, not necessarily homogeneous, polynomials.
   Literature status: classical twisted lattice construction; zero novelty. -/
theorem charged_polynomial_lower_bound (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (vector : ActualGround D hu)
    (exponent : ℤ) (lower : exponent < -chargeNorm D charge - nativeOddWeightedDegree D polynomial) :
    chargedCoefficient D hu charge exponent (polynomial ⊗ₜ[ℂ] vector) = 0 := by
  classical
  rw [charged_native_expansion]
  have zero_sum : (∑ degree ∈ (halfTranslatedPolynomial D charge polynomial).support,
      oscillatorTerm D charge exponent polynomial degree) = 0 := by
    apply Finset.sum_eq_zero
    intro degree hdegree
    have degree_bound := (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hdegree)).trans (translated_native_degree D charge polynomial)
    have shifted : exponent + chargeNorm D charge + (degree : ℤ) < 0 := by
      have cast_bound : (degree : ℤ) ≤ nativeOddWeightedDegree D polynomial := by
        exact_mod_cast degree_bound
      omega
    simp [oscillatorTerm, halfCreationCoeff, shifted]
  simp [zero_sum]

private theorem charged_tensor_lower_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (state : ActualTensor D hu) :
    ∃ lower : ℤ, ∀ exponent : ℤ, exponent < lower →
      chargedCoefficient D hu charge exponent state = 0 := by
  induction state using TensorProduct.induction_on with
  | zero => exact ⟨0, by intros; simp⟩
  | tmul polynomial vector =>
    exact ⟨-chargeNorm D charge - nativeOddWeightedDegree D polynomial,
      fun exponent lower => charged_polynomial_lower_bound D hu charge polynomial vector exponent lower⟩
  | add left right hleft hright =>
    obtain ⟨left_bound, hleft⟩ := hleft
    obtain ⟨right_bound, hright⟩ := hright
    refine ⟨min left_bound right_bound, ?_⟩
    intro exponent lower
    simp [hleft exponent (lt_of_lt_of_le lower (min_le_left _ _)),
      hright exponent (lt_of_lt_of_le lower (min_le_right _ _))]

def chargedField (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    LatticeHalfFock.HalfField (ActualTensor D hu) :=
  HVertexOperator.of_coeff (chargedCoefficient D hu charge) (by
    intro state
    obtain ⟨lower, hlower⟩ := charged_tensor_lower_truncation D hu charge state
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨lower, ?_⟩
    intro exponent hexponent
    by_contra hbound
    exact hexponent (hlower exponent (by omega)))

private theorem creation_zero (D : LatticeData) (charge : Charge D) :
    halfCreationCoeff D charge 0 = 1 := by
  have constant : PowerSeries.constantCoeff (halfCreationSeries D charge) = 0 := by
    simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [halfCreationCoeff, if_neg (by omega)]
  change PowerSeries.coeff 0 (halfCreationExponential D charge) = 1
  rw [halfCreationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' constant), finsum_eq_single _ 0]
  · simp
  · intro degree hdegree
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constant]
    simp [hdegree]

theorem charged_vacuum_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (vector : ActualGround D hu) :
    chargedCoefficient D hu charge exponent ((1 : Oscillator D) ⊗ₜ[ℂ] vector) =
      chargeScalar D charge • (halfCreationCoeff D charge (exponent + chargeNorm D charge) ⊗ₜ[ℂ]
        groundAction D hu charge vector) := by
  classical
  have translation_one : halfTranslatedPolynomial D charge (1 : Oscillator D) = 1 :=
    map_one (MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D charge))
  have support_one : (1 : Polynomial (Oscillator D)).support = {0} := by
    rw [← Polynomial.C_1, Polynomial.support_C (one_ne_zero : (1 : Oscillator D) ≠ 0)]
  rw [charged_native_expansion, translation_one, support_one]
  simp [oscillatorTerm, translation_one, Polynomial.coeff_one]

/- proof_shape: charged_ground_leading: content
   admission_basis: escape-witness
   escape_witness: The actual normalized tensor coefficient has a nonzero
   vacuum coordinate on every nonzero actual ground vector. Native coefficient
   evaluation, the monomial tensor basis and the inverse group representation
   establish this without an assumed injective charged action or field law.
   Literature status: classical twisted lattice construction; zero novelty. -/
theorem charged_ground_leading (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (vector : ActualGround D hu) (nonzero : vector ≠ 0) :
    chargedCoefficient D hu charge (-chargeNorm D charge) ((1 : Oscillator D) ⊗ₜ[ℂ] vector) ≠ 0 := by
  rw [charged_vacuum_coefficient]
  simp only [neg_add_cancel, creation_zero]
  have scalar_nonzero : chargeScalar D charge ≠ 0 := by
    exact zpow_ne_zero _ (by norm_num)
  apply smul_ne_zero scalar_nonzero
  intro tensor_zero
  have coordinate := congrArg (fun state : ActualTensor D hu =>
    TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials (Index D) ℂ) state 0)
      tensor_zero
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at coordinate
  have one_coordinate : (MvPolynomial.basisMonomials (Index D) ℂ).repr
      (1 : Oscillator D) 0 = 1 := by
    change (1 : Oscillator D).coeff 0 = 1
    simp
  simp only [one_coordinate, one_smul, map_zero, Finsupp.zero_apply] at coordinate
  apply nonzero
  have inverse := (groundRepresentation D hu).inv_self_apply (groundLift D charge) vector
  rw [show groundRepresentation D hu (groundLift D charge) vector = 0 from coordinate,
    map_zero] at inverse
  exact inverse.symm

end
noncomputable section

private def nativeCoefficientMap (D : LatticeData) (charge : Charge D) (exponent : ℤ) :
    Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
  Polynomial.lsum fun degree => LinearMap.mulRight (Oscillator D)
    (halfCreationCoeff D charge (exponent + chargeNorm D charge + degree))

private theorem oscillatorCoefficient_as_sum (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) :
    oscillatorCoefficient D charge exponent polynomial =
      nativeCoefficientMap D charge exponent (halfTranslatedPolynomial D charge polynomial) := by
  change (∑ᶠ degree : ℕ, oscillatorTerm D charge exponent polynomial degree) = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D charge exponent polynomial)]
  rfl

private theorem nativeCoefficientMap_C_mul (D : LatticeData) (charge : Charge D)
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

private theorem oscillatorCoefficient_X_mul (D : LatticeData) (charge : Charge D)
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

private theorem polynomialDerivation_coeff (D : LatticeData) (colour : Fin D.rank)
    (mode degree : ℕ) (polynomial : Polynomial (Oscillator D)) :
    (LatticeActualAnnihilation.polynomialDerivation D colour mode polynomial).coeff degree =
      LatticeActualAnnihilation.annihilate D colour mode (polynomial.coeff degree) := by
  change LatticeActualAnnihilation.annihilationDerivation D colour mode
    (polynomial.coeff degree) = _
  rw [LatticeActualAnnihilation.annihilation_apply]

private theorem nativeCoefficientMap_annihilation (D : LatticeData) (colour : Fin D.rank)
    (mode : ℕ) (charge : Charge D) (exponent : ℤ) (polynomial : Polynomial (Oscillator D)) :
    LatticeActualAnnihilation.annihilate D colour mode
        (nativeCoefficientMap D charge exponent polynomial) =
      nativeCoefficientMap D charge exponent
          (LatticeActualAnnihilation.polynomialDerivation D colour mode polynomial) +
        ((2 / (2 * mode + 1 : ℂ)) * (bilinear D (unitCharge D colour) charge : ℂ)) •
          nativeCoefficientMap D charge (exponent - (2 * mode + 1 : ℕ)) polynomial := by
  classical
  have contained : (LatticeActualAnnihilation.polynomialDerivation D colour mode polynomial).support ⊆
      polynomial.support := by
    intro degree hdegree
    apply Polynomial.mem_support_iff.mpr
    intro zero
    have nonzero := Polynomial.mem_support_iff.mp hdegree
    rw [polynomialDerivation_coeff, zero, map_zero] at nonzero
    exact nonzero rfl
  rw [nativeCoefficientMap_on_support D charge exponent polynomial _ (by rfl), map_sum,
    nativeCoefficientMap_on_support D charge exponent _ polynomial.support contained,
    nativeCoefficientMap_on_support D charge (exponent - (2 * mode + 1 : ℕ)) polynomial _ (by rfl),
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro degree hdegree
  rw [LatticeActualAnnihilation.annihilate_mul, half_annihilation_creation,
    polynomialDerivation_coeff, mul_smul_comm]
  rw [show exponent + chargeNorm D charge + (degree : ℤ) - (2 * mode + 1 : ℕ) =
    (exponent - (2 * mode + 1 : ℕ)) + chargeNorm D charge + degree by omega]

private theorem oscillator_annihilation (D : LatticeData) (colour : Fin D.rank)
    (mode : ℕ) (charge : Charge D) (exponent : ℤ) (polynomial : Oscillator D) :
    LatticeActualAnnihilation.annihilate D colour mode
        (oscillatorCoefficient D charge exponent polynomial) =
      oscillatorCoefficient D charge exponent
          (LatticeActualAnnihilation.annihilate D colour mode polynomial) +
        ((2 / (2 * mode + 1 : ℂ)) * (bilinear D (unitCharge D colour) charge : ℂ)) •
          oscillatorCoefficient D charge (exponent - (2 * mode + 1 : ℕ)) polynomial := by
  simp only [oscillatorCoefficient_as_sum, half_translated_derivation]
  exact nativeCoefficientMap_annihilation D colour mode charge exponent _

private theorem oscillator_current_ward (D : LatticeData) (colour : Fin D.rank)
    (charge : Charge D) (mode exponent : ℤ) (polynomial : Oscillator D) :
    LatticeHalfFock.current D colour mode (oscillatorCoefficient D charge exponent polynomial) -
      oscillatorCoefficient D charge exponent (LatticeHalfFock.current D colour mode polynomial) =
        (bilinear D (unitCharge D colour) charge : ℂ) •
          oscillatorCoefficient D charge (exponent - (2 * mode + 1)) polynomial := by
  by_cases negative : mode < 0
  · simp only [LatticeHalfFock.current, if_pos negative, LinearMap.mulLeft_apply,
      oscillatorCoefficient_X_mul, LatticeFiniteNegativeGeneration.bilinear_symmetric D charge]
    have shifted : exponent + (omega D (colour, (-mode - 1).toNat) : ℤ) =
        exponent - (2 * mode + 1) := by
      simp only [omega, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      omega
    rw [shifted]
    abel
  · have nonnegative : 0 ≤ mode := by omega
    have mode_cast : (mode.toNat : ℤ) = mode := Int.toNat_of_nonneg nonnegative
    have shifted : exponent - (2 * mode.toNat + 1 : ℕ) = exponent - (2 * mode + 1) := by
      push_cast
      omega
    have scalar : LatticeHalfFock.frequency mode * (2 / (2 * mode.toNat + 1 : ℂ)) = 1 := by
      have complex_cast : (mode.toNat : ℂ) = (mode : ℂ) := by exact_mod_cast mode_cast
      have nonzero : (2 * mode.toNat + 1 : ℂ) ≠ 0 := by
        exact_mod_cast (by omega : 2 * mode.toNat + 1 ≠ 0)
      unfold LatticeHalfFock.frequency
      rw [← complex_cast]
      simp only [div_eq_mul_inv]
      rw [← mul_assoc,
        show ((mode.toNat : ℂ) + 1 * (2 : ℂ)⁻¹) * 2 = 2 * mode.toNat + 1 by ring,
        mul_inv_cancel₀ nonzero]
    simp only [LatticeHalfFock.current, if_neg negative, LinearMap.smul_apply,
      oscillator_annihilation, map_smul, smul_add, smul_smul, shifted]
    rw [← mul_assoc, scalar, one_mul]
    abel

theorem charged_tensor_current_ward (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (charge : Charge D) (mode exponent : ℤ) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
        chargedCoefficient D hu charge exponent -
      chargedCoefficient D hu charge exponent *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
      (bilinear D (unitCharge D colour) charge : ℂ) •
        chargedCoefficient D hu charge (exponent - (2 * mode + 1)) := by
  apply TensorProduct.ext'
  intro polynomial vector
  simp only [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd, chargedCoefficient,
    Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, map_smul]
  rw [← smul_sub, ← TensorProduct.sub_tmul, oscillator_current_ward,
    TensorProduct.smul_tmul']
  rw [smul_comm]
  simp only [TensorProduct.smul_tmul']

end

noncomputable section
open LatticeHalfFock
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
attribute [local instance] LieRing.ofAssociativeRing

private def linearCreation (D : LatticeData) (a : Charge D) (n : ℕ) : Oscillator D :=
  ∑ i : Fin D.rank, (a i : ℂ) • MvPolynomial.X (i,n)

private theorem creation_negative (D : LatticeData) (a : Charge D) (d : ℤ)
    (hd : d < 0) : halfCreationCoeff D a d = 0 := by
  simp [halfCreationCoeff, hd]

private theorem creation_recurrence (D : LatticeData) (a : Charge D) (R : ℤ) :
    (∑ n ∈ Finset.range (R.toNat+1),
      linearCreation D a n * halfCreationCoeff D a (R-(2*n+1 : ℕ))) =
        ((R : ℂ)/2) • halfCreationCoeff D a R := by
  classical
  by_cases hR : R ≤ 0
  · have terms (n : ℕ) : halfCreationCoeff D a (R-(2*n+1 : ℕ)) = 0 :=
      creation_negative D a _ (by omega)
    simp only [terms, mul_zero, Finset.sum_const_zero]
    rcases lt_or_eq_of_le hR with h | h
    · rw [creation_negative D a R h, smul_zero]
    · subst R; simp
  · have hpos : 0 < R := by omega
    obtain ⟨r, hr⟩ : ∃ r : ℕ, R = (r+1 : ℕ) := by
      exact ⟨R.toNat-1, by omega⟩
    subst R
    let f : ℕ → Oscillator D := fun k =>
      if k % 2 = 0 then linearCreation D a (k/2) *
        PowerSeries.coeff (r-k) (halfCreationExponential D a) else 0
    let g : ℕ → Oscillator D := fun n =>
      linearCreation D a n * halfCreationCoeff D a (((r+1 : ℕ) : ℤ)-((2*n+1 : ℕ) : ℤ))
    have term (k : ℕ) (hk : k ∈ Finset.range (r+1)) (he : k%2=0) :
        f k = g (k/2) := by
      have hk' : k ≤ r := by have := Finset.mem_range.mp hk; omega
      have idx : ((r+1 : ℕ) : ℤ) - ((2*(k/2)+1 : ℕ) : ℤ) = (r-k : ℕ) := by omega
      simp only [f, g, if_pos he, idx, halfCreationCoeff,
        Int.natCast_nonneg, not_lt.mpr, if_false, Int.toNat_natCast]
    have sum_eq : (∑ k ∈ Finset.range (r+1), f k) =
        ∑ n ∈ Finset.range ((r+1)+1), g n := by
      apply Finset.sum_bij_ne_zero (fun k _ _ => k/2)
      · intro k hk hn
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro k hk hn l hl hm equal
        have ek : k%2=0 := by
          by_contra h; exact hn (by simp [f,h])
        have el : l%2=0 := by
          by_contra h; exact hm (by simp [f,h])
        omega
      · intro n hn nonzero
        have bound : 2*n+1 ≤ r+1 := by
          by_contra h
          exact nonzero (by
            dsimp only [g]
            rw [creation_negative D a _ (by omega), mul_zero])
        have hk : 2*n ∈ Finset.range (r+1) := by simp; omega
        have he : (2*n)%2=0 := by omega
        refine ⟨2*n, hk, ?_, by omega⟩
        rw [term _ hk he, show 2*n/2=n by omega]
        exact nonzero
      · intro k hk hn
        have he : k%2=0 := by
          by_contra h; exact hn (by simp [f,h])
        exact term k hk he
    have differential := congrArg (PowerSeries.coeff r) (exponential_derivative D a)
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at differential
    have driver : (∑ k ∈ Finset.range (r+1),
        PowerSeries.coeff k (halfCreationExponential D a) *
          PowerSeries.coeff (r-k) (PowerSeries.derivative (R := Oscillator D)
            (halfCreationSeries D a))) =
        (2 : ℂ) • ∑ k ∈ Finset.range (r+1), f k := by
      rw [← Finset.sum_range_reflect]
      simp only [Nat.add_sub_cancel, series_derivative_coeff, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ r := by have := Finset.mem_range.mp hk; omega
      rw [show r-(r-k)=k by omega]
      by_cases he : k%2=0
      · simp only [if_pos he, f, linearCreation, mul_smul_comm]
        rw [mul_comm, ← Finset.smul_sum, smul_mul_assoc]
      · simp [he, f]
    rw [driver, sum_eq] at differential
    have cast_mul : PowerSeries.coeff (r+1) (halfCreationExponential D a) *
        (r+1 : Oscillator D) =
        (r+1 : ℂ) • PowerSeries.coeff (r+1) (halfCreationExponential D a) := by
      simp [Algebra.smul_def, mul_comm]
    rw [cast_mul] at differential
    have result := congrArg (fun p : Oscillator D => (2 : ℂ)⁻¹ • p) differential.symm
    simpa [g, halfCreationCoeff, smul_smul, div_eq_mul_inv,
      show ¬ ((r : ℤ)+1 < 0) by omega, mul_comm] using result

private theorem gram_charge_left (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (a : Charge D) (i : Fin D.rank) :
    ∑ l, H i l * (bilinear D (unitCharge D l) a : ℂ) = (a i : ℂ) := by
  have row (l : Fin D.rank) : (bilinear D (unitCharge D l) a : ℂ) =
      (gramComplex D *ᵥ fun k => (a k : ℂ)) l := by
    simp [bilinear, unitCharge, Matrix.mulVec, dotProduct, gramComplex]
  simp_rw [row]
  change (H *ᵥ (gramComplex D *ᵥ fun k => (a k : ℂ))) i = _
  rw [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]

private theorem gram_charge_right (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)
    (a : Charge D) (l : Fin D.rank) :
    ∑ i, H i l * (bilinear D (unitCharge D i) a : ℂ) = (a l : ℂ) := by
  have col (i : Fin D.rank) : (bilinear D (unitCharge D i) a : ℂ) =
      ((fun k => (a k : ℂ)) ᵥ* gramComplex D) i := by
    rw [LatticeFiniteNegativeGeneration.bilinear_symmetric]
    simp [bilinear, unitCharge, Matrix.vecMul, dotProduct, gramComplex]
  simp_rw [col, mul_comm (H _ _)]
  change (((fun k => (a k : ℂ)) ᵥ* gramComplex D) ᵥ* H) l = _
  rw [Matrix.vecMul_vecMul, hGH, Matrix.vecMul_one]

private theorem gram_charge_norm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (a : Charge D) :
    (∑ i, ∑ l, H i l * (bilinear D (unitCharge D i) a : ℂ) *
      (bilinear D (unitCharge D l) a : ℂ)) = (bilinear D a a : ℂ) := by
  calc
    _ = ∑ i, (bilinear D (unitCharge D i) a : ℂ) *
        (∑ l, H i l * (bilinear D (unitCharge D l) a : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = ∑ i, (bilinear D (unitCharge D i) a : ℂ) * (a i : ℂ) := by
      simp_rw [gram_charge_left D H hHG]
    _ = _ := by
      have row (i : Fin D.rank) : bilinear D (unitCharge D i) a =
          ∑ l, D.G i l * a l := by simp [bilinear, unitCharge]
      simp_rw [row]
      simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul, bilinear]
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      ring

private theorem coherent_current (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) (j d : ℤ) (hj : 0 ≤ j) :
    current D i j (halfCreationCoeff D a d) =
      (bilinear D (unitCharge D i) a : ℂ) •
        halfCreationCoeff D a (d-(2*j+1)) := by
  have jj : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
  have jc : (j.toNat : ℂ) = (j : ℂ) := by exact_mod_cast jj
  have wne : (2*j.toNat+1 : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : 2*j.toNat+1 ≠ 0)
  have scalar : frequency j * (2/(2*j.toNat+1 : ℂ)) = 1 := by
    rw [frequency, ← jc]
    simp only [div_eq_mul_inv]
    rw [← mul_assoc,
      show ((j.toNat : ℂ)+1*(2 : ℂ)⁻¹)*2 = 2*j.toNat+1 by ring,
      mul_inv_cancel₀ wne]
  rw [current, if_neg (by omega), LinearMap.smul_apply, half_annihilation_creation,
    smul_smul, ← mul_assoc, scalar, one_mul,
    show d-(2*j.toNat+1 : ℕ) = d-(2*j+1) by push_cast; omega]

private theorem oscillator_one (D : LatticeData) (a : Charge D) (e : ℤ) :
    oscillatorCoefficient D a e 1 = halfCreationCoeff D a (e+chargeNorm D a) := by
  rw [oscillatorCoefficient_as_sum]
  simp only [halfTranslatedPolynomial, map_one, nativeCoefficientMap, Polynomial.lsum_apply]
  rw [← Polynomial.C_1, Polynomial.sum_C_index (by simp)]
  simp

private theorem oscillator_variable (D : LatticeData) (a : Charge D) (e : ℤ)
    (x : Index D) :
    oscillatorCoefficient D a e (MvPolynomial.X x) =
      MvPolynomial.X x * halfCreationCoeff D a (e+chargeNorm D a) -
        (bilinear D a (unitCharge D x.1) : ℂ) •
          halfCreationCoeff D a (e+chargeNorm D a+omega D x) := by
  simpa [oscillator_one, add_assoc, add_comm, add_left_comm] using oscillatorCoefficient_X_mul D a e x 1

private def quadraticCreation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n k : ℕ) : Oscillator D :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ l, H i l •
    (MvPolynomial.X (i,n) * MvPolynomial.X (l,k))

private theorem contract_first (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (a : Charge D) (n : ℕ) (p : Oscillator D) :
    (∑ i, ∑ l, H i l • ((bilinear D (unitCharge D l) a : ℂ) •
      (MvPolynomial.X (i,n) * p))) = linearCreation D a n * p := by
  simp_rw [smul_smul, ← Finset.sum_smul, gram_charge_left D H hHG]
  simp [linearCreation, Finset.sum_mul, smul_mul_assoc]

private theorem contract_second (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)
    (a : Charge D) (n : ℕ) (p : Oscillator D) :
    (∑ i, ∑ l, H i l • ((bilinear D (unitCharge D i) a : ℂ) •
      (MvPolynomial.X (l,n) * p))) = linearCreation D a n * p := by
  rw [Finset.sum_comm]
  simp_rw [smul_smul, ← Finset.sum_smul, gram_charge_right D H hGH]
  simp [linearCreation, Finset.sum_mul, smul_mul_assoc]

private theorem contract_double (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (a : Charge D) (p : Oscillator D) :
    (∑ i, ∑ l, H i l • ((bilinear D (unitCharge D i) a : ℂ) •
      ((bilinear D (unitCharge D l) a : ℂ) • p))) =
        (bilinear D a a : ℂ) • p := by
  simp_rw [smul_smul, ← mul_assoc, ← Finset.sum_smul]
  rw [gram_charge_norm D H hHG]

private theorem oscillator_quadratic (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (e : ℤ) (n k : ℕ) :
    oscillatorCoefficient D a e (quadraticCreation D H n k) =
      quadraticCreation D H n k * halfCreationCoeff D a (e+chargeNorm D a) -
      (2 : ℂ)⁻¹ • (linearCreation D a n *
        halfCreationCoeff D a (e+chargeNorm D a+(2*k+1 : ℕ))) -
      (2 : ℂ)⁻¹ • (linearCreation D a k *
        halfCreationCoeff D a (e+chargeNorm D a+(2*n+1 : ℕ))) +
      ((bilinear D a a : ℂ)/2) •
        halfCreationCoeff D a (e+chargeNorm D a+(2*n+1 : ℕ)+(2*k+1 : ℕ)) := by
  unfold quadraticCreation
  rw [map_smul]
  simp_rw [map_sum, map_smul, oscillatorCoefficient_X_mul, oscillator_variable,
    LatticeFiniteNegativeGeneration.bilinear_symmetric D a,
    mul_sub, mul_smul_comm, smul_sub, omega]
  simp_rw [Finset.sum_sub_distrib, smul_sub,
    show e+(2*n+1 : ℕ)+chargeNorm D a+(2*k+1 : ℕ) =
        e+chargeNorm D a+(2*n+1 : ℕ)+(2*k+1 : ℕ) by omega,
    contract_first D H hHG, contract_second D H hGH, contract_double D H hHG]
  simp only [Finset.sum_mul, smul_mul_assoc, smul_smul, div_eq_mul_inv]
  rw [show e+(2*n+1 : ℕ)+chargeNorm D a = e+chargeNorm D a+(2*n+1 : ℕ) by omega]
  simp only [mul_assoc]
  module

private def contractedPair (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m j : ℤ) (p : Oscillator D) : Oscillator D :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ l, H i l • normalPair D i l j (m-j-1) p

private theorem rawL_contracted (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (p : Oscillator D) :
    rawL D H m p = ∑ᶠ j : ℤ, contractedPair D H m j p := by
  classical
  have term (i l : Fin D.rank) : Function.HasFiniteSupport
      (fun j : ℤ => H i l • normalPair D i l j (m-j-1) p) := by
    simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
      (fun _ : ℤ => H i l) (normalPair_finite D i l m p)
  have inner (i : Fin D.rank) : Function.HasFiniteSupport
      (fun j : ℤ => ∑ l, H i l • normalPair D i l j (m-j-1) p) :=
    Function.HasFiniteSupport.sum (term i) Finset.univ
  have outer : Function.HasFiniteSupport
      (fun j : ℤ => ∑ i, ∑ l, H i l • normalPair D i l j (m-j-1) p) :=
    Function.HasFiniteSupport.sum inner Finset.univ
  simp only [rawL, LinearMap.smul_apply, LinearMap.sum_apply]
  change (2 : ℂ)⁻¹ • (∑ i, ∑ l, H i l • ∑ᶠ j : ℤ,
    normalPair D i l j (m-j-1) p) = _
  simp_rw [smul_finsum' _ (normalPair_finite D _ _ m p)]
  simp_rw [sum_finsum_comm Finset.univ _ (fun l _ => term _ l)]
  rw [sum_finsum_comm Finset.univ _ (fun i _ => inner i), smul_finsum' _ outer]
  rfl

private def groundPair (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m j : ℤ) : Oscillator D :=
  if m ≤ j ∧ j < 0 then quadraticCreation D H (-j-1).toNat (j-m).toNat else 0

private def mixedLeft (D : LatticeData) (a : Charge D) (m d j : ℤ) : Oscillator D :=
  if j < min m 0 then linearCreation D a (-j-1).toNat *
    halfCreationCoeff D a (d-2*m+2*j+1) else 0

private theorem contractedPair_coherent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m d j : ℤ) :
    contractedPair D H m j (halfCreationCoeff D a d) =
      groundPair D H m j * halfCreationCoeff D a d +
      (2 : ℂ)⁻¹ • mixedLeft D a m d j +
      (2 : ℂ)⁻¹ • mixedLeft D a m d (m-j-1) +
      (if 0 ≤ j ∧ j < m then ((bilinear D a a : ℂ)/2) •
        halfCreationCoeff D a (d-2*m) else 0) := by
  classical
  by_cases hj : j < 0
  · by_cases hk : m-j-1 < 0
    · have hground : m ≤ j ∧ j < 0 := by omega
      have hmixed : ¬ j < min m 0 := by omega
      have hmixed' : ¬ m-j-1 < min m 0 := by omega
      have hmiddle : ¬ (0 ≤ j ∧ j < m) := by omega
      simp only [contractedPair, normalPair, if_pos hj, Module.End.mul_apply,
        current, if_pos hk, LinearMap.mulLeft_apply, groundPair, if_pos hground,
        mixedLeft, if_neg hmixed, if_neg hmixed', smul_zero, hmiddle, if_false,
        add_zero]
      simp only [quadraticCreation, Finset.sum_mul, smul_mul_assoc, mul_assoc,
        show -(m-j-1)-1 = j-m by omega]
    · have hground : ¬ (m ≤ j ∧ j < 0) := by omega
      have hmixed : j < min m 0 := by omega
      have hmixed' : ¬ m-j-1 < min m 0 := by omega
      have hmiddle : ¬ (0 ≤ j ∧ j < m) := by omega
      simp only [contractedPair, normalPair, if_pos hj, Module.End.mul_apply]
      simp_rw [coherent_current D a _ (m-j-1) d (by omega)]
      simp only [current, if_pos hj, LinearMap.mulLeft_apply, mul_smul_comm]
      rw [contract_first D H hHG]
      simp only [groundPair, if_neg hground, zero_mul, mixedLeft, if_pos hmixed,
        if_neg hmixed', smul_zero, if_neg hmiddle, zero_add, add_zero]
      congr 3
      omega
  · by_cases hk : m-j-1 < 0
    · have hground : ¬ (m ≤ j ∧ j < 0) := by omega
      have hmixed : ¬ j < min m 0 := by omega
      have hmixed' : m-j-1 < min m 0 := by omega
      have hmiddle : ¬ (0 ≤ j ∧ j < m) := by omega
      simp only [contractedPair, normalPair, if_neg hj, Module.End.mul_apply]
      simp_rw [coherent_current D a _ j d (by omega)]
      simp only [current, if_pos hk, LinearMap.mulLeft_apply, mul_smul_comm]
      rw [contract_second D H hGH]
      simp only [groundPair, if_neg hground, zero_mul, mixedLeft, if_neg hmixed,
        if_pos hmixed', smul_zero, if_neg hmiddle, zero_add, add_zero]
      congr 3 <;> omega
    · have hground : ¬ (m ≤ j ∧ j < 0) := by omega
      have hmixed : ¬ j < min m 0 := by omega
      have hmixed' : ¬ m-j-1 < min m 0 := by omega
      have hmiddle : 0 ≤ j ∧ j < m := by omega
      simp only [contractedPair, normalPair, if_neg hj, Module.End.mul_apply]
      simp_rw [coherent_current D a _ j d (by omega), map_smul,
        coherent_current D a _ (m-j-1) _ (by omega)]
      rw [contract_double D H hHG]
      simp only [groundPair, if_neg hground, zero_mul, mixedLeft, if_neg hmixed,
        if_neg hmixed', smul_zero, if_pos hmiddle, zero_add, add_zero, smul_smul]
      congr 1
      · ring
      · congr 1; omega

private theorem mixedLeft_finite (D : LatticeData) (a : Charge D) (m d : ℤ) :
    Function.HasFiniteSupport (mixedLeft D a m d) := by
  apply (Set.finite_Icc (-((d-2*m).toNat : ℤ)-1) (-1)).subset
  intro j hj
  have neg : j < min m 0 := by
    by_contra h; exact hj (by simp [mixedLeft,h])
  have nonnegative : 0 ≤ d-2*m+2*j+1 := by
    by_contra h
    exact hj (by
      rw [mixedLeft, if_pos neg, creation_negative D a _ (by omega), mul_zero])
  simp only [Set.mem_Icc]
  have bound : d-2*m ≤ ((d-2*m).toNat : ℤ) := Int.self_le_toNat _
  omega

private theorem groundPair_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    Function.HasFiniteSupport (groundPair D H m) := by
  apply (Set.finite_Icc m (-1)).subset
  intro j hj
  have h : m ≤ j ∧ j < 0 := by
    by_contra h; exact hj (by simp [groundPair,h])
  simpa only [Set.mem_Icc] using (show m ≤ j ∧ j ≤ -1 by omega)

private theorem groundPair_sum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    (∑ᶠ j : ℤ, groundPair D H m j) = rawL D H m 1 := by
  rw [rawL_contracted]
  apply finsum_congr
  intro j
  by_cases hj : j < 0
  · by_cases hk : m-j-1 < 0
    · simp [groundPair, show m ≤ j by omega, contractedPair, normalPair, hj,
        current, hk, quadraticCreation, show -(m-j-1)-1 = j-m by omega]
    · have zero (i : Fin D.rank) : current D i (m-j-1) (1 : Oscillator D) = 0 :=
        current_vanish D i 1 _ (by simp; omega)
      simp [groundPair, show ¬ m ≤ j by omega, contractedPair, normalPair, hj, zero]
  · have zero (i : Fin D.rank) : current D i j (1 : Oscillator D) = 0 :=
      current_vanish D i 1 _ (by simp; omega)
    simp [groundPair, hj, contractedPair, normalPair, zero]

private theorem integer_finsum_negative (D : LatticeData) (f : ℤ → Oscillator D)
    (hf : ∀ j : ℤ, 0 ≤ j → f j = 0) :
    (∑ᶠ j : ℤ, f j) = ∑ᶠ n : ℕ, f (-(n : ℤ)-1) := by
  classical
  let embedding : ℕ → ℤ := fun n => -(n : ℤ)-1
  have inj : Function.Injective embedding := by intro n k h; dsimp [embedding] at h; omega
  have range : Set.range embedding = {j : ℤ | j < 0} := by
    ext j
    constructor
    · rintro ⟨n,rfl⟩; dsimp [embedding]; omega
    · intro hj
      change j < 0 at hj
      exact ⟨(-j-1).toNat, by dsimp [embedding]; omega⟩
  calc
    (∑ᶠ j : ℤ, f j) = ∑ᶠ j ∈ Set.range embedding, f j := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro j
      by_cases hj : j < 0
      · simp [range,hj]
      · simp [range,hj,hf j (by omega)]
    _ = _ := finsum_mem_range inj

private theorem mixedLeft_sum (D : LatticeData) (a : Charge D) (m d : ℤ) :
    (∑ᶠ j : ℤ, mixedLeft D a m d j) =
      ∑ n ∈ Finset.range ((d-2*m).toNat+1),
        if (max (-m) 0).toNat ≤ n then linearCreation D a n *
          halfCreationCoeff D a (d-2*m-(2*n+1 : ℕ)) else 0 := by
  classical
  rw [integer_finsum_negative D _ (by intro j hj; simp [mixedLeft, show ¬ j < min m 0 by omega])]
  have terms (n : ℕ) : mixedLeft D a m d (-(n : ℤ)-1) =
      if (max (-m) 0).toNat ≤ n then linearCreation D a n *
        halfCreationCoeff D a (d-2*m-(2*n+1 : ℕ)) else 0 := by
    have cond : -(n : ℤ)-1 < min m 0 ↔ (max (-m) 0).toNat ≤ n := by omega
    simp only [mixedLeft, cond, show -(-(n : ℤ)-1)-1 = n by omega, Int.toNat_natCast]
    congr 1
    push_cast
    congr 2
    omega
  simp_rw [terms]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have negative : d-2*m-(2*n+1 : ℕ) < 0 := by omega
  exact hn (by dsimp only; split_ifs <;> simp only [creation_negative D a _ negative, mul_zero])

private theorem rawL_coherent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m d : ℤ) :
    rawL D H m (halfCreationCoeff D a d) =
      rawL D H m 1 * halfCreationCoeff D a d +
      (∑ n ∈ Finset.range ((d-2*m).toNat+1),
        if (max (-m) 0).toNat ≤ n then linearCreation D a n *
          halfCreationCoeff D a (d-2*m-(2*n+1 : ℕ)) else 0) +
      ∑ j ∈ Finset.Ico (0 : ℤ) m,
        ((bilinear D a a : ℂ)/2) • halfCreationCoeff D a (d-2*m) := by
  classical
  let g : ℤ → Oscillator D := fun j => groundPair D H m j * halfCreationCoeff D a d
  let f := mixedLeft D a m d
  let c : ℤ → Oscillator D := fun j =>
    if 0 ≤ j ∧ j < m then ((bilinear D a a : ℂ)/2) •
      halfCreationCoeff D a (d-2*m) else 0
  let mirror : ℤ ≃ ℤ := {
    toFun := fun j => m-j-1
    invFun := fun j => m-j-1
    left_inv := by intro j; dsimp; omega
    right_inv := by intro j; dsimp; omega }
  have hg : Function.HasFiniteSupport g := by
    simpa only [g, Pi.mul_def] using
      (groundPair_finite D H m).mul_left (fun _ => halfCreationCoeff D a d)
  have hf : Function.HasFiniteSupport f := mixedLeft_finite D a m d
  have hmirror : Function.HasFiniteSupport (fun j : ℤ => f (m-j-1)) :=
    hf.fun_comp_of_injective mirror.injective
  have hhalf : Function.HasFiniteSupport (fun j : ℤ => (2 : ℂ)⁻¹ • f j) := by
    simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
      (fun _ : ℤ => (2 : ℂ)⁻¹) hf
  have hhalfmirror : Function.HasFiniteSupport
      (fun j : ℤ => (2 : ℂ)⁻¹ • f (m-j-1)) := by
    simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
      (fun _ : ℤ => (2 : ℂ)⁻¹) hmirror
  have csupport : Function.support c ⊆ (Finset.Ico (0 : ℤ) m) := by
    intro j hj
    have h : 0 ≤ j ∧ j < m := by by_contra h; exact hj (by simp [c,h])
    simpa only [Finset.mem_coe, Finset.mem_Ico] using h
  have hc : Function.HasFiniteSupport c := (Finset.Ico (0 : ℤ) m).finite_toSet.subset csupport
  have gsum : (∑ᶠ j : ℤ, g j) = rawL D H m 1 * halfCreationCoeff D a d := by
    have result := map_finsum (LinearMap.mulRight ℂ (halfCreationCoeff D a d))
      (groundPair_finite D H m)
    simpa only [LinearMap.mulRight_apply, groundPair_sum] using result.symm
  have csum : (∑ᶠ j : ℤ, c j) = ∑ j ∈ Finset.Ico (0 : ℤ) m,
      ((bilinear D a a : ℂ)/2) • halfCreationCoeff D a (d-2*m) := by
    rw [finsum_eq_sum_of_support_subset _ csupport]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [c, if_pos (Finset.mem_Ico.mp hj)]
  have mirror_sum : (∑ᶠ j : ℤ, f (m-j-1)) = ∑ᶠ j : ℤ, f j :=
    finsum_comp_equiv mirror
  rw [rawL_contracted]
  simp_rw [contractedPair_coherent D H hHG hGH]
  change (∑ᶠ j : ℤ, (g j + (2 : ℂ)⁻¹ • f j + (2 : ℂ)⁻¹ • f (m-j-1) + c j)) = _
  have split1 := finsum_add_distrib ((hg.add hhalf).add hhalfmirror) hc
  have split2 := finsum_add_distrib (hg.add hhalf) hhalfmirror
  have split3 := finsum_add_distrib hg hhalf
  simp only [Pi.add_def] at split1 split2 split3
  rw [split1, split2, split3, ← smul_finsum' _ hf,
    ← smul_finsum' _ hmirror, gsum, csum, mirror_sum]
  rw [show rawL D H m 1 * halfCreationCoeff D a d +
      (2 : ℂ)⁻¹ • (∑ᶠ j : ℤ, f j) + (2 : ℂ)⁻¹ • (∑ᶠ j : ℤ, f j) =
      rawL D H m 1 * halfCreationCoeff D a d + (∑ᶠ j : ℤ, f j) by module]
  rw [mixedLeft_sum]

private theorem creation_tail_recurrence (D : LatticeData) (a : Charge D) (R : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range (R.toNat+1),
      if N ≤ n then linearCreation D a n * halfCreationCoeff D a (R-(2*n+1 : ℕ)) else 0) +
    (∑ n ∈ Finset.range N,
      linearCreation D a n * halfCreationCoeff D a (R-(2*n+1 : ℕ))) =
        ((R : ℂ)/2) • halfCreationCoeff D a R := by
  classical
  let f : ℕ → Oscillator D := fun n => linearCreation D a n *
    halfCreationCoeff D a (R-(2*n+1 : ℕ))
  have support : Function.support f ⊆ Finset.range (R.toNat+1) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hn (by dsimp only [f]; rw [creation_negative D a _ (by omega), mul_zero])
  have highsupport : Function.support (fun n => if N ≤ n then f n else 0) ⊆
      Finset.range (R.toNat+1) := by
    intro n hn
    apply support
    intro h
    exact hn (by simp [h])
  have lowsupport : Function.support (fun n => if n < N then f n else 0) ⊆
      Finset.range N := by
    intro n hn
    by_contra h
    exact hn (by simp [show ¬ n < N by simpa using h])
  have highfinite : Function.HasFiniteSupport (fun n => if N ≤ n then f n else 0) :=
    (Finset.range (R.toNat+1)).finite_toSet.subset highsupport
  have lowfinite : Function.HasFiniteSupport (fun n => if n < N then f n else 0) :=
    (Finset.range N).finite_toSet.subset lowsupport
  have lowsum : (∑ᶠ n : ℕ, if n < N then f n else 0) = ∑ n ∈ Finset.range N, f n := by
    rw [finsum_eq_sum_of_support_subset _ lowsupport]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos (Finset.mem_range.mp hn)]
  rw [← creation_recurrence D a R]
  change _ + (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range (R.toNat+1), f n
  rw [← finsum_eq_sum_of_support_subset _ highsupport, ← lowsum,
    ← finsum_eq_sum_of_support_subset _ support, ← finsum_add_distrib highfinite lowfinite]
  apply finsum_congr
  intro n
  by_cases hn : N ≤ n
  · simp [hn, show ¬ n < N by omega]
  · simp [hn, show n < N by omega]

private theorem negative_ground_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    rawL D H (-1) 1 = quadraticCreation D H 0 0 := by
  rw [rawL_ground_negative D H (-1) (by omega)]
  simp [quadraticCreation]

private theorem negative_ground_two (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    rawL D H (-2) 1 = quadraticCreation D H 1 0 + quadraticCreation D H 0 1 := by
  rw [rawL_ground_negative D H (-2) (by omega)]
  have interval : Finset.Icc (-2 : ℤ) (-1) = {-2,-1} := by decide
  simp [interval, quadraticCreation, Finset.sum_add_distrib, smul_add]

private theorem translated_ground_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (d : ℤ) :
    oscillatorCoefficient D a (d-chargeNorm D a) (rawL D H (-1) 1) =
      rawL D H (-1) 1 * halfCreationCoeff D a d -
      linearCreation D a 0 * halfCreationCoeff D a (d+1) +
      ((bilinear D a a : ℂ)/2) • halfCreationCoeff D a (d+2) := by
  rw [negative_ground_one, oscillator_quadratic D H hHG hGH]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero,
    mul_zero, zero_add, sub_add_cancel,
    show d+1+1=d+2 by omega]
  module

private theorem translated_ground_two (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (d : ℤ) :
    oscillatorCoefficient D a (d-chargeNorm D a) (rawL D H (-2) 1) =
      rawL D H (-2) 1 * halfCreationCoeff D a d -
      linearCreation D a 0 * halfCreationCoeff D a (d+3) -
      linearCreation D a 1 * halfCreationCoeff D a (d+1) +
      (bilinear D a a : ℂ) • halfCreationCoeff D a (d+4) := by
  rw [negative_ground_two, map_add, oscillator_quadratic D H hHG hGH,
    oscillator_quadratic D H hHG hGH]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero,
    Nat.cast_ofNat, mul_zero, mul_one, zero_add, sub_add_cancel,
    show d+1+3=d+4 by omega, show d+3+1=d+4 by omega]
  rw [add_mul]
  module

/- These are exactly the four generator seeds, with every signed d retained.
   In particular d=-2 and d=-4 retain the translated double contraction. -/
private theorem generator_coherent_seed (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m : ℤ) (hm : m=1 ∨ m=2 ∨ m= -1 ∨ m= -2) (d : ℤ) :
    rawL D H m (halfCreationCoeff D a d) -
      oscillatorCoefficient D a (d-chargeNorm D a) (rawL D H m 1) =
        (((d-2*m+m*bilinear D a a : ℤ) : ℂ)/2) •
          halfCreationCoeff D a (d-2*m) := by
  classical
  rcases hm with h | h | h | h <;> subst m
  · rw [rawL_coherent D H hHG hGH, rawL_ground_nonnegative D H 1 (by omega),
      map_zero, zero_mul, sub_zero]
    norm_num only [Int.reduceNeg, max_eq_right (by omega : (-1 : ℤ) ≤ 0),
      Int.toNat_zero, Nat.zero_le, ite_true, zero_add]
    rw [creation_recurrence]
    have interval : Finset.Ico (0 : ℤ) 1 = {0} := by decide
    simp only [interval, Finset.sum_singleton]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat]
    module
  · rw [rawL_coherent D H hHG hGH, rawL_ground_nonnegative D H 2 (by omega),
      map_zero, zero_mul, sub_zero]
    norm_num only [Int.reduceNeg, max_eq_right (by omega : (-2 : ℤ) ≤ 0),
      Int.toNat_zero, Nat.zero_le, ite_true, zero_add]
    rw [creation_recurrence]
    have interval : Finset.Ico (0 : ℤ) 2 = {0,1} := by decide
    simp only [interval, Finset.sum_insert, Finset.mem_singleton, Int.zero_ne_one,
      not_false_eq_true, Finset.sum_singleton]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat]
    module
  · have tail := creation_tail_recurrence D a (d+2) 1
    have low : (∑ n ∈ Finset.range 1, linearCreation D a n *
        halfCreationCoeff D a (d+2-(2*n+1 : ℕ))) =
        linearCreation D a 0 * halfCreationCoeff D a (d+1) := by
      norm_num [Finset.sum_range_succ, show d+2-1=d+1 by omega]
    rw [low] at tail
    have tail_eq := eq_sub_of_add_eq tail
    rw [rawL_coherent D H hHG hGH, translated_ground_one D H hHG hGH]
    norm_num only [Int.reduceNeg, max_eq_left (by omega : (0 : ℤ) ≤ 1),
      Int.toNat_one, Finset.Ico_eq_empty_of_le (by omega : (-1 : ℤ) ≤ 0),
      Finset.sum_empty, mul_neg, mul_one, sub_neg_eq_add, add_zero]
    rw [tail_eq]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_one, Int.cast_ofNat]
    module
  · have tail := creation_tail_recurrence D a (d+4) 2
    have low : (∑ n ∈ Finset.range 2, linearCreation D a n *
        halfCreationCoeff D a (d+4-(2*n+1 : ℕ))) =
        linearCreation D a 0 * halfCreationCoeff D a (d+3) +
        linearCreation D a 1 * halfCreationCoeff D a (d+1) := by
      norm_num [Finset.sum_range_succ, show d+4-1=d+3 by omega, show d+4-3=d+1 by omega]
    rw [low] at tail
    have tail_eq := eq_sub_of_add_eq tail
    rw [rawL_coherent D H hHG hGH, translated_ground_two D H hHG hGH]
    norm_num only [Int.reduceNeg, max_eq_left (by omega : (0 : ℤ) ≤ 2),
      show (2 : ℤ).toNat = 2 by rfl, Finset.Ico_eq_empty_of_le (by omega : (-2 : ℤ) ≤ 0),
      Finset.sum_empty, mul_neg, Int.reduceMul, sub_neg_eq_add, add_zero]
    rw [tail_eq]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_one, Int.cast_ofNat]
    module

/- The scalar is kept in the native cover exponent.  In particular there is
   no rank/16 contribution to the charged primary weight. -/
private def wardScalar (D : LatticeData) (a : Charge D) (m e : ℤ) : ℂ :=
  ((e - 2*m + (m+1)*bilinear D a a : ℤ) : ℂ) / 2

private def wardResidual (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D) (m e : ℤ) :
    Module.End ℂ (Oscillator D) :=
  ⁅L D H m, oscillatorCoefficient D a e⁆ -
    wardScalar D a m e • oscillatorCoefficient D a (e-2*m)

private theorem oscillator_current_bracket (D : LatticeData) (i : Fin D.rank)
    (a : Charge D) (j e : ℤ) :
    ⁅current D i j, oscillatorCoefficient D a e⁆ =
      (bilinear D (unitCharge D i) a : ℂ) •
        oscillatorCoefficient D a (e-(2*j+1)) := by
  apply LinearMap.ext
  intro p
  exact oscillator_current_ward D i a j e p

private theorem current_residual_bracket (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m e j : ℤ) (i : Fin D.rank) :
    ⁅current D i j, wardResidual D H a m e⁆ =
      (bilinear D (unitCharge D i) a : ℂ) •
        wardResidual D H a m (e-(2*j+1)) := by
  have jl : ⁅current D i j, L D H m⁆ =
      frequency j • current D i (m+j) := by
    rw [← lie_skew, show ⁅L D H m, current D i j⁆ =
      -frequency j • current D i (m+j) from L_current_commutator D H hHG hGH i m j]
    simp
  have scalar : frequency j + wardScalar D a m (e-(2*j+1)) -
      wardScalar D a m e = 0 := by
    simp only [wardScalar, frequency, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_one, Int.cast_ofNat]
    ring
  have shift : e-(2*(m+j)+1) = (e-(2*j+1))-2*m := by omega
  have shift' : (e-2*m)-(2*j+1) = (e-(2*j+1))-2*m := by omega
  rw [wardResidual, lie_sub, lie_smul, leibniz_lie, jl,
    smul_lie, oscillator_current_bracket, oscillator_current_bracket,
    lie_smul, oscillator_current_bracket, shift, shift']
  dsimp only [wardResidual]
  simp only [smul_sub, smul_smul]
  have ke : wardScalar D a m e = frequency j +
      wardScalar D a m (e-(2*j+1)) := by linear_combination -scalar
  rw [ke]
  module

/- All exponents belong to the induction predicate.  This is essential:
   multiplication by a creation variable changes the exponent in the residual. -/
private theorem oscillator_ward_of_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m : ℤ)
    (ground : ∀ e : ℤ, wardResidual D H a m e 1 = 0) :
    ∀ (p : Oscillator D) (e : ℤ), wardResidual D H a m e p = 0 := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c =>
    intro e
    rw [MvPolynomial.C_eq_smul_one,
      map_smul, ground e, smul_zero]
  | add p q hp hq =>
    intro e
    rw [map_add, hp e, hq e, add_zero]
  | mul_X p x hp =>
    intro e
    have bracket := congrArg (fun A : Module.End ℂ (Oscillator D) => A p)
      (current_residual_bracket D H hHG hGH a m e (-(x.2 : ℤ)-1) x.1)
    rw [current_negative] at bracket
    change MvPolynomial.X x * wardResidual D H a m e p -
      wardResidual D H a m e (MvPolynomial.X x * p) =
        (bilinear D (unitCharge D x.1) a : ℂ) •
          wardResidual D H a m (e-(2*(-(x.2 : ℤ)-1)+1)) p at bracket
    rw [hp e, hp _, mul_zero, smul_zero, zero_sub] at bracket
    simpa only [mul_comm, neg_eq_zero] using bracket

private def OscillatorWard (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D) (m : ℤ) : Prop :=
  ∀ e : ℤ, ⁅L D H m, oscillatorCoefficient D a e⁆ =
    wardScalar D a m e • oscillatorCoefficient D a (e-2*m)

private theorem wardScalar_bracket (D : LatticeData) (a : Charge D) (r s e : ℤ) :
    wardScalar D a s e * wardScalar D a r (e-2*s) -
      wardScalar D a r e * wardScalar D a s (e-2*r) =
        ((r : ℂ)-(s : ℂ)) * wardScalar D a (r+s) e := by
  simp only [wardScalar, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_one, Int.cast_ofNat]
  ring

private theorem oscillator_ward_add (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (r s : ℤ) (different : r ≠ s)
    (hr : OscillatorWard D H a r) (hs : OscillatorWard D H a s) :
    OscillatorWard D H a (r+s) := by
  intro e
  have jacobi := lie_lie (L D H r) (L D H s) (oscillatorCoefficient D a e)
  have vir : ⁅L D H r, L D H s⁆ =
      ((r : ℂ)-(s : ℂ)) • L D H (r+s) +
      (if r+s = 0 then ((D.rank : ℂ)/12)*((r : ℂ)^3-(r : ℂ)) else 0) • 1 :=
    L_virasoro D H hHG hGH r s
  rw [vir, add_lie, smul_lie, smul_lie, hs e, hr e,
    lie_smul, lie_smul, hr _, hs _] at jacobi
  have central : ⁅(1 : Module.End ℂ (Oscillator D)), oscillatorCoefficient D a e⁆ = 0 := by
    apply LinearMap.ext
    intro p
    change (oscillatorCoefficient D a e) p - (oscillatorCoefficient D a e) p = 0
    exact sub_self _
  rw [central, smul_zero, add_zero, smul_smul, smul_smul,
    show (e-2*s)-2*r = e-2*(r+s) by omega,
    show (e-2*r)-2*s = e-2*(r+s) by omega,
    ← sub_smul, wardScalar_bracket] at jacobi
  rw [← smul_smul] at jacobi
  exact (smul_right_injective _ (sub_ne_zero.mpr
    (by exact_mod_cast different : (r : ℂ) ≠ (s : ℂ)))) jacobi

/- The four native seeds generate the whole Virasoro/Witt action.  The central
   identity in L_virasoro commutes, so no central charge enters wardScalar. -/
private theorem oscillator_ward_all_modes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D)
    (p1 : OscillatorWard D H a 1) (p2 : OscillatorWard D H a 2)
    (n1 : OscillatorWard D H a (-1)) (n2 : OscillatorWard D H a (-2)) :
    ∀ m : ℤ, OscillatorWard D H a m := by
  have zero : OscillatorWard D H a 0 := by
    simpa using oscillator_ward_add D H hHG hGH a 1 (-1) (by omega) p1 n1
  have positive : ∀ n : ℕ, OscillatorWard D H a (n+2) := by
    intro n
    induction n with
    | zero => exact p2
    | succ n ih =>
      have step := oscillator_ward_add D H hHG hGH a 1 ((n : ℤ)+2) (by omega) p1 ih
      have mode : (1 : ℤ)+((n : ℤ)+2) = (n.succ : ℤ)+2 := by omega
      rw [mode] at step
      exact step
  have negative : ∀ n : ℕ, OscillatorWard D H a (-(n+2)) := by
    intro n
    induction n with
    | zero => exact n2
    | succ n ih =>
      have step := oscillator_ward_add D H hHG hGH a (-1) (-((n : ℤ)+2)) (by omega) n1 ih
      have mode : (-1 : ℤ)+(-((n : ℤ)+2)) = -((n.succ : ℤ)+2) := by omega
      rw [mode] at step
      exact step
  intro m
  by_cases hp : 2 ≤ m
  · convert positive (m-2).toNat using 1 <;> omega
  · by_cases hn : m ≤ -2
    · convert negative (-m-2).toNat using 1 <;> omega
    · have cases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
      rcases cases with h | h | h <;> subst m
      · exact n1
      · exact zero
      · exact p1

private theorem oscillator_ward_generator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m : ℤ) (hm : m=1 ∨ m=2 ∨ m= -1 ∨ m= -2) :
    OscillatorWard D H a m := by
  have ground (e : ℤ) : wardResidual D H a m e 1 = 0 := by
    have nonzero : m ≠ 0 := by rcases hm with h | h | h | h <;> omega
    have seed := generator_coherent_seed D H hHG hGH a m hm (e+chargeNorm D a)
    have shift : e+chargeNorm D a-2*m = (e-2*m)+chargeNorm D a := by omega
    have coefficient : e+chargeNorm D a-2*m+m*bilinear D a a =
        e-2*m+(m+1)*bilinear D a a := by unfold chargeNorm; ring
    rw [show e+chargeNorm D a-chargeNorm D a=e by omega, coefficient, shift] at seed
    change L D H m (oscillatorCoefficient D a e 1) -
      oscillatorCoefficient D a e (L D H m 1) -
        wardScalar D a m e • oscillatorCoefficient D a (e-2*m) 1 = 0
    simp only [L, nonzero, if_false, zero_smul, add_zero, oscillator_one]
    exact sub_eq_zero.mpr seed
  intro e
  apply sub_eq_zero.mp
  apply LinearMap.ext
  intro p
  exact oscillator_ward_of_ground D H hHG hGH a m ground p e

/- proof_shape: charged_tensor_virasoro_ward: content
   admission_basis: escape-witness
   escape_witness: Signed coherent normal action, including the actual negative
   quadratic translation, propagates through one all-exponent polynomial
   residual induction; the native Virasoro bracket then generates every integer
   mode from ±1 and ±2. Neither primary covariance nor a derivative law is
   assumed. The literal scalar and actual ground representation are preserved.
   Literature status: classical FLM twisted lattice construction; zero novelty.
   utility: none; this is a universal algebraic identity, not finite computation. -/
theorem charged_tensor_virasoro_ward (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m e : ℤ) (v : ActualTensor D hu) :
    tensorL D (ActualGround D hu) ((D.G⁻¹).map (Int.castRingHom ℂ)) m
        (chargedCoefficient D hu a e v) -
      chargedCoefficient D hu a e
        (tensorL D (ActualGround D hu) ((D.G⁻¹).map (Int.castRingHom ℂ)) m v) =
      (((e-2*m+(m+1)*bilinear D a a : ℤ) : ℂ)/2) •
        chargedCoefficient D hu a (e-2*m) v := by
  classical
  let H : Matrix (Fin D.rank) (Fin D.rank) ℂ := (D.G⁻¹).map (Int.castRingHom ℂ)
  have hHG : H * gramComplex D = 1 := by
    have hm := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
      M.map (Int.castRingHom ℂ)) (Matrix.nonsing_inv_mul D.G hu)
    change (D.G⁻¹.map (Int.castRingHom ℂ)) * (D.G.map (Int.castRingHom ℂ)) = 1
    rw [← Matrix.map_mul]
    simpa using hm
  have hGH : gramComplex D * H = 1 := by
    have hm := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
      M.map (Int.castRingHom ℂ)) (Matrix.mul_nonsing_inv D.G hu)
    change (D.G.map (Int.castRingHom ℂ)) * (D.G⁻¹.map (Int.castRingHom ℂ)) = 1
    rw [← Matrix.map_mul]
    simpa using hm
  have allModes := oscillator_ward_all_modes D H hHG hGH a
    (oscillator_ward_generator D H hHG hGH a 1 (by omega))
    (oscillator_ward_generator D H hHG hGH a 2 (by omega))
    (oscillator_ward_generator D H hHG hGH a (-1) (by omega))
    (oscillator_ward_generator D H hHG hGH a (-2) (by omega))
  have tensor : tensorL D (ActualGround D hu) H m * chargedCoefficient D hu a e -
      chargedCoefficient D hu a e * tensorL D (ActualGround D hu) H m =
        wardScalar D a m e • chargedCoefficient D hu a (e-2*m) := by
    apply TensorProduct.ext'
    intro p t
    have oscillator := congrArg (fun A : Module.End ℂ (Oscillator D) => A p) (allModes m e)
    change L D H m (oscillatorCoefficient D a e p) -
      oscillatorCoefficient D a e (L D H m p) =
        wardScalar D a m e • oscillatorCoefficient D a (e-2*m) p at oscillator
    simp only [tensorL, tensorEnd, chargedCoefficient, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, map_smul]
    rw [← smul_sub, ← TensorProduct.sub_tmul, oscillator, TensorProduct.smul_tmul']
    rw [smul_comm]
    simp only [TensorProduct.smul_tmul']
  exact congrArg (fun A : Module.End ℂ (ActualTensor D hu) => A v) tensor

end

end D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

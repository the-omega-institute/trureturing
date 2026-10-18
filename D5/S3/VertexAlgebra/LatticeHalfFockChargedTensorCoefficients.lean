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

end D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

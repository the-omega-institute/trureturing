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
  rw [show (algebraMap ℂ (Polynomial (Oscillator D))) (MvPolynomial.coeff exponent polynomial) =
    Polynomial.C ((algebraMap ℂ (Oscillator D)) (MvPolynomial.coeff exponent polynomial)) by rfl,
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

private theorem charged_vacuum_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
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
    change MvPolynomial.coeff 0 (1 : Oscillator D) = 1
    simp
  simp only [one_coordinate, one_smul, map_zero, Finsupp.zero_apply] at coordinate
  apply nonzero
  have inverse := (groundRepresentation D hu).inv_self_apply (groundLift D charge) vector
  rw [show groundRepresentation D hu (groundLift D charge) vector = 0 from coordinate,
    map_zero] at inverse
  exact inverse.symm

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

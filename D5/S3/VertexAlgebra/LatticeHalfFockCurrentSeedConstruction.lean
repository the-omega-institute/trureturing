/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical minus-one current seed from the original charged correction. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeed

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCurrentNormalRecurrence
open LatticeHalfFockNormalCurrentAction LatticeHalfFockCurrentSeed
open LatticeHalfFockFirstDescendant LatticeHalfFockOriginalMixedIterate
open LatticeHalfFockAllStateCurrentCommutator MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

private theorem half_choose (degree : ℕ) :
    Ring.choose (1 / 2 : ℂ) (degree + 1) =
      halfBinomial degree / (2 * (degree + 1 : ℂ)) := by
  rw [binomial_product, Finset.prod_range_succ', halfBinomial, Nat.factorial_succ]
  have product : (∏ offset ∈ Finset.range degree, ((1 / 2 : ℂ) - ((offset + 1 : ℕ) : ℂ))) =
      ∏ offset ∈ Finset.range degree, ((-1 / 2 : ℂ) - (offset : ℂ)) := by
    apply Finset.prod_congr rfl
    intro offset member
    push_cast
    ring
  rw [product]
  have factorial : (degree.factorial : ℂ) ≠ 0 := by exact_mod_cast degree.factorial_ne_zero
  have successor : (degree + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
  push_cast
  field_simp
  ring

private theorem pairScalar_one (weight : ℕ) :
    pairScalar 1 weight = -(weight : ℂ) * Ring.choose (1 / 2 : ℂ) (weight + 1) := by
  rw [pairScalar, half_choose]
  have first : halfBinomial 1 = (-1 / 2 : ℂ) := by norm_num [halfBinomial]
  rw [first]
  have successor : (weight + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero weight
  simp only [Nat.cast_one, one_mul]
  rw [add_comm (1 : ℂ)]
  field_simp <;> ring

theorem finsum_nat_split {V : Type*} [AddCommGroup V] (term : ℕ → V)
    (finite : Function.HasFiniteSupport term) :
    (∑ᶠ degree, term degree) = term 0 + ∑ᶠ degree, term (degree + 1) := by
  have cover : insert 0 (Set.range Nat.succ) = Set.univ := by
    ext degree
    cases degree <;> simp
  rw [← finsum_mem_univ, ← cover,
    finsum_mem_insert' term (by simp) (finite.subset Set.inter_subset_right),
    finsum_mem_range Nat.succ_injective]

private def polynomialSeedTerm (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (polynomial : Oscillator D) (degree : ℕ) : NativeField D hu :=
  Ring.choose (1 / 2 : ℂ) (degree + 1) • shiftLinear D hu (degree + 1)
    (correctedPolynomial D hu charge (neutralPolynomialMode D colour charge degree polynomial))

private theorem polynomialSeed_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (polynomialSeedTerm D hu charge colour polynomial) := by
  apply (Finset.range (polynomialFrequencyBound D polynomial + 1)).finite_toSet.subset
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  exact nonzero (by simp [polynomialSeedTerm,
    neutralPolynomialMode_vanish D colour charge polynomial degree (by omega)])

private def pairFieldTerm (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (polynomial : Oscillator D) (other : Index D) : NativeField D hu :=
  (pairScalar 1 (sourceWeight D other) * (D.G colour other.1 : ℂ)) •
    shiftLinear D hu (1 + sourceWeight D other)
      (correctedPolynomial D hu charge (pderiv other polynomial))

private theorem pairField_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (pairFieldTerm D hu charge colour polynomial) := by
  classical
  apply polynomial.vars.finite_toSet.subset
  intro other nonzero
  by_contra outside
  exact nonzero (by simp [pairFieldTerm, pderiv_eq_zero_of_notMem_vars outside])

private theorem pairField_group (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (polynomial : Oscillator D) (degree : ℕ) :
    (∑ other : Fin D.rank, pairFieldTerm D hu charge colour polynomial (other, degree)) =
      -polynomialSeedTerm D hu charge colour polynomial (degree + 1) := by
  simp only [pairFieldTerm, sourceWeight, pairScalar_one, polynomialSeedTerm,
    Nat.cast_add, Nat.cast_one, neutralPolynomialMode_positive, LinearMap.smul_apply,
    weightedPartial, LinearMap.sum_apply, Derivation.coeFn_coe, map_smul, map_sum,
    Finset.smul_sum, smul_smul]
  rw [← Finset.sum_neg_distrib]
  simp only [← neg_smul]
  apply Finset.sum_congr rfl
  intro other member
  rw [show 1 + (degree + 1) = degree + 1 + 1 by omega]
  congr 1
  ring

private theorem pairField_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (polynomial : Oscillator D) :
    (∑ᶠ other : Index D, pairFieldTerm D hu charge colour polynomial other) =
      -(∑ᶠ degree : ℕ, polynomialSeedTerm D hu charge colour polynomial (degree + 1)) := by
  have finite := pairField_finite D hu charge colour polynomial
  rw [finsum_curry _ finite, finsum_eq_sum_of_fintype]
  rw [sum_finsum_comm Finset.univ _ (by
    intro other member
    exact finite.comp_of_injective (by
      intro first second equality
      exact congrArg Prod.snd equality))]
  simp only [pairField_group]
  rw [finsum_neg_distrib]

private theorem polynomial_seed (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (polynomial : Oscillator D) :
    correctedPolynomial D hu charge (polynomial * X (colour, 0)) +
      (∑ᶠ degree : ℕ, polynomialSeedTerm D hu charge colour polynomial degree) =
      normalInsertionLinear D hu (colour, 0) (correctedPolynomial D hu charge polynomial) := by
  have singleton : (halfBinomial 1 * (bilinear D (unitCharge D colour) charge : ℂ)) •
      shiftLinear D hu 1 (correctedPolynomial D hu charge polynomial) =
      -polynomialSeedTerm D hu charge colour polynomial 0 := by
    norm_num [halfBinomial, polynomialSeedTerm, neutralPolynomialMode, Ring.choose_one_right,
      map_smul, smul_smul, neg_smul]
  rw [correctedPolynomial_X_mul, sourceWeight]
  change normalInsertionLinear D hu (colour, 0) (correctedPolynomial D hu charge polynomial) +
      (halfBinomial 1 * (bilinear D (unitCharge D colour) charge : ℂ)) •
        shiftLinear D hu 1 (correctedPolynomial D hu charge polynomial) +
      (∑ᶠ other, pairFieldTerm D hu charge colour polynomial other) + _ = _
  rw [singleton, pairField_sum,
    finsum_nat_split _ (polynomialSeed_finite D hu charge colour polynomial)]
  abel

private def sourceSeedTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (degree : ℕ) : NativeField D hu :=
  Ring.choose (1 / 2 : ℂ) (degree + 1) • shiftLinear D hu (degree + 1)
    (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state))

private theorem sourceSeed_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) :
    Function.HasFiniteSupport (sourceSeedTerm D hu h state) := by
  apply (Finset.range (vectorFrequencyBound D state + 1)).finite_toSet.subset
  intro degree nonzero
  apply sourceCurrent_nat_support D h state
  intro zero
  exact nonzero (by simp [sourceSeedTerm, zero])

private theorem sourceSeed_single (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (charge : Charge D) (polynomial : Oscillator D) (degree : ℕ) :
    sourceSeedTerm D hu h (Finsupp.single charge polynomial) degree =
      ∑ colour, h colour • polynomialSeedTerm D hu charge colour polynomial degree := by
  have singlefield (source : Oscillator D) :
      Ytw D hu (Finsupp.single charge source) = correctedPolynomial D hu charge source := by
    simp [Ytw]
  simp only [sourceSeedTerm, sourceCurrent_single, Finsupp.single_finsetSum,
    map_sum, Finsupp.smul_single, map_smul, singlefield, Finset.smul_sum, polynomialSeedTerm]
  apply Finset.sum_congr rfl
  intro colour member
  exact smul_comm _ _ _

private theorem source_seed_field (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) :
    Ytw D hu (((sourceCurrent D h)[[-1]]) state) +
      (∑ᶠ degree : ℕ, sourceSeedTerm D hu h state degree) =
      ∑ colour, h colour • normalInsertionLinear D hu (colour, 0) (Ytw D hu state) := by
  classical
  induction state using Finsupp.induction_linear with
  | zero => simp [sourceSeedTerm]
  | single charge polynomial =>
    simp_rw [sourceSeed_single]
    rw [finsum_sum_comm Finset.univ _ (by
      intro colour member
      exact Function.HasFiniteSupport.smul_right (fun _ : ℕ => h colour)
        (polynomialSeed_finite D hu charge colour polynomial))]
    simp_rw [← smul_finsum' _ (polynomialSeed_finite D hu charge _ polynomial)]
    rw [sourceCurrent_single]
    have negative (colour : Fin D.rank) : neutralPolynomialMode D colour charge (-1) =
        LinearMap.mulLeft ℂ (X (colour, 0)) := by
      simpa using neutralPolynomialMode_negative D colour charge 0
    simp only [negative, LinearMap.mulLeft_apply,
      Finsupp.single_finsetSum, map_sum, Finsupp.smul_single, map_smul,
      Ytw, LinearMap.coe_comp, Finsupp.lsum_apply, Finsupp.sum_single_index,
      map_zero, add_zero, ← Finset.sum_add_distrib, ← smul_add]
    apply Finset.sum_congr rfl
    intro colour member
    rw [mul_comm (X (colour, 0)) polynomial, polynomial_seed]
  | add first second firstProof secondProof =>
    have terms : sourceSeedTerm D hu h (first + second) =
        fun degree => sourceSeedTerm D hu h first degree +
          sourceSeedTerm D hu h second degree := by
      funext degree
      simp [sourceSeedTerm, map_add, smul_add]
    rw [terms, finsum_add_distrib (sourceSeed_finite D hu h first)
      (sourceSeed_finite D hu h second)]
    simp only [map_add, Finset.smul_sum, smul_add, Finset.sum_add_distrib]
    rw [← firstProof, ← secondProof]
    abel

theorem actual_current_seed (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (exponent : ℤ) :
    (Ytw D hu (((sourceCurrent D h)[[-1]]) state)).coeff exponent vector +
      (∑ᶠ degree : ℕ, Ring.choose (1 / 2 : ℂ) (degree + 1) •
        (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state)).coeff
          (exponent + 2 * degree + 2) vector) =
      ∑ colour, h colour •
        (normalInsertion D hu (colour, 0) (Ytw D hu state)).coeff exponent vector := by
  let evaluation : NativeField D hu →ₗ[ℂ] ActualTensor D hu :=
    { toFun := fun field => field.coeff exponent vector,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have equality := congrArg evaluation (source_seed_field D hu h state)
  have mapped : evaluation (∑ᶠ degree, sourceSeedTerm D hu h state degree) =
      ∑ᶠ degree, evaluation (sourceSeedTerm D hu h state degree) :=
    evaluation.toAddMonoidHom.map_finsum (sourceSeed_finite D hu h state)
  simp only [map_add, map_sum, map_smul, mapped] at equality
  have pointwise (degree : ℕ) : evaluation (sourceSeedTerm D hu h state degree) =
      Ring.choose (1 / 2 : ℂ) (degree + 1) •
        (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state)).coeff
          (exponent + 2 * degree + 2) vector := by
    simp only [evaluation, sourceSeedTerm, shiftLinear, shiftField, LinearMap.coe_mk,
      AddHom.coe_mk, map_smul, HVertexOperator.coeff_of_coeff, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  simp_rw [pointwise] at equality
  exact equality

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction.actual_current_seed

/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Pascal recurrences of the actual finite current residues. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeHalfFockFirstDescendant LatticeHalfFockOriginalMixedIterate
open LatticeHalfFockAllStateField LatticeHalfFockAllStateCurrentCommutator
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockCurrentSeedConstruction LatticeHalfFockCurrentBorcherds
open scoped BigOperators VertexOperator

noncomputable section

private def seedTerm (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) (degree : ℕ) :
    ActualTensor D hu := Ring.choose (LatticeHalfFock.frequency mode) (degree + 1) •
      (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state)).coeff
        (exponent + 2 * degree + 2) vector

private theorem seedTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (mode exponent : ℤ) : Function.HasFiniteSupport (seedTerm D hu h state vector mode exponent) := by
  apply (Finset.range (vectorFrequencyBound D state + 1)).finite_toSet.subset
  intro degree nonzero
  apply sourceCurrent_nat_support D h state
  intro zero
  exact nonzero (by simp [seedTerm, zero])

private def seedLeft (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) : ActualTensor D hu :=
  (Ytw D hu (((sourceCurrent D h)[[-1]]) state)).coeff exponent vector +
    ∑ᶠ degree : ℕ, seedTerm D hu h state vector mode exponent degree

private def seedRight (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) : ActualTensor D hu :=
  (∑ᶠ degree : ℕ, rightFirst D hu h state vector (-1) mode exponent degree) +
    ∑ᶠ degree : ℕ, rightSecond D hu h state vector (-1) mode exponent degree

private def splitIncrement (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) : ActualTensor D hu :=
  currentCombination D hu h mode ((Ytw D hu state).coeff (exponent + 2 * mode + 3) vector) -
    (Ytw D hu state).coeff (exponent + 2 * mode + 3) (currentCombination D hu h mode vector)

private theorem seedRight_step (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    seedRight D hu h state vector (mode + 1) exponent -
      seedRight D hu h state vector mode exponent =
      splitIncrement D hu h state vector mode exponent := by
  have firstShift (degree : ℕ) :
      rightFirst D hu h state vector (-1) (mode + 1) exponent (degree + 1) =
        rightFirst D hu h state vector (-1) mode exponent degree := by
    unfold rightFirst
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show mode + 1 + (-1) - ((degree : ℤ) + 1) = mode + (-1) - degree by omega,
      show exponent + 2 * (mode + 1) + 1 - 2 * ((degree : ℤ) + 1) =
        exponent + 2 * mode + 1 - 2 * degree by omega]
  have secondShift (degree : ℕ) :
      rightSecond D hu h state vector (-1) mode exponent (degree + 1) =
        rightSecond D hu h state vector (-1) (mode + 1) exponent degree := by
    unfold rightSecond
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show exponent + 2 * mode + 1 - 2 * (-1) + 2 * ((degree : ℤ) + 1) =
      exponent + 2 * (mode + 1) + 1 - 2 * (-1) + 2 * degree by omega,
      show mode + ((degree : ℤ) + 1) = mode + 1 + degree by omega]
  have first := finsum_nat_split _
    (rightFirst_finite D hu h state vector (-1) (mode + 1) exponent)
  have second := finsum_nat_split _
    (rightSecond_finite D hu h state vector (-1) mode exponent)
  simp_rw [firstShift] at first
  simp_rw [secondShift] at second
  have firstZero : rightFirst D hu h state vector (-1) (mode + 1) exponent 0 =
      currentCombination D hu h mode ((Ytw D hu state).coeff (exponent + 2 * mode + 3) vector) := by
    unfold rightFirst
    simp only [Nat.cast_zero, mul_zero]
    rw [show mode + 1 + (-1) - 0 = mode by omega,
      show exponent + 2 * (mode + 1) + 1 - 0 = exponent + 2 * mode + 3 by omega]
  have secondZero : rightSecond D hu h state vector (-1) mode exponent 0 =
      (Ytw D hu state).coeff (exponent + 2 * mode + 3) (currentCombination D hu h mode vector) := by
    unfold rightSecond
    simp only [Nat.cast_zero, mul_zero]
    rw [show exponent + 2 * mode + 1 - 2 * (-1) + 0 = exponent + 2 * mode + 3 by omega,
      add_zero]
  unfold seedRight splitIncrement
  rw [first, second, firstZero, secondZero]
  abel

private theorem seedLeft_step (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    seedLeft D hu h state vector (mode + 1) exponent -
      seedLeft D hu h state vector mode exponent =
      splitIncrement D hu h state vector mode exponent := by
  have frequency : LatticeHalfFock.frequency (mode + 1) = LatticeHalfFock.frequency mode + 1 := by
    simp [LatticeHalfFock.frequency]
    ring
  have difference (degree : ℕ) : seedTerm D hu h state vector (mode + 1) exponent degree -
      seedTerm D hu h state vector mode exponent degree =
      Ring.choose (LatticeHalfFock.frequency mode) degree •
        (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state)).coeff
          (exponent + 2 * degree + 2) vector := by
    rw [seedTerm, seedTerm, frequency, Ring.choose_succ_succ, add_smul, add_sub_cancel_right]
  have commutator := actual_current_Ytw_commutator D hu h state mode
    (exponent + 2 * mode + 3) vector
  have indices (degree : ℕ) : exponent + 2 * mode + 3 - (2 * mode + 1) + 2 * degree =
      exponent + 2 * degree + 2 := by omega
  simp_rw [indices] at commutator
  change splitIncrement D hu h state vector mode exponent = _ at commutator
  unfold seedLeft
  rw [show ∀ first second : ActualTensor D hu,
      ((Ytw D hu (((sourceCurrent D h)[[-1]]) state)).coeff exponent vector + first) -
        ((Ytw D hu (((sourceCurrent D h)[[-1]]) state)).coeff exponent vector + second) =
        first - second by intros; abel]
  rw [← finsum_sub_distrib (seedTerm_finite D hu h state vector (mode + 1) exponent)
    (seedTerm_finite D hu h state vector mode exponent)]
  simp_rw [difference]
  exact commutator.symm

private theorem normal_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (exponent : ℤ) :
    (∑ colour, h colour •
      (normalInsertion D hu (colour, 0) (Ytw D hu state)).coeff exponent vector) =
        seedRight D hu h state vector 0 exponent := by
  simp only [normalInsertion, HVertexOperator.coeff_of_coeff, normalCoefficient,
    LinearMap.coe_mk, AddHom.coe_mk, smul_add, Finset.sum_add_distrib]
  simp_rw [smul_finsum' _ (negativeTerm_finite D hu _ (Ytw D hu state) exponent vector),
    smul_finsum' _ (positiveTerm_finite D hu _ (Ytw D hu state) exponent vector)]
  rw [sum_finsum_comm Finset.univ _ (by
    intro colour member
    exact Function.HasFiniteSupport.smul_right (fun _ : ℕ => h colour)
      (negativeTerm_finite D hu (colour, 0) (Ytw D hu state) exponent vector)),
    sum_finsum_comm Finset.univ _ (by
      intro colour member
      exact Function.HasFiniteSupport.smul_right (fun _ : ℕ => h colour)
        (positiveTerm_finite D hu (colour, 0) (Ytw D hu state) exponent vector))]
  unfold seedRight
  congr 1
  · apply finsum_congr
    intro degree
    simp only [negativeTerm, jetScalar, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, div_one, one_smul, rightFirst,
      currentCombination, LinearMap.sum_apply, LinearMap.smul_apply, Nat.cast_zero,
      mul_zero, zero_add, add_zero]
    rw [show -(degree : ℤ) - 1 = -1 - degree by omega,
      show exponent - 2 * (degree : ℤ) + 1 = exponent + 1 - 2 * degree by omega]
  · apply finsum_congr
    intro degree
    simp only [positiveTerm, jetScalar, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, div_one, one_smul, rightSecond,
      currentCombination, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Nat.cast_zero, mul_zero, zero_add, add_zero]
    rw [show exponent + 2 * (degree : ℤ) + 3 =
      exponent + 1 - 2 * (-1) + 2 * degree by omega]

private theorem seed_signed (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    seedLeft D hu h state vector mode exponent = seedRight D hu h state vector mode exponent := by
  have base : seedLeft D hu h state vector 0 exponent = seedRight D hu h state vector 0 exponent := by
    have seed := actual_current_seed D hu h state vector exponent
    rw [normal_zero] at seed
    simpa only [seedLeft, seedTerm, LatticeHalfFock.frequency, Int.cast_zero, zero_add] using seed
  have invariant (mode : ℤ) : seedLeft D hu h state vector (mode + 1) exponent -
      seedRight D hu h state vector (mode + 1) exponent =
      seedLeft D hu h state vector mode exponent - seedRight D hu h state vector mode exponent := by
    have first := seedLeft_step D hu h state vector mode exponent
    have second := seedRight_step D hu h state vector mode exponent
    exact sub_eq_sub_iff_sub_eq_sub.mp (first.trans second.symm)
  apply sub_eq_zero.mp
  induction mode using Int.induction_on with
  | zero => exact sub_eq_zero.mpr base
  | succ offset previous => rw [invariant, previous]
  | pred offset previous =>
    have equality := invariant (-(offset : ℤ) - 1)
    rw [show -(offset : ℤ) - 1 + 1 = -(offset : ℤ) by omega, previous] at equality
    exact equality.symm

private theorem left_minus_one (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    leftResidue D hu h state vector (-1) mode exponent =
      seedLeft D hu h state vector mode exponent := by
  have zero : leftTerm D hu h state vector (-1) mode exponent 0 =
      (Ytw D hu (((sourceCurrent D h)[[-1]]) state)).coeff exponent vector := by
    simp [leftTerm]
  have tail (degree : ℕ) : leftTerm D hu h state vector (-1) mode exponent (degree + 1) =
      seedTerm D hu h state vector mode exponent degree := by
    simp only [leftTerm, seedTerm, Nat.cast_add, Nat.cast_one]
    rw [show (-1 : ℤ) + ((degree : ℤ) + 1) = degree by omega,
      show exponent + 2 * ((degree : ℤ) + 1) = exponent + 2 * degree + 2 by omega]
  rw [leftResidue, finsum_nat_split _ (leftTerm_finite D hu h state vector (-1) mode exponent), zero]
  simp_rw [tail]
  rfl

private theorem right_minus_one (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    rightResidue D hu h state vector (-1) mode exponent =
      seedRight D hu h state vector mode exponent := by
  have phase (degree : ℕ) : (-1 : ℂ) ^ degree * Ring.choose (-1 : ℂ) degree = 1 := by
    rw [Ring.choose_neg', Ring.multichoose_one, Units.smul_def, zsmul_eq_mul,
      Int.cast_negOnePow_natCast, mul_one, ← mul_pow]
    simp
  have minus : (-1 : ℂ) ^ (-1 : ℤ) = -1 := by norm_num
  unfold rightResidue
  simp only [rightTerm, Int.cast_neg, Int.cast_one, phase, one_smul, minus,
    neg_one_smul, sub_neg_eq_add]
  exact finsum_add_distrib (rightFirst_finite D hu h state vector (-1) mode exponent)
    (rightSecond_finite D hu h state vector (-1) mode exponent)

theorem actual_current_minus_one_borcherds (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    leftResidue D hu h state vector (-1) mode exponent =
      rightResidue D hu h state vector (-1) mode exponent := by
  rw [left_minus_one, right_minus_one]
  exact seed_signed D hu h state vector mode exponent

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence


namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeHalfFockFirstDescendant LatticeHalfFockOriginalMixedIterate
open LatticeHalfFockAllStateField LatticeHalfFockAllStateCurrentCommutator
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockCurrentSeedConstruction LatticeHalfFockCurrentBorcherds
open scoped BigOperators VertexOperator

noncomputable section

private def binomialSum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℂ) (term : ℕ → V) : V := ∑ᶠ degree, Ring.choose scalar degree • term degree

private def alternatingSum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℂ) (term : ℕ → V) : V :=
  ∑ᶠ degree, ((-1 : ℂ) ^ degree * Ring.choose scalar degree) • term degree

private theorem binomial_difference {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℂ) (term : ℕ → V) (finite : Function.HasFiniteSupport term) :
    binomialSum (scalar + 1) term - binomialSum scalar term =
      binomialSum scalar (fun degree => term (degree + 1)) := by
  have first := finsum_nat_split (fun degree => Ring.choose (scalar + 1) degree • term degree)
    (Function.HasFiniteSupport.smul_right (fun degree => Ring.choose (scalar + 1) degree) finite)
  have second := finsum_nat_split (fun degree => Ring.choose scalar degree • term degree)
    (Function.HasFiniteSupport.smul_right (fun degree => Ring.choose scalar degree) finite)
  have tail (degree : ℕ) : Ring.choose (scalar + 1) (degree + 1) • term (degree + 1) =
      Ring.choose scalar degree • term (degree + 1) +
        Ring.choose scalar (degree + 1) • term (degree + 1) := by
    rw [Ring.choose_succ_succ, add_smul]
  have shifted := finite.comp_of_injective Nat.succ_injective
  simp_rw [tail] at first
  have finiteFirst : Function.HasFiniteSupport
      (fun degree => Ring.choose scalar degree • term (degree + 1)) :=
    (Function.HasFiniteSupport.smul_right (fun degree => Ring.choose scalar degree) shifted)
  have finiteSecond : Function.HasFiniteSupport
      (fun degree => Ring.choose scalar (degree + 1) • term (degree + 1)) :=
    (Function.HasFiniteSupport.smul_right (fun degree => Ring.choose scalar (degree + 1)) shifted)
  rw [finsum_add_distrib finiteFirst finiteSecond] at first
  unfold binomialSum
  rw [first, second]
  simp only [Ring.choose_zero_right, one_smul]
  abel

private theorem alternating_pascal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℂ) (term : ℕ → V) (finite : Function.HasFiniteSupport term) :
    alternatingSum (scalar + 1) term = alternatingSum scalar term -
      alternatingSum scalar (fun degree => term (degree + 1)) := by
  have first := finsum_nat_split
    (fun degree => ((-1 : ℂ) ^ degree * Ring.choose (scalar + 1) degree) • term degree)
    (Function.HasFiniteSupport.smul_right
    (fun degree => (-1 : ℂ) ^ degree * Ring.choose (scalar + 1) degree) finite)
  have second := finsum_nat_split
    (fun degree => ((-1 : ℂ) ^ degree * Ring.choose scalar degree) • term degree)
    (Function.HasFiniteSupport.smul_right
    (fun degree => (-1 : ℂ) ^ degree * Ring.choose scalar degree) finite)
  have tail (degree : ℕ) :
      ((-1 : ℂ) ^ (degree + 1) * Ring.choose (scalar + 1) (degree + 1)) • term (degree + 1) =
      ((-1 : ℂ) ^ (degree + 1) * Ring.choose scalar (degree + 1)) • term (degree + 1) -
        ((-1 : ℂ) ^ degree * Ring.choose scalar degree) • term (degree + 1) := by
    rw [← sub_smul]
    congr 1
    rw [Ring.choose_succ_succ, pow_succ]
    ring
  have shifted := finite.comp_of_injective Nat.succ_injective
  simp_rw [tail] at first
  have finiteFirst : Function.HasFiniteSupport (fun degree =>
      ((-1 : ℂ) ^ (degree + 1) * Ring.choose scalar (degree + 1)) • term (degree + 1)) :=
    (Function.HasFiniteSupport.smul_right
      (fun degree => (-1 : ℂ) ^ (degree + 1) * Ring.choose scalar (degree + 1)) shifted)
  have finiteSecond : Function.HasFiniteSupport (fun degree =>
      ((-1 : ℂ) ^ degree * Ring.choose scalar degree) • term (degree + 1)) :=
    (Function.HasFiniteSupport.smul_right
      (fun degree => (-1 : ℂ) ^ degree * Ring.choose scalar degree) shifted)
  rw [finsum_sub_distrib finiteFirst finiteSecond] at first
  unfold alternatingSum
  rw [first, second]
  simp only [Ring.choose_zero_right, pow_zero, one_mul, one_smul]
  abel

private theorem source_sequence_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order exponent : ℤ) :
    Function.HasFiniteSupport (fun degree : ℕ =>
      (Ytw D hu (((sourceCurrent D h)[[order + degree]]) state)).coeff
        (exponent + 2 * degree) vector) := by
  apply (Finset.range (((vectorFrequencyBound D state : ℤ) - order).toNat + 1)).finite_toSet.subset
  intro degree nonzero
  apply signed_source_support D h state order
  intro zero
  exact nonzero (by simp [zero])

theorem leftResidue_forward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    leftResidue D hu h state vector (order + 1) mode exponent =
      leftResidue D hu h state vector order (mode + 1) (exponent - 2) -
        leftResidue D hu h state vector order mode (exponent - 2) := by
  let term (degree : ℕ) := (Ytw D hu (((sourceCurrent D h)[[order + degree]]) state)).coeff
    (exponent - 2 + 2 * degree) vector
  have frequency : LatticeHalfFock.frequency (mode + 1) = LatticeHalfFock.frequency mode + 1 := by
    simp [LatticeHalfFock.frequency]
    ring
  have equal := binomial_difference (LatticeHalfFock.frequency mode) term
    (source_sequence_finite D hu h state vector order (exponent - 2))
  have shifted (degree : ℕ) : term (degree + 1) =
      (Ytw D hu (((sourceCurrent D h)[[order + 1 + degree]]) state)).coeff
        (exponent + 2 * degree) vector := by
    dsimp [term]
    rw [show order + ((degree : ℤ) + 1) = order + 1 + degree by omega,
      show exponent - 2 + 2 * ((degree : ℤ) + 1) = exponent + 2 * degree by omega]
  simp_rw [shifted] at equal
  simp only [leftResidue, leftTerm]
  rw [frequency]
  exact equal.symm

private theorem right_as_alternating (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    rightResidue D hu h state vector order mode exponent =
      alternatingSum (order : ℂ) (rightFirst D hu h state vector order mode exponent) -
        (-1 : ℂ) ^ order •
          alternatingSum (order : ℂ) (rightSecond D hu h state vector order mode exponent) := by
  have first : Function.HasFiniteSupport (fun degree : ℕ =>
      ((-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree) •
        rightFirst D hu h state vector order mode exponent degree) :=
    Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree)
      (rightFirst_finite D hu h state vector order mode exponent)
  have second : Function.HasFiniteSupport (fun degree : ℕ =>
      ((-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree) •
        rightSecond D hu h state vector order mode exponent degree) :=
    Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree)
      (rightSecond_finite D hu h state vector order mode exponent)
  have term (degree : ℕ) : rightTerm D hu h state vector order mode exponent degree =
      ((-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree) •
        rightFirst D hu h state vector order mode exponent degree -
      (-1 : ℂ) ^ order • (((-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree) •
        rightSecond D hu h state vector order mode exponent degree) := by
    rw [rightTerm, smul_sub]
    congr 1
    exact smul_comm _ _ _
  unfold rightResidue
  simp_rw [term]
  have scaledSecond : Function.HasFiniteSupport (fun degree : ℕ => (-1 : ℂ) ^ order •
      (((-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree) •
        rightSecond D hu h state vector order mode exponent degree)) :=
    Function.HasFiniteSupport.smul_right (fun _ : ℕ => (-1 : ℂ) ^ order) second
  rw [finsum_sub_distrib first scaledSecond, ← smul_finsum' _ second]
  rfl

theorem rightResidue_forward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    rightResidue D hu h state vector (order + 1) mode exponent =
      rightResidue D hu h state vector order (mode + 1) (exponent - 2) -
        rightResidue D hu h state vector order mode (exponent - 2) := by
  let first := rightFirst D hu h state vector (order + 1) mode exponent
  let second := rightSecond D hu h state vector (order + 1) mode exponent
  have firstNext : rightFirst D hu h state vector order (mode + 1) (exponent - 2) = first := by
    funext degree
    dsimp [rightFirst, first]
    rw [show mode + 1 + order - (degree : ℤ) = mode + (order + 1) - degree by omega,
      show exponent - 2 + 2 * (mode + 1) + 1 - 2 * (degree : ℤ) =
        exponent + 2 * mode + 1 - 2 * degree by omega]
  have firstPrevious : rightFirst D hu h state vector order mode (exponent - 2) =
      fun degree => first (degree + 1) := by
    funext degree
    dsimp [rightFirst, first]
    rw [show mode + order - (degree : ℤ) = mode + (order + 1) - ((degree : ℤ) + 1) by omega,
      show exponent - 2 + 2 * mode + 1 - 2 * (degree : ℤ) =
        exponent + 2 * mode + 1 - 2 * ((degree : ℤ) + 1) by omega]
  have secondNext : rightSecond D hu h state vector order (mode + 1) (exponent - 2) =
      fun degree => second (degree + 1) := by
    funext degree
    dsimp [rightSecond, second]
    rw [show exponent - 2 + 2 * (mode + 1) + 1 - 2 * order + 2 * (degree : ℤ) =
        exponent + 2 * mode + 1 - 2 * (order + 1) + 2 * ((degree : ℤ) + 1) by omega,
      show mode + 1 + (degree : ℤ) = mode + ((degree : ℤ) + 1) by omega]
  have secondPrevious : rightSecond D hu h state vector order mode (exponent - 2) = second := by
    funext degree
    dsimp [rightSecond, second]
    rw [show exponent - 2 + 2 * mode + 1 - 2 * order + 2 * (degree : ℤ) =
      exponent + 2 * mode + 1 - 2 * (order + 1) + 2 * degree by omega]
  have phase : (-1 : ℂ) ^ (order + 1) = -((-1 : ℂ) ^ order) := by
    rw [zpow_add₀ (by norm_num), zpow_one]
    ring
  rw [right_as_alternating, right_as_alternating, right_as_alternating,
    firstNext, firstPrevious, secondNext, secondPrevious]
  change alternatingSum ((order + 1 : ℤ) : ℂ) first -
      (-1 : ℂ) ^ (order + 1) • alternatingSum ((order + 1 : ℤ) : ℂ) second = _
  rw [Int.cast_add, Int.cast_one, phase, alternating_pascal _ first
    (rightFirst_finite D hu h state vector (order + 1) mode exponent),
    alternating_pascal _ second (rightSecond_finite D hu h state vector (order + 1) mode exponent),
    neg_smul, smul_sub]
  abel

theorem discrepancy_forward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    discrepancy D hu h state vector (order + 1) mode exponent =
      discrepancy D hu h state vector order (mode + 1) (exponent - 2) -
        discrepancy D hu h state vector order mode (exponent - 2) := by
  unfold discrepancy
  rw [leftResidue_forward, rightResidue_forward]
  abel

private theorem discrepancy_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    discrepancy D hu h state vector 0 mode exponent = 0 := by
  have tail (degree : ℕ) : rightTerm D hu h state vector 0 mode exponent (degree + 1) = 0 := by
    simp [rightTerm, Ring.choose_zero_succ]
  have rightZero : rightResidue D hu h state vector 0 mode exponent =
      currentCombination D hu h mode ((Ytw D hu state).coeff (exponent + 2 * mode + 1) vector) -
        (Ytw D hu state).coeff (exponent + 2 * mode + 1) (currentCombination D hu h mode vector) := by
    rw [rightResidue, finsum_nat_split _ (rightTerm_finite D hu h state vector 0 mode exponent)]
    simp_rw [tail]
    simp [rightTerm, rightFirst, rightSecond]
  have commutator := actual_current_Ytw_commutator D hu h state mode
    (exponent + 2 * mode + 1) vector
  have indices (degree : ℕ) : exponent + 2 * mode + 1 - (2 * mode + 1) + 2 * degree =
      exponent + 2 * degree := by omega
  simp_rw [indices] at commutator
  unfold discrepancy
  apply sub_eq_zero.mpr
  rw [rightZero]
  simpa only [leftResidue, leftTerm, zero_add] using commutator.symm

theorem actual_nonnegative_current_borcherds (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order : ℕ) (mode exponent : ℤ) :
    leftResidue D hu h state vector order mode exponent =
      rightResidue D hu h state vector order mode exponent := by
  have closed (order : ℕ) : ∀ mode exponent,
      discrepancy D hu h state vector order mode exponent = 0 := by
    induction order with
    | zero => exact discrepancy_zero D hu h state vector
    | succ order previous =>
      intro mode exponent
      rw [Nat.cast_add, Nat.cast_one, discrepancy_forward, previous, previous, sub_self]
  exact sub_eq_zero.mp (closed order mode exponent)

private theorem choose_next (scalar : ℂ) (degree : ℕ) :
    ((degree + 1 : ℕ) : ℂ) * Ring.choose scalar (degree + 1) =
      (scalar - degree) * Ring.choose scalar degree := by
  have identity := Ring.choose_smul_choose scalar (n := degree + 1) (k := degree)
    (Nat.le_succ degree)
  simpa [nsmul_eq_mul, Ring.choose_one_right, mul_comm] using identity

private theorem choose_lower (scalar : ℂ) (degree : ℕ) :
    ((degree + 1 : ℕ) : ℂ) * Ring.choose scalar (degree + 1) =
      scalar * Ring.choose (scalar - 1) degree := by
  have identity := Ring.choose_smul_choose scalar (n := degree + 1) (k := 1)
    (by omega)
  simpa [nsmul_eq_mul, Ring.choose_one_right] using identity

private theorem choose_complement (scalar : ℂ) (degree : ℕ) :
    (scalar - degree) * Ring.choose scalar degree =
      scalar * Ring.choose (scalar - 1) degree := by
  rw [← choose_next, choose_lower]

private theorem binomial_translation_balance {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar order : ℂ) (term : ℕ → V) (finite : Function.HasFiniteSupport term) :
    (∑ᶠ degree : ℕ, (((scalar - degree) * Ring.choose scalar degree) • term (degree + 1) -
      ((order + degree) * Ring.choose scalar degree) • term degree)) =
        -order • binomialSum scalar term := by
  have finiteShift := finite.comp_of_injective Nat.succ_injective
  have finiteA : Function.HasFiniteSupport (fun degree : ℕ =>
      ((scalar - degree) * Ring.choose scalar degree) • term (degree + 1)) := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (scalar - degree) * Ring.choose scalar degree) finiteShift
  have finiteB : Function.HasFiniteSupport (fun degree : ℕ =>
      ((order + degree) * Ring.choose scalar degree) • term degree) := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (order + degree) * Ring.choose scalar degree) finite
  have finiteIndex : Function.HasFiniteSupport (fun degree : ℕ =>
      ((degree : ℂ) * Ring.choose scalar degree) • term degree) := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (degree : ℂ) * Ring.choose scalar degree) finite
  have finiteChoose : Function.HasFiniteSupport (fun degree : ℕ =>
      Ring.choose scalar degree • term degree) := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => Ring.choose scalar degree) finite
  have split := finsum_nat_split
    (fun degree : ℕ => ((degree : ℂ) * Ring.choose scalar degree) • term degree) finiteIndex
  simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add] at split
  simp_rw [choose_next] at split
  have decomposition (degree : ℕ) :
      ((order + degree) * Ring.choose scalar degree) • term degree =
        order • (Ring.choose scalar degree • term degree) +
          ((degree : ℂ) * Ring.choose scalar degree) • term degree := by
    rw [add_mul, add_smul, mul_smul]
  rw [finsum_sub_distrib finiteA finiteB, ← split]
  simp_rw [decomposition]
  have finiteOrder : Function.HasFiniteSupport (fun degree : ℕ =>
      order • (Ring.choose scalar degree • term degree)) :=
    Function.HasFiniteSupport.smul_right (fun _ : ℕ => order) finiteChoose
  rw [finsum_add_distrib finiteOrder finiteIndex,
    ← smul_finsum' order finiteChoose]
  unfold binomialSum
  module

private theorem alternating_degree {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℂ) (term : ℕ → V) (finite : Function.HasFiniteSupport term) :
    (∑ᶠ degree, ((-1 : ℂ) ^ degree * Ring.choose scalar degree * degree) • term degree) =
      -scalar • alternatingSum (scalar - 1) (fun degree => term (degree + 1)) := by
  have weighted := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose scalar degree * degree) finite
  have split := finsum_nat_split
    (fun degree : ℕ => ((-1 : ℂ) ^ degree * Ring.choose scalar degree * degree) • term degree) weighted
  simp only [Nat.cast_zero, mul_zero, zero_smul, zero_add] at split
  rw [split]
  unfold alternatingSum
  have shifted := finite.comp_of_injective Nat.succ_injective
  have finiteWeighted : Function.HasFiniteSupport (fun degree : ℕ =>
      ((-1 : ℂ) ^ degree * Ring.choose (scalar - 1) degree) • term (degree + 1)) :=
    Function.HasFiniteSupport.smul_right
      (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose (scalar - 1) degree) shifted
  rw [smul_finsum' _ finiteWeighted]
  apply finsum_congr
  intro degree
  rw [← mul_smul]
  congr 1
  calc
    (-1 : ℂ) ^ (degree + 1) * Ring.choose scalar (degree + 1) * (degree + 1 : ℕ) =
        -((-1 : ℂ) ^ degree) * (((degree + 1 : ℕ) : ℂ) * Ring.choose scalar (degree + 1)) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [choose_lower]; ring

private theorem alternating_complement {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℂ) (term : ℕ → V) (finite : Function.HasFiniteSupport term) :
    (∑ᶠ degree, ((-1 : ℂ) ^ degree * Ring.choose scalar degree * (scalar - degree)) • term degree) =
      scalar • alternatingSum (scalar - 1) term := by
  unfold alternatingSum
  have finiteWeighted : Function.HasFiniteSupport (fun degree : ℕ =>
      ((-1 : ℂ) ^ degree * Ring.choose (scalar - 1) degree) • term degree) :=
    Function.HasFiniteSupport.smul_right
      (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose (scalar - 1) degree) finite
  rw [smul_finsum' _ finiteWeighted]
  apply finsum_congr
  intro degree
  rw [← mul_smul]
  congr 1
  calc
    (-1 : ℂ) ^ degree * Ring.choose scalar degree * (scalar - degree) =
      (-1 : ℂ) ^ degree * ((scalar - degree) * Ring.choose scalar degree) := by ring
    _ = _ := by rw [choose_complement]; ring

private theorem source_current_translation (D : LatticeData) (h : Fin D.rank → ℂ)
    (state : Carrier D) (mode : ℤ) :
    ((sourceCurrent D h)[[mode]]) (LatticeSugawaraConformal.translation D state) =
      LatticeSugawaraConformal.translation D (((sourceCurrent D h)[[mode]]) state) +
        (mode : ℂ) • ((sourceCurrent D h)[[mode - 1]]) state := by
  simp only [sourceCurrent_mode, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro colour member
  have covariance := congrArg (fun operator : Module.End ℂ (Carrier D) => operator state)
    (LatticeSugawaraConformal.neutral_translation_covariance D colour mode)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at covariance
  rw [sub_eq_iff_eq_add] at covariance
  rw [covariance]
  module

private theorem source_field_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (mode exponent : ℤ) :
    (Ytw D hu (((sourceCurrent D h)[[mode]]) (LatticeSugawaraConformal.translation D state))).coeff
      exponent vector =
        (((exponent + 2 : ℤ) : ℂ) / 2) •
          (Ytw D hu (((sourceCurrent D h)[[mode]]) state)).coeff (exponent + 2) vector +
        (mode : ℂ) • (Ytw D hu (((sourceCurrent D h)[[mode - 1]]) state)).coeff exponent vector := by
  rw [source_current_translation]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [LatticeHalfFockOriginalTranslation.Ytw_translation_physical]

theorem leftResidue_backward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    (-order : ℂ) • leftResidue D hu h state vector (order - 1) mode exponent =
      (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2) •
        leftResidue D hu h state vector order mode (exponent + 2) -
      leftResidue D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent := by
  let term (degree : ℕ) :=
    (Ytw D hu (((sourceCurrent D h)[[order - 1 + degree]]) state)).coeff
      (exponent + 2 * degree) vector
  have finite := source_sequence_finite D hu h state vector (order - 1) exponent
  have shifted (degree : ℕ) : term (degree + 1) =
      (Ytw D hu (((sourceCurrent D h)[[order + degree]]) state)).coeff
        (exponent + 2 + 2 * degree) vector := by
    dsimp [term]
    rw [show order - 1 + ((degree : ℤ) + 1) = order + degree by omega,
      show exponent + 2 * ((degree : ℤ) + 1) = exponent + 2 + 2 * degree by omega]
  have predecessor (degree : ℕ) :
      (Ytw D hu (((sourceCurrent D h)[[order + degree - 1]]) state)).coeff
        (exponent + 2 * degree) vector = term degree := by
    dsimp [term]
    rw [show order + degree - 1 = order - 1 + degree by omega]
  have termIdentity (degree : ℕ) :
      (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2) •
        leftTerm D hu h state vector order mode (exponent + 2) degree -
      leftTerm D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent degree =
        ((LatticeHalfFock.frequency mode - degree) * Ring.choose (LatticeHalfFock.frequency mode) degree) •
          term (degree + 1) -
        (((order : ℂ) + degree) * Ring.choose (LatticeHalfFock.frequency mode) degree) • term degree := by
    unfold leftTerm
    rw [source_field_translation,
      show exponent + 2 * degree + 2 = exponent + 2 + 2 * degree by omega,
      predecessor, ← shifted]
    simp only [LatticeHalfFock.frequency]
    push_cast
    module
  simp only [leftResidue]
  have finiteScaled : Function.HasFiniteSupport (fun degree : ℕ =>
      (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2) •
        leftTerm D hu h state vector order mode (exponent + 2) degree) :=
    Function.HasFiniteSupport.smul_right (fun _ : ℕ => (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2))
      (leftTerm_finite D hu h state vector order mode (exponent + 2))
  rw [smul_finsum' _ (leftTerm_finite D hu h state vector order mode (exponent + 2)),
    ← finsum_sub_distrib
      finiteScaled
      (leftTerm_finite D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent)]
  simp_rw [termIdentity]
  exact (binomial_translation_balance (LatticeHalfFock.frequency mode) (order : ℂ) term finite).symm

private theorem alternating_difference {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar multiplier : ℂ) (first second : ℕ → V)
    (finiteFirst : Function.HasFiniteSupport first) (finiteSecond : Function.HasFiniteSupport second) :
    multiplier • alternatingSum scalar first - alternatingSum scalar second =
      ∑ᶠ degree, ((-1 : ℂ) ^ degree * Ring.choose scalar degree) •
        (multiplier • first degree - second degree) := by
  unfold alternatingSum
  have weightedFirst : Function.HasFiniteSupport (fun degree : ℕ =>
      ((-1 : ℂ) ^ degree * Ring.choose scalar degree) • first degree) := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose scalar degree) finiteFirst
  have weightedSecond : Function.HasFiniteSupport (fun degree : ℕ =>
      ((-1 : ℂ) ^ degree * Ring.choose scalar degree) • second degree) := Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose scalar degree) finiteSecond
  have weightedMultiplier : Function.HasFiniteSupport (fun degree : ℕ =>
      multiplier • (((-1 : ℂ) ^ degree * Ring.choose scalar degree) • first degree)) :=
    Function.HasFiniteSupport.smul_right (fun _ : ℕ => multiplier) weightedFirst
  rw [smul_finsum' _ weightedFirst, ← finsum_sub_distrib weightedMultiplier weightedSecond]
  apply finsum_congr
  intro degree
  rw [smul_sub, smul_comm multiplier]

theorem rightResidue_backward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    (-order : ℂ) • rightResidue D hu h state vector (order - 1) mode exponent =
      (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2) •
        rightResidue D hu h state vector order mode (exponent + 2) -
      rightResidue D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent := by
  let multiplier := (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2)
  let first := rightFirst D hu h state vector order mode (exponent + 2)
  let second := rightSecond D hu h state vector order mode (exponent + 2)
  let firstT := rightFirst D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent
  let secondT := rightSecond D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent
  have firstIdentity (degree : ℕ) :
      multiplier • first degree - firstT degree = (degree : ℂ) • first degree := by
    dsimp [first, firstT, rightFirst, multiplier]
    rw [LatticeHalfFockOriginalTranslation.Ytw_translation_physical, map_smul]
    rw [show exponent + 2 * mode + 1 - 2 * degree + 2 =
      exponent + 2 + 2 * mode + 1 - 2 * degree by omega]
    push_cast
    module
  have secondIdentity (degree : ℕ) :
      multiplier • second degree - secondT degree = ((order : ℂ) - degree) • second degree := by
    dsimp [second, secondT, rightSecond, multiplier]
    rw [LatticeHalfFockOriginalTranslation.Ytw_translation_physical]
    rw [show exponent + 2 * mode + 1 - 2 * order + 2 * degree + 2 =
      exponent + 2 + 2 * mode + 1 - 2 * order + 2 * degree by omega]
    push_cast
    module
  have firstShift (degree : ℕ) : first (degree + 1) =
      rightFirst D hu h state vector (order - 1) mode exponent degree := by
    dsimp [first, rightFirst]
    rw [show mode + order - ((degree : ℤ) + 1) = mode + (order - 1) - degree by omega,
      show exponent + 2 + 2 * mode + 1 - 2 * ((degree : ℤ) + 1) =
        exponent + 2 * mode + 1 - 2 * degree by omega]
  have secondShift (degree : ℕ) : second degree =
      rightSecond D hu h state vector (order - 1) mode exponent degree := by
    dsimp [second, rightSecond]
    rw [show exponent + 2 + 2 * mode + 1 - 2 * order + 2 * degree =
      exponent + 2 * mode + 1 - 2 * (order - 1) + 2 * degree by omega]
  have firstBalance :
      multiplier • alternatingSum (order : ℂ) first - alternatingSum (order : ℂ) firstT =
        (-order : ℂ) • alternatingSum ((order - 1 : ℤ) : ℂ)
          (rightFirst D hu h state vector (order - 1) mode exponent) := by
    rw [alternating_difference _ _ first firstT
      (rightFirst_finite D hu h state vector order mode (exponent + 2))
      (rightFirst_finite D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent)]
    simp_rw [firstIdentity, ← mul_smul]
    rw [alternating_degree (order : ℂ) first
      (rightFirst_finite D hu h state vector order mode (exponent + 2))]
    simp_rw [firstShift]
    simp only [Int.cast_sub, Int.cast_one]
  have secondBalance :
      multiplier • alternatingSum (order : ℂ) second - alternatingSum (order : ℂ) secondT =
        (order : ℂ) • alternatingSum ((order - 1 : ℤ) : ℂ)
          (rightSecond D hu h state vector (order - 1) mode exponent) := by
    rw [alternating_difference _ _ second secondT
      (rightSecond_finite D hu h state vector order mode (exponent + 2))
      (rightSecond_finite D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent)]
    simp_rw [secondIdentity, ← mul_smul]
    rw [alternating_complement (order : ℂ) second
      (rightSecond_finite D hu h state vector order mode (exponent + 2))]
    rw [show second = rightSecond D hu h state vector (order - 1) mode exponent from funext secondShift]
    simp only [Int.cast_sub, Int.cast_one]
  have phase : (-1 : ℂ) ^ order = -((-1 : ℂ) ^ (order - 1)) := by
    have identity := zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num) (order - 1) 1
    rw [show order - 1 + 1 = order by omega] at identity
    simpa using identity
  rw [right_as_alternating, right_as_alternating, right_as_alternating]
  change (-order : ℂ) • (_ - _ • _) =
    multiplier • (alternatingSum (order : ℂ) first - (-1 : ℂ) ^ order • alternatingSum (order : ℂ) second) -
      (alternatingSum (order : ℂ) firstT - (-1 : ℂ) ^ order • alternatingSum (order : ℂ) secondT)
  symm
  calc
    _ = (multiplier • alternatingSum (order : ℂ) first - alternatingSum (order : ℂ) firstT) -
      (-1 : ℂ) ^ order • (multiplier • alternatingSum (order : ℂ) second - alternatingSum (order : ℂ) secondT) := by module
    _ = _ := by rw [firstBalance, secondBalance, phase]; module

theorem discrepancy_backward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    (-order : ℂ) • discrepancy D hu h state vector (order - 1) mode exponent =
      (((exponent + 2 * mode + 3 : ℤ) : ℂ) / 2) •
        discrepancy D hu h state vector order mode (exponent + 2) -
      discrepancy D hu h (LatticeSugawaraConformal.translation D state) vector order mode exponent := by
  unfold discrepancy
  rw [smul_sub, leftResidue_backward, rightResidue_backward, smul_sub]
  abel

theorem actual_signed_current_borcherds (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    leftResidue D hu h state vector order mode exponent =
      rightResidue D hu h state vector order mode exponent := by
  have negative (index : ℕ) : ∀ (source : Carrier D) mode exponent,
      discrepancy D hu h source vector (-(index : ℤ) - 1) mode exponent = 0 := by
    induction index with
    | zero =>
      intro source mode exponent
      unfold discrepancy
      exact sub_eq_zero.mpr (actual_current_minus_one_borcherds D hu h source vector mode exponent)
    | succ index inductionHypothesis =>
      intro source mode exponent
      have recurrence := discrepancy_backward D hu h source vector (-(index : ℤ) - 1) mode exponent
      rw [inductionHypothesis source, inductionHypothesis (LatticeSugawaraConformal.translation D source)] at recurrence
      have nonzero : (-(-(index : ℤ) - 1) : ℂ) ≠ 0 := by
        have positive : (0 : ℤ) < -(-(index : ℤ) - 1) := by omega
        exact_mod_cast (ne_of_gt positive)
      have zero : discrepancy D hu h source vector (-(index : ℤ) - 1 - 1) mode exponent = 0 :=
        (smul_eq_zero.mp (by
          simpa only [smul_zero, sub_zero, Int.cast_sub, Int.cast_neg, Int.cast_one]
            using recurrence)).resolve_left nonzero
      change discrepancy D hu h source vector (-((index + 1 : ℕ) : ℤ) - 1) mode exponent = 0
      rw [show -((index + 1 : ℕ) : ℤ) - 1 = -(index : ℤ) - 1 - 1 by omega]
      exact zero
  by_cases nonnegative : 0 ≤ order
  · have identity : (order.toNat : ℤ) = order := Int.toNat_of_nonneg nonnegative
    rw [← identity]
    exact actual_nonnegative_current_borcherds D hu h state vector order.toNat mode exponent
  · have identity : order = -(((-order - 1).toNat : ℕ) : ℤ) - 1 := by
      have cast := Int.toNat_of_nonneg (show 0 ≤ -order - 1 by omega)
      omega
    apply sub_eq_zero.mp
    change discrepancy D hu h state vector order mode exponent = 0
    rw [identity]
    exact negative _ state mode exponent

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_forward
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence.actual_nonnegative_current_borcherds
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_backward
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence.actual_signed_current_borcherds

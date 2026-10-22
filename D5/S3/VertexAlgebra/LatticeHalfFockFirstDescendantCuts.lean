/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Statewise finite signed current cuts for the actual charged field.
   Literature status: classical twisted lattice construction; zero novelty. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFirstDescendant LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open scoped BigOperators

noncomputable section

def cutSummand (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (a : Charge D) (exponent cut mode : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  if mode < cut then
    currentCombination D hu h mode * chargedCoefficient D hu a (exponent + 2 * mode + 3)
  else chargedCoefficient D hu a (exponent + 2 * mode + 3) * currentCombination D hu h mode

private theorem currentCombination_upper (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (vector : ActualTensor D hu) :
    ∃ cutoff : ℕ, ∀ mode : ℤ, (cutoff : ℤ) ≤ mode →
      currentCombination D hu h mode vector = 0 := by
  obtain ⟨cutoff, bound⟩ := LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  refine ⟨cutoff, ?_⟩
  intro mode high
  simp [currentCombination, LinearMap.sum_apply, bound, high]

theorem cutSummand_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (fun mode => cutSummand D hu h a exponent cut mode vector) := by
  classical
  obtain ⟨cutoff, upper⟩ := currentCombination_upper D hu h vector
  let lower := ((HahnModule.of ℂ).symm (chargedField D hu a vector)).order
  apply (Finset.Icc (min cut (min 0 (lower - exponent - 3)))
    (max cut (cutoff : ℤ))).finite_toSet.subset
  intro mode nonzero
  change cutSummand D hu h a exponent cut mode vector ≠ 0 at nonzero
  simp only [Finset.mem_coe, Finset.mem_Icc]
  by_cases negative : mode < cut
  · have coefficientNonzero : chargedCoefficient D hu a (exponent + 2 * mode + 3) vector ≠ 0 := by
      intro zero
      apply nonzero
      simp [cutSummand, negative, Module.End.mul_apply, zero]
    have bound : lower ≤ exponent + 2 * mode + 3 :=
      HahnSeries.order_le_of_coeff_ne_zero coefficientNonzero
    constructor <;> omega
  · have high : mode < (cutoff : ℤ) := by
      by_contra outside
      apply nonzero
      simp [cutSummand, negative, Module.End.mul_apply, upper mode (by omega)]
    constructor <;> omega

def cutProduct (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (a : Charge D) (exponent cut : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun vector := ∑ᶠ mode : ℤ, cutSummand D hu h a exponent cut mode vector
  map_add' first second := by
    simp only [map_add]
    exact finsum_add_distrib (cutSummand_finite D hu h a exponent cut first)
      (cutSummand_finite D hu h a exponent cut second)
  map_smul' scalar vector := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' scalar (cutSummand_finite D hu h a exponent cut vector)).symm

private theorem currentCombination_ward (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent mode : ℤ) (vector : ActualTensor D hu) :
    currentCombination D hu h mode (chargedCoefficient D hu a (exponent + 2 * mode + 3) vector) -
      chargedCoefficient D hu a (exponent + 2 * mode + 3)
        (currentCombination D hu h mode vector) =
      chargePairing D h a • chargedCoefficient D hu a (exponent + 2) vector := by
  simp only [currentCombination, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    chargePairing, Finset.sum_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro colour member
  rw [← smul_sub]
  have ward := congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector)
    (charged_tensor_current_ward D hu colour a mode (exponent + 2 * mode + 3))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at ward
  rw [show exponent + 2 * mode + 3 - (2 * mode + 1) = exponent + 2 by omega] at ward
  rw [ward, smul_smul]

theorem cutProduct_step (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    cutProduct D hu h a exponent (cut + 1) vector - cutProduct D hu h a exponent cut vector =
      chargePairing D h a • chargedCoefficient D hu a (exponent + 2) vector := by
  change (∑ᶠ mode : ℤ, cutSummand D hu h a exponent (cut + 1) mode vector) -
    (∑ᶠ mode : ℤ, cutSummand D hu h a exponent cut mode vector) = _
  rw [← finsum_sub_distrib (cutSummand_finite D hu h a exponent (cut + 1) vector)
    (cutSummand_finite D hu h a exponent cut vector)]
  rw [finsum_eq_single _ cut (by
    intro mode different
    have equivalent : mode < cut + 1 ↔ mode < cut := by omega
    simp only [cutSummand, equivalent, sub_self])]
  simp only [cutSummand, show cut < cut + 1 by omega, lt_self_iff_false, if_true, if_false,
    Module.End.mul_apply]
  exact currentCombination_ward D hu h a exponent cut vector

theorem cutProduct_telescope (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    cutProduct D hu h a exponent cut vector = cutProduct D hu h a exponent 0 vector +
      ((cut : ℂ) * chargePairing D h a) • chargedCoefficient D hu a (exponent + 2) vector := by
  induction cut using Int.induction_on with
  | zero => simp
  | succ cut inductionProof =>
    have step := cutProduct_step D hu h a exponent cut vector
    rw [sub_eq_iff_eq_add, inductionProof] at step
    rw [step]
    push_cast
    module
  | pred cut inductionProof =>
    have step := cutProduct_step D hu h a exponent (-(cut : ℤ) - 1) vector
    rw [show -(cut : ℤ) - 1 + 1 = -(cut : ℤ) by omega, inductionProof] at step
    rw [sub_eq_iff_eq_add] at step
    have rearranged := eq_sub_of_add_eq' step.symm
    rw [rearranged]
    push_cast
    module

def leftTerm (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) (offset : ℕ) :=
  currentCombination D hu h (cut - 1 - offset)
    (chargedCoefficient D hu a (exponent + 2 * cut + 1 - 2 * offset) vector)

def rightTerm (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) (offset : ℕ) :=
  chargedCoefficient D hu a (exponent + 2 * cut + 3 + 2 * offset)
    (currentCombination D hu h (cut + offset) vector)

theorem leftTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (leftTerm D hu h a exponent cut vector) := by
  have finite := Function.HasFiniteSupport.comp_of_injective
    (show Function.Injective (fun offset : ℕ => cut - 1 - (offset : ℤ)) from by
      intro first second equal; dsimp only at equal; omega)
    (cutSummand_finite D hu h a exponent cut vector)
  convert finite using 1
  funext offset
  simp only [Function.comp_apply, cutSummand,
    show cut - 1 - (offset : ℤ) < cut by omega, if_true, Module.End.mul_apply, leftTerm]
  rw [show exponent + 2 * (cut - 1 - (offset : ℤ)) + 3 =
    exponent + 2 * cut + 1 - 2 * offset by omega]

theorem rightTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (rightTerm D hu h a exponent cut vector) := by
  have finite := Function.HasFiniteSupport.comp_of_injective
    (show Function.Injective (fun offset : ℕ => cut + (offset : ℤ)) from by
      intro first second equal; dsimp only at equal; omega)
    (cutSummand_finite D hu h a exponent cut vector)
  convert finite using 1
  funext offset
  simp only [Function.comp_apply, cutSummand,
    show ¬cut + (offset : ℤ) < cut by omega, if_false, Module.End.mul_apply, rightTerm]
  rw [show exponent + 2 * (cut + (offset : ℤ)) + 3 =
    exponent + 2 * cut + 3 + 2 * offset by omega]

theorem cutProduct_nat_reindex (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    cutProduct D hu h a exponent cut vector =
      (∑ᶠ offset : ℕ, leftTerm D hu h a exponent cut vector offset) +
        ∑ᶠ offset : ℕ, rightTerm D hu h a exponent cut vector offset := by
  classical
  let before := fun mode : ℤ => if mode < cut then
    cutSummand D hu h a exponent cut mode vector else 0
  let after := fun mode : ℤ => if cut ≤ mode then
    cutSummand D hu h a exponent cut mode vector else 0
  have beforeFinite : Function.HasFiniteSupport before := by
    apply (cutSummand_finite D hu h a exponent cut vector).subset
    intro mode member
    change before mode ≠ 0 at member
    by_cases negative : mode < cut
    · simpa [before, negative] using member
    · simp [before, negative] at member
  have afterFinite : Function.HasFiniteSupport after := by
    apply (cutSummand_finite D hu h a exponent cut vector).subset
    intro mode member
    change after mode ≠ 0 at member
    by_cases positive : cut ≤ mode
    · simpa [after, positive] using member
    · simp [after, positive] at member
  have split : (fun mode => cutSummand D hu h a exponent cut mode vector) =
      fun mode => before mode + after mode := by
    funext mode
    by_cases negative : mode < cut
    · simp [before, after, negative, show ¬cut ≤ mode by omega]
    · simp [before, after, negative, show cut ≤ mode by omega]
  have leftRange : Set.range (fun offset : ℕ => cut - 1 - (offset : ℤ)) = Set.Iio cut := by
    ext mode
    constructor
    · rintro ⟨offset, rfl⟩
      simp only [Set.mem_Iio]
      omega
    · intro member
      refine ⟨(cut - 1 - mode).toNat, ?_⟩
      dsimp only
      have cast := Int.toNat_of_nonneg (show 0 ≤ cut - 1 - mode by
        simp only [Set.mem_Iio] at member; omega)
      omega
  have rightRange : Set.range (fun offset : ℕ => cut + (offset : ℤ)) = Set.Ici cut := by
    ext mode
    constructor
    · rintro ⟨offset, rfl⟩
      simp only [Set.mem_Ici]
      omega
    · intro member
      refine ⟨(mode - cut).toNat, ?_⟩
      dsimp only
      have cast := Int.toNat_of_nonneg (show 0 ≤ mode - cut by
        simp only [Set.mem_Ici] at member; omega)
      omega
  have left : (∑ᶠ mode : ℤ, before mode) =
      ∑ᶠ offset : ℕ, leftTerm D hu h a exponent cut vector offset := by
    calc
      _ = ∑ᶠ mode ∈ Set.Iio cut, cutSummand D hu h a exponent cut mode vector := by
        apply finsum_congr
        intro mode
        simp only [finsum_eq_if, Set.mem_Iio]
        rfl
      _ = ∑ᶠ offset : ℕ, cutSummand D hu h a exponent cut (cut - 1 - offset) vector := by
        rw [← leftRange]
        apply finsum_mem_range
        intro first second equal
        dsimp only at equal
        omega
      _ = _ := by
        apply finsum_congr
        intro offset
        simp only [cutSummand, show cut - 1 - (offset : ℤ) < cut by omega,
          if_true, Module.End.mul_apply, leftTerm]
        rw [show exponent + 2 * (cut - 1 - (offset : ℤ)) + 3 =
          exponent + 2 * cut + 1 - 2 * offset by omega]
  have right : (∑ᶠ mode : ℤ, after mode) =
      ∑ᶠ offset : ℕ, rightTerm D hu h a exponent cut vector offset := by
    calc
      _ = ∑ᶠ mode ∈ Set.Ici cut, cutSummand D hu h a exponent cut mode vector := by
        apply finsum_congr
        intro mode
        simp only [finsum_eq_if, Set.mem_Ici]
        rfl
      _ = ∑ᶠ offset : ℕ, cutSummand D hu h a exponent cut (cut + offset) vector := by
        rw [← rightRange]
        apply finsum_mem_range
        intro first second equal
        dsimp only at equal
        omega
      _ = _ := by
        apply finsum_congr
        intro offset
        simp only [cutSummand, show ¬cut + (offset : ℤ) < cut by omega,
          if_false, Module.End.mul_apply, rightTerm]
        rw [show exponent + 2 * (cut + (offset : ℤ)) + 3 =
          exponent + 2 * cut + 3 + 2 * offset by omega]
  change (∑ᶠ mode : ℤ, cutSummand D hu h a exponent cut mode vector) = _
  rw [split, finsum_add_distrib beforeFinite afterFinite, left, right]

theorem cutProduct_zero_normal (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    cutProduct D hu h a exponent 0 vector = ∑ colour, h colour •
      (normalInsertion D hu (colour, 0) (chargedField D hu a)).coeff exponent vector := by
  have negativeIdentity : leftTerm D hu h a exponent 0 vector = fun offset =>
      ∑ colour, h colour • negativeTerm D hu (colour, 0) (chargedField D hu a)
        exponent vector offset := by
    funext offset
    simp only [leftTerm, currentCombination, LinearMap.sum_apply, LinearMap.smul_apply,
      negativeTerm, jetScalar, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one, div_one, one_smul, chargedField, HVertexOperator.coeff_of_coeff,
      Nat.cast_zero, mul_zero, add_zero]
    rw [show (0 : ℤ) - 1 - offset = -(offset : ℤ) - 1 by omega,
      show exponent + 1 - 2 * offset = exponent - 2 * offset + 1 by omega]
  have positiveIdentity : rightTerm D hu h a exponent 0 vector = fun offset =>
      ∑ colour, h colour • positiveTerm D hu (colour, 0) (chargedField D hu a)
        exponent vector offset := by
    funext offset
    simp only [rightTerm, currentCombination, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, positiveTerm, jetScalar, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, div_one, one_smul, chargedField,
      HVertexOperator.coeff_of_coeff, Nat.cast_zero, mul_zero, add_zero, zero_add]
    rw [show exponent + 3 + 2 * offset = exponent + 2 * offset + 3 by omega]
  rw [cutProduct_nat_reindex, negativeIdentity, positiveIdentity,
    finsum_sum_comm Finset.univ (fun offset colour => h colour •
      negativeTerm D hu (colour, 0) (chargedField D hu a) exponent vector offset)
      (fun colour _ => (negativeTerm_finite D hu (colour, 0) (chargedField D hu a)
        exponent vector).fun_comp (smul_zero (h colour))),
    finsum_sum_comm Finset.univ (fun offset colour => h colour •
      positiveTerm D hu (colour, 0) (chargedField D hu a) exponent vector offset)
      (fun colour _ => (positiveTerm_finite D hu (colour, 0) (chargedField D hu a)
        exponent vector).fun_comp (smul_zero (h colour))),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro colour member
  rw [← smul_finsum' (h colour)
      (negativeTerm_finite D hu (colour, 0) (chargedField D hu a) exponent vector),
    ← smul_finsum' (h colour)
      (positiveTerm_finite D hu (colour, 0) (chargedField D hu a) exponent vector),
    ← smul_add]
  rfl

theorem native_first_descendant_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (originalFirstDescendant D h a)).coeff exponent vector =
      cutProduct D hu h a exponent 0 vector -
        (chargePairing D h a / 2) • chargedCoefficient D hu a (exponent + 2) vector := by
  rw [originalFirstDescendant_coefficient, cutProduct_zero_normal]

theorem native_first_descendant_mixed_iterate (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (originalFirstDescendant D h a)).coeff exponent vector +
      (((cut : ℂ) + 1 / 2) * chargePairing D h a) •
        chargedCoefficient D hu a (exponent + 2) vector =
      (∑ᶠ offset : ℕ, leftTerm D hu h a exponent cut vector offset) +
        ∑ᶠ offset : ℕ, rightTerm D hu h a exponent cut vector offset := by
  rw [← cutProduct_nat_reindex, native_first_descendant_coefficient,
    cutProduct_telescope D hu h a exponent cut vector]
  module

end
end D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts.cutProduct_telescope
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts.native_first_descendant_mixed_iterate

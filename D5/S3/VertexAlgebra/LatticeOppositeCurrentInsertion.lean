/- GID: D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeOppositeCurrentInsertion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual pointwise current reflection and its zero-mode insertion correction. -/

import D5.S3.VertexAlgebra.LatticeOppositeCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOppositeCurrentInsertion

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraLocalNilpotence LatticeOppositeCoefficients
open scoped BigOperators VertexOperator

noncomputable section

attribute [local irreducible] sugawaraMode neutralMode Y

theorem finsum_zero_succ {Space : Type*} [AddCommGroup Space]
    (term : ℕ → Space) (finite : Function.HasFiniteSupport term) :
    (∑ᶠ offset : ℕ, term offset) = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some offset => offset + 1
    invFun value := match value with | 0 => none | offset + 1 => some offset
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  rw [← finsum_comp_equiv zeroSucc, finsum_option]
  · rfl
  · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1)
      (fun first second equality => Nat.add_right_cancel equality)

private theorem rising_mode_current_finite (D : LatticeData)
    (current : Fin D.rank) (state tested : Carrier D) (index : ℤ) :
    Function.HasFiniteSupport (fun offset : ℕ =>
      neutralMode D current (-(offset : ℤ)) (((Y D state)[[index + offset]]) tested)) := by
  classical
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (Y D state tested)).order - index - 1).toNat, ?_⟩
  intro offset present
  contrapose! present
  have vanished : ((Y D state)[[index + offset]]) tested = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [Function.mem_support, vanished]

theorem current_one_reflection (D : LatticeData)
    (current : Fin D.rank) (state tested : Carrier D) (index : ℤ) :
    ((Y D (neutralMode D current (-1) state))[[index]]) tested +
        ((Y D (neutralMode D current 0 state))[[index - 1]]) tested =
      (∑ᶠ offset : ℕ, neutralMode D current (-(offset : ℤ))
        (((Y D state)[[index + offset - 1]]) tested)) +
      ∑ᶠ offset : ℕ, ((Y D state)[[index - offset - 2]])
        (neutralMode D current (offset + 1) tested) := by
  have native := current_negative_insertion D current 0 state tested index
  dsimp only at native
  simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_smul,
    pow_zero, Nat.cast_zero, sub_zero, neg_zero, zero_add, zero_sub] at native
  have negativeFinite := rising_mode_current_finite D current state tested (index - 1)
  have negativeSplit := finsum_zero_succ _ negativeFinite
  have negativeTail : (∑ᶠ offset : ℕ, neutralMode D current (-((offset + 1 : ℕ) : ℤ))
      (((Y D state)[[(index - 1) + (offset + 1 : ℕ)]]) tested)) =
      ∑ᶠ offset : ℕ, neutralMode D current (-(offset : ℤ) - 1)
        (((Y D state)[[index + offset]]) tested) := by
    apply finsum_congr
    intro offset
    rw [show -((offset + 1 : ℕ) : ℤ) = -(offset : ℤ) - 1 by omega,
      show (index - 1) + (offset + 1 : ℕ) = index + offset by omega]
  have positiveSplit := finsum_zero_succ _ native.2.1
  have positiveTail : (∑ᶠ offset : ℕ, ((Y D state)[[index - (offset + 1 : ℕ) - 1]])
      (neutralMode D current (offset + 1 : ℕ) tested)) =
      ∑ᶠ offset : ℕ, ((Y D state)[[index - offset - 2]])
        (neutralMode D current (offset + 1) tested) := by
    apply finsum_congr
    intro offset
    rw [show index - (offset + 1 : ℕ) - 1 = index - offset - 2 by omega,
      Nat.cast_add, Nat.cast_one]
  have negativeIndex : (fun offset : ℕ => neutralMode D current (-(offset : ℤ))
      (((Y D state)[[(index - 1) + offset]]) tested)) =
      (fun offset : ℕ => neutralMode D current (-(offset : ℤ))
        (((Y D state)[[index + offset - 1]]) tested)) := by
    funext offset
    rw [show (index - 1) + offset = index + offset - 1 by omega]
  rw [negativeTail, negativeIndex] at negativeSplit
  simp only [Nat.cast_zero, neg_zero, zero_add, add_zero, sub_zero] at negativeSplit positiveSplit
  rw [positiveTail] at positiveSplit
  have correction := congrArg (fun operator : Module.End ℂ (Carrier D) => operator tested)
    (zero_current_correction D current state (index - 1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at correction
  rw [native.2.2, positiveSplit, negativeSplit]
  rw [← correction]
  abel

private theorem one_pow_single_current (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (state : Carrier D) (power : ℕ) :
    ((sugawaraMode D H 1)^power) (neutralMode D current (-1) state) =
      neutralMode D current (-1) (((sugawaraMode D H 1)^power) state) +
        (power : ℂ) • neutralMode D current 0
          (((sugawaraMode D H 1)^(power - 1)) state) := by
  cases power with
  | zero => simp
  | succ power =>
    have expansion := one_pow_current_insertion_bounded D H hHG hGH current 1 (power + 1) state
    simpa [min_eq_right (show 1 ≤ power + 1 by omega), Finset.sum_range_succ] using expansion

private theorem one_divided_mode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (state : Carrier D) (power : ℕ) (index : ℤ) :
    (((power + 1).factorial : ℂ)⁻¹) •
        ((Y D (((sugawaraMode D H 1)^(power + 1)) (neutralMode D current (-1) state)))[[index]]) =
      (((power + 1).factorial : ℂ)⁻¹) •
        ((Y D (neutralMode D current (-1) (((sugawaraMode D H 1)^(power + 1)) state)))[[index]]) +
      ((power.factorial : ℂ)⁻¹) •
        ((Y D (neutralMode D current 0 (((sugawaraMode D H 1)^power) state)))[[index]]) := by
  rw [one_pow_single_current D H hHG hGH]
  simp only [Nat.add_sub_cancel, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_add, smul_smul]
  congr 1
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have positive : ((power + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero power
  field_simp

theorem sum_successor_pair {Space : Type*} [AddCommGroup Space]
    (term first second : ℕ → Space) (initial : term 0 = first 0)
    (successor : ∀ power, term (power + 1) = first (power + 1) + second power) (cutoff : ℕ) :
    (∑ power ∈ Finset.range (cutoff + 1), term power) =
      (∑ power ∈ Finset.range (cutoff + 1), first power) +
        ∑ power ∈ Finset.range cutoff, second power := by
  induction cutoff with
  | zero => simpa using initial
  | succ cutoff inductionHypothesis =>
    rw [Finset.sum_range_succ term (cutoff + 1),
      Finset.sum_range_succ first (cutoff + 1),
      Finset.sum_range_succ second cutoff, inductionHypothesis, successor]
    abel

private theorem opposite_one_normal_sum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (state : Carrier D) (weight index : ℤ) (cutoff : ℕ)
    (stateCovered : oscillatorBound D state < cutoff)
    (insertionCovered : oscillatorBound D (neutralMode D current (-1) state) < cutoff + 1) :
    oppositeCoeff D H (weight + 1) (neutralMode D current (-1) state) index =
      paritySign (weight + 1) • ∑ power ∈ Finset.range (cutoff + 1),
        ((power.factorial : ℂ)⁻¹) •
          (((Y D (neutralMode D current (-1) (((sugawaraMode D H 1)^power) state)))
              [[2 * weight - index - power]]) +
            ((Y D (neutralMode D current 0 (((sugawaraMode D H 1)^power) state)))
              [[2 * weight - index - power - 1]])) := by
  classical
  let first : ℕ → Module.End ℂ (Carrier D) := fun power => ((power.factorial : ℂ)⁻¹) •
    ((Y D (neutralMode D current (-1) (((sugawaraMode D H 1)^power) state)))
      [[2 * weight - index - power]])
  let second : ℕ → Module.End ℂ (Carrier D) := fun power => ((power.factorial : ℂ)⁻¹) •
    ((Y D (neutralMode D current 0 (((sugawaraMode D H 1)^power) state)))
      [[2 * weight - index - power - 1]])
  have initial : oppositeTerm D H (weight + 1) (neutralMode D current (-1) state) index 0 = first 0 := by
    simp only [oppositeTerm, first]
    congr 2 <;> norm_num <;> ring
  have successor (power : ℕ) :
      oppositeTerm D H (weight + 1) (neutralMode D current (-1) state) index (power + 1) =
        first (power + 1) + second power := by
    unfold oppositeTerm first second
    rw [show 2 * (weight + 1) - index - (power + 1 : ℕ) - 2 =
      2 * weight - index - (power + 1 : ℕ) by omega]
    rw [one_divided_mode D H hHG hGH]
    rw [show 2 * weight - index - (power + 1 : ℕ) =
      2 * weight - index - power - 1 by omega]
  have finalZero : second cutoff = 0 := by
    simp [second, one_pow_eq_zero D H state cutoff stateCovered]
  rw [opposite_cutoff D H (weight + 1) _ index (cutoff + 1) insertionCovered,
    sum_successor_pair _ first second initial successor,
    show (∑ power ∈ Finset.range cutoff, second power) =
      ∑ power ∈ Finset.range (cutoff + 1), second power by
        rw [Finset.sum_range_succ, finalZero, add_zero], ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro power present
  exact (smul_add _ _ _).symm

private theorem falling_mode_current_finite (D : LatticeData)
    (current : Fin D.rank) (state tested : Carrier D) (index : ℤ) :
    Function.HasFiniteSupport (fun offset : ℕ =>
      ((Y D state)[[index - offset - 2]]) (neutralMode D current (offset + 1) tested)) := by
  classical
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (neutralField D current tested)).order - 1).toNat, ?_⟩
  intro offset present
  contrapose! present
  have vanished : neutralMode D current (offset + 1) tested = 0 := by
    rw [← neutralField_ncoeff]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [Function.mem_support, vanished]

set_option maxHeartbeats 8000000 in
theorem opposite_current_one_insertion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (state tested : Carrier D) (weight index : ℤ) :
    oppositeCoeff D H (weight + 1) (neutralMode D current (-1) state) index tested =
      -(∑ᶠ offset : ℕ, reversedFirstTerm D H current 0 weight state index tested offset) -
        ∑ᶠ offset : ℕ, reversedSecondTerm D H current 0 weight state index tested offset := by
  classical
  let cutoff := max (oscillatorBound D state)
    (oscillatorBound D (neutralMode D current (-1) state)) + 1
  have stateCovered : oscillatorBound D state < cutoff := by dsimp [cutoff]; omega
  have insertionCovered : oscillatorBound D (neutralMode D current (-1) state) < cutoff + 1 := by
    dsimp [cutoff]
    omega
  let negative : ℕ → ℕ → Carrier D := fun power offset =>
    neutralMode D current (-(offset : ℤ))
      (((Y D (((sugawaraMode D H 1)^power) state))[[2 * weight - index - power + offset - 1]]) tested)
  let positive : ℕ → ℕ → Carrier D := fun power offset =>
    ((Y D (((sugawaraMode D H 1)^power) state))[[2 * weight - index - power - offset - 2]])
      (neutralMode D current (offset + 1) tested)
  have negativeFinite (power : ℕ) : Function.HasFiniteSupport (negative power) := by
    have finite := rising_mode_current_finite D current (((sugawaraMode D H 1)^power) state)
      tested (2 * weight - index - power - 1)
    have indices (offset : ℕ) : 2 * weight - index - power - 1 + offset =
        2 * weight - index - power + offset - 1 := by omega
    simpa only [negative, indices] using finite
  have positiveFinite (power : ℕ) : Function.HasFiniteSupport (positive power) :=
    falling_mode_current_finite D current (((sugawaraMode D H 1)^power) state) tested
      (2 * weight - index - power)
  have normal : oppositeCoeff D H (weight + 1) (neutralMode D current (-1) state) index tested =
      paritySign (weight + 1) •
          (∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • ∑ᶠ offset : ℕ, negative power offset) +
        paritySign (weight + 1) •
          (∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • ∑ᶠ offset : ℕ, positive power offset) := by
    rw [opposite_one_normal_sum D H hHG hGH current state weight index cutoff
      stateCovered insertionCovered]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply]
    simp_rw [current_one_reflection]
    simp only [smul_add, Finset.sum_add_distrib, negative, positive]
  have negativeSwap :
      (∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • ∑ᶠ offset : ℕ, negative power offset) =
      ∑ᶠ offset : ℕ, ∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • negative power offset := by
    simp_rw [smul_finsum]
    apply sum_finsum_comm
    intro power present
    exact (negativeFinite power).fun_comp (smul_zero _)
  have positiveSwap :
      (∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • ∑ᶠ offset : ℕ, positive power offset) =
      ∑ᶠ offset : ℕ, ∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • positive power offset := by
    simp_rw [smul_finsum]
    apply sum_finsum_comm
    intro power present
    exact (positiveFinite power).fun_comp (smul_zero _)
  have sign : paritySign (weight + 1) = -paritySign weight := by
    rw [LatticeActualGeneratorLocality.paritySign_add]
    norm_num [paritySign]
  have negativePoint (offset : ℕ) : paritySign (weight + 1) •
      (∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • negative power offset) =
        -reversedSecondTerm D H current 0 weight state index tested offset := by
    unfold reversedSecondTerm
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.cast_zero, sub_zero]
    rw [opposite_cutoff_apply D H weight state (index - offset - 1) tested
      (cutoff + 1) (by omega), map_smul, map_sum]
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.cast_zero, sub_zero, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, sign, neg_smul, negative]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro power present
    rw [show 2 * weight - (index - offset - 1) - power - 2 =
      2 * weight - index - power + offset - 1 by omega]
  have positivePoint (offset : ℕ) : paritySign (weight + 1) •
      (∑ power ∈ Finset.range (cutoff + 1), (power.factorial : ℂ)⁻¹ • positive power offset) =
        -reversedFirstTerm D H current 0 weight state index tested offset := by
    unfold reversedFirstTerm
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.cast_zero, add_zero]
    rw [opposite_cutoff_apply D H weight state (index + offset)
      (neutralMode D current (offset + 1) tested) (cutoff + 1) (by omega)]
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.cast_zero, add_zero, LinearMap.smul_apply, LinearMap.sum_apply,
      sign, neg_smul, positive]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro power present
    rw [show 2 * weight - (index + offset) - power - 2 =
      2 * weight - index - power - offset - 2 by omega]
  rw [normal, negativeSwap, positiveSwap, smul_finsum, smul_finsum]
  simp_rw [negativePoint, positivePoint]
  rw [finsum_neg_distrib, finsum_neg_distrib]
  abel

end
end D5.S3.VertexAlgebra.LatticeOppositeCurrentInsertion

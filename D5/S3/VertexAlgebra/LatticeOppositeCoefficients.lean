/- GID: D5/S3/VertexAlgebra/LatticeOppositeCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeOppositeCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite actual opposite coefficients with integer weights and native current reconstruction. -/

import D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Lie.OfAssociative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOppositeCoefficients

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open LatticeSugawaraLocalNilpotence LatticeActualStateFieldCalculus
open LatticeFiniteNegativeGeneration
open scoped BigOperators VertexOperator

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

def oppositeTerm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) (power : ℕ) :
    Module.End ℂ (Carrier D) :=
  ((power.factorial : ℂ)⁻¹) •
    ((Y D (((sugawaraMode D H 1)^power) state))[[2 * weight - index - power - 2]])

def oppositeCoeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) : Module.End ℂ (Carrier D) :=
  paritySign weight •
    ∑ power ∈ Finset.range (oscillatorBound D state + 1),
      oppositeTerm D H weight state index power

private theorem oppositeTerm_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) (power : ℕ)
    (beyond : oscillatorBound D state < power) :
    oppositeTerm D H weight state index power = 0 := by
  simp [oppositeTerm, one_pow_eq_zero D H state power beyond]

theorem opposite_cutoff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) (cutoff : ℕ)
    (covers : oscillatorBound D state < cutoff) :
    oppositeCoeff D H weight state index = paritySign weight •
      ∑ power ∈ Finset.range cutoff, oppositeTerm D H weight state index power := by
  classical
  unfold oppositeCoeff
  congr 1
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro power present outside
  apply oppositeTerm_zero
  simp only [Finset.mem_range] at outside
  omega

theorem opposite_terms_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) :
    Function.HasFiniteSupport (oppositeTerm D H weight state index) := by
  classical
  apply (Finset.range (oscillatorBound D state + 1)).finite_toSet.subset
  intro power present
  by_contra outside
  apply present
  apply oppositeTerm_zero
  simp only [Finset.mem_coe, Finset.mem_range] at outside
  omega

theorem opposite_cutoff_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) (tested : Carrier D) (cutoff : ℕ)
    (covers : oscillatorBound D state < cutoff) :
    oppositeCoeff D H weight state index tested = paritySign weight •
      ∑ power ∈ Finset.range cutoff, ((power.factorial : ℂ)⁻¹) •
        ((Y D (((sugawaraMode D H 1)^power) state))[[2 * weight - index - power - 2]]) tested := by
  rw [opposite_cutoff D H weight state index cutoff covers]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, oppositeTerm]

theorem opposite_finsum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (weight : ℤ) (state : Carrier D) (index : ℤ) :
    oppositeCoeff D H weight state index =
      paritySign weight • ∑ᶠ power : ℕ, oppositeTerm D H weight state index power := by
  unfold oppositeCoeff
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro power present
  by_contra outside
  apply present
  apply oppositeTerm_zero
  simp only [Finset.mem_coe, Finset.mem_range] at outside
  omega

private theorem zero_current_state_commutator (D : LatticeData)
    (current : Fin D.rank) (state : Carrier D) (index : ℤ) :
    neutralMode D current 0 * ((Y D state)[[index]]) -
      ((Y D state)[[index]]) * neutralMode D current 0 =
        ((Y D (neutralMode D current 0 state))[[index]]) := by
  let generator := ((neutralField D current)[[-1]]) (vacuum D)
  have generatorField : Y D generator = neutralField D current := stateField_current D current
  have actual := mode_commutator D generator state 0 index
  rw [stateField_current, neutralField_ncoeff] at actual
  rw [actual, finsum_eq_single _ 0]
  · simp only [commutatorTerm, StateFieldResidueReconstruction.integerBinomial,
      LatticeAllStateReconstruction.mu, generatorField, neutralField_ncoeff]
    simp
  · intro power nonzero
    simp [commutatorTerm, StateFieldResidueReconstruction.integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero nonzero)]

theorem zero_current_correction (D : LatticeData)
    (current : Fin D.rank) (state : Carrier D) (index : ℤ) :
    ((Y D state)[[index]]) * neutralMode D current 0 +
      ((Y D (neutralMode D current 0 state))[[index]]) =
        neutralMode D current 0 * ((Y D state)[[index]]) := by
  rw [← zero_current_state_commutator]
  abel

private theorem negative_binomial (degree offset : ℕ) :
    (-1 : ℂ)^offset * ((Ring.choose (-(degree : ℤ) - 1) offset : ℤ) : ℂ) =
      ((degree + offset).choose degree : ℂ) := by
  rw [show -(degree : ℤ) - 1 = -((degree : ℤ) + 1) by omega,
    Ring.choose_neg,
    show (degree : ℤ) + 1 + offset - 1 = ((degree + offset : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
    Int.cast_negOnePow_natCast, Int.cast_natCast]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num
  exact_mod_cast (Nat.choose_symm_add (a := degree) (b := offset)).symm

set_option maxHeartbeats 2000000 in
theorem current_negative_insertion (D : LatticeData)
    (current : Fin D.rank) (degree : ℕ) (state tested : Carrier D) (index : ℤ) :
    let first : ℕ → Carrier D := fun offset =>
      ((degree + offset).choose degree : ℂ) •
        neutralMode D current (-(offset : ℤ) - degree - 1)
          (((Y D state)[[index + offset]]) tested)
    let second : ℕ → Carrier D := fun offset =>
      ((degree + offset).choose degree : ℂ) •
        ((Y D state)[[index - offset - degree - 1]])
          (neutralMode D current offset tested)
    Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      ((Y D (neutralMode D current (-(degree : ℤ) - 1) state))[[index]]) tested =
        (∑ᶠ offset : ℕ, first offset) + (-1 : ℂ)^degree • ∑ᶠ offset : ℕ, second offset := by
  let generator := ((neutralField D current)[[-1]]) (vacuum D)
  have actual := StateFieldResidueReconstruction.stateField_iterate_of_creation_translation_locality
    (Y D) (vacuum D) (translation D) (translation_kills_vacuum D)
    (stateField_creation D) (stateField_creativity D) (stateField_covariance D)
    (LatticeAllStateLocality.stateField_locality D)
    generator state tested (-(degree : ℤ) - 1) index
  rw [stateField_current] at actual
  simp only [neutralField_ncoeff, negative_binomial] at actual
  have sign : -((-1 : ℂ)^(-(degree : ℤ) - 1)) = (-1 : ℂ)^degree := by
    rw [show -(degree : ℤ) - 1 = -((degree + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow]
    norm_num [pow_succ]
  have firstIndex (offset : ℕ) :
      -(degree : ℤ) - 1 - offset = -(offset : ℤ) - degree - 1 := by omega
  have secondIndex (offset : ℕ) :
      -(degree : ℤ) - 1 + index - offset = index - offset - degree - 1 := by omega
  simp only [firstIndex, secondIndex] at actual
  refine ⟨actual.1, actual.2.1, ?_⟩
  rw [actual.2.2, sub_eq_add_neg, ← neg_smul, sign]

private theorem current_ad_pow (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (frequency power : ℕ) :
    ((LieAlgebra.ad ℂ (Module.End ℂ (Carrier D)) (sugawaraMode D H 1))^power)
        (neutralMode D current (-(frequency : ℤ))) =
      (frequency.descFactorial power : ℂ) •
        neutralMode D current ((power : ℤ) - frequency) := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
    rw [pow_succ', Module.End.mul_apply, inductionHypothesis, map_smul]
    change (frequency.descFactorial power : ℂ) •
        (sugawaraMode D H 1 * neutralMode D current ((power : ℤ) - frequency) -
          neutralMode D current ((power : ℤ) - frequency) * sugawaraMode D H 1) = _
    rw [sugawaraMode_current_commutator D H hHG hGH, smul_smul]
    have indices : 1 + ((power : ℤ) - frequency) = (power + 1 : ℕ) - frequency := by omega
    rw [indices]
    congr 1
    rw [Nat.descFactorial_succ, Nat.cast_mul]
    by_cases below : power ≤ frequency
    · rw [Nat.cast_sub below]
      push_cast
      ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp

theorem one_pow_current_insertion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (frequency power : ℕ) (state : Carrier D) :
    ((sugawaraMode D H 1)^power) (neutralMode D current (-(frequency : ℤ)) state) =
      ∑ split ∈ Finset.HasAntidiagonal.antidiagonal power,
        ((power.choose split.1 : ℂ) * (frequency.descFactorial split.1 : ℂ)) •
          neutralMode D current ((split.1 : ℤ) - frequency)
            (((sugawaraMode D H 1)^split.2) state) := by
  have expansion := LieModule.toEnd_pow_lie
    (R := ℂ) (L := Module.End ℂ (Carrier D)) (M := Carrier D)
    (sugawaraMode D H 1) (neutralMode D current (-(frequency : ℤ))) state power
  simp only [LieModule.toEnd_module_end, LieHom.id_apply,
    current_ad_pow D H hHG hGH, Module.End.lie_apply, LinearMap.smul_apply,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul] at expansion
  exact expansion

theorem one_pow_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ) (state : Carrier D) (homogeneous : state ∈ grade D weight) (power : ℕ) :
    ((sugawaraMode D H 1)^power) state ∈ grade D (weight - power) := by
  induction power with
  | zero => simpa using homogeneous
  | succ power inductionHypothesis =>
    apply (actualL0_eigen_iff_grade D H hHG hGH _ _).mp
    have eigen := (actualL0_eigen_iff_grade D H hHG hGH _ _).mpr inductionHypothesis
    have commutator := congrArg (fun operator : Module.End ℂ (Carrier D) =>
        operator (((sugawaraMode D H 1)^power) state))
      (sugawaraMode_virasoro D H hHG hGH 0 1)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, eigen, map_smul] at commutator
    norm_num at commutator
    rw [sub_eq_iff_eq_add] at commutator
    rw [pow_succ', Module.End.mul_apply]
    rw [commutator]
    push_cast
    module

def reversedFirstTerm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (current : Fin D.rank) (degree : ℕ) (weight : ℤ)
    (state : Carrier D) (index : ℤ) (tested : Carrier D) (offset : ℕ) : Carrier D :=
  ((degree + offset).choose degree : ℂ) •
    oppositeCoeff D H weight state (index + offset)
      (neutralMode D current (offset + degree + 1) tested)

def reversedSecondTerm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (current : Fin D.rank) (degree : ℕ) (weight : ℤ)
    (state : Carrier D) (index : ℤ) (tested : Carrier D) (offset : ℕ) : Carrier D :=
  ((degree + offset).choose degree : ℂ) •
    neutralMode D current (-(offset : ℤ))
      (oppositeCoeff D H weight state (index - offset - degree - 1) tested)

theorem reversed_first_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (current : Fin D.rank) (degree : ℕ) (weight : ℤ)
    (state : Carrier D) (index : ℤ) (tested : Carrier D) :
    Function.HasFiniteSupport (reversedFirstTerm D H current degree weight state index tested) := by
  classical
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (neutralField D current tested)).order - 1).toNat, ?_⟩
  intro offset present
  contrapose! present
  have vanished : neutralMode D current (offset + degree + 1) tested = 0 := by
    rw [← neutralField_ncoeff]
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [Function.mem_support, reversedFirstTerm, vanished]

def oppositeInputBound (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (degree : ℕ) (weight : ℤ) (state : Carrier D) (index : ℤ) (tested : Carrier D) : ℕ :=
  (Finset.range (oscillatorBound D state + 1)).sup fun power =>
    (-((HahnModule.of ℂ).symm (Y D (((sugawaraMode D H 1)^power) state) tested)).order -
      2 * weight + index - degree + power).toNat

theorem opposite_reversed_input_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (degree : ℕ) (weight : ℤ) (state : Carrier D) (index : ℤ) (tested : Carrier D)
    (offset : ℕ) (beyond : oppositeInputBound D H degree weight state index tested < offset) :
    oppositeCoeff D H weight state (index - offset - degree - 1) tested = 0 := by
  classical
  unfold oppositeCoeff
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  have vanished : (∑ power ∈ Finset.range (oscillatorBound D state + 1),
      oppositeTerm D H weight state (index - offset - degree - 1) power tested) = 0 := by
    apply Finset.sum_eq_zero
    intro power present
    have below :
        (-((HahnModule.of ℂ).symm (Y D (((sugawaraMode D H 1)^power) state) tested)).order -
          2 * weight + index - degree + power).toNat ≤
            oppositeInputBound D H degree weight state index tested := by
      unfold oppositeInputBound
      exact Finset.le_sup (f := fun descendant : ℕ =>
        (-((HahnModule.of ℂ).symm
          (Y D (((sugawaraMode D H 1)^descendant) state) tested)).order -
          2 * weight + index - degree + descendant).toNat) present
    unfold oppositeTerm
    rw [LinearMap.smul_apply]
    have zeroMode : ((Y D (((sugawaraMode D H 1)^power) state))
        [[2 * weight - (index - offset - degree - 1) - power - 2]]) tested = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    rw [zeroMode, smul_zero]
  rw [vanished, smul_zero]

theorem reversed_second_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (current : Fin D.rank) (degree : ℕ) (weight : ℤ)
    (state : Carrier D) (index : ℤ) (tested : Carrier D) :
    Function.HasFiniteSupport (reversedSecondTerm D H current degree weight state index tested) := by
  classical
  apply (Finset.range (oppositeInputBound D H degree weight state index tested + 1)).finite_toSet.subset
  intro offset present
  by_contra outside
  have beyond : oppositeInputBound D H degree weight state index tested < offset := by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega
  exact present (by simp [reversedSecondTerm,
    opposite_reversed_input_zero D H degree weight state index tested offset beyond])

theorem one_pow_current_insertion_bounded (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (frequency power : ℕ) (state : Carrier D) :
    ((sugawaraMode D H 1)^power) (neutralMode D current (-(frequency : ℤ)) state) =
      ∑ insertion ∈ Finset.range (min power frequency + 1),
        ((power.choose insertion : ℂ) * (frequency.descFactorial insertion : ℂ)) •
          neutralMode D current ((insertion : ℤ) - frequency)
            (((sugawaraMode D H 1)^(power - insertion)) state) := by
  rw [one_pow_current_insertion D H hHG hGH,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro insertion present outside
  have above : frequency < insertion := by
    simp only [Finset.mem_range] at present outside
    omega
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr above]
  simp

end
end D5.S3.VertexAlgebra.LatticeOppositeCoefficients

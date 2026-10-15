import D5.S3.VertexAlgebra.TemporaryBcGhostSuperBorcherdsTerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperJacobi

open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField BcGhostSuperLocality
open BcGhostSuperReconstruction BcGhostSuperResidues BcGhostSuperBorcherdsTerms SuperFieldProducts
open FieldNormalProductLocality (deltaEnd)
open SuperFieldLocality (locality_raise delta_iterate_eq_pow)
open scoped VertexOperator

noncomputable section

def mu (state : Carrier) (mode : ℤ) (vector : Carrier) : Carrier := ((Y state)[[mode]]) vector

def exchangeEpsilon (exchange : ℂ) (parameter : ℤ) : ℂ := epsilon parameter * exchange

def jacobiLeftTerm (first last parameter : ℤ) (left right vector : Carrier) (offset : ℕ) : Carrier :=
  integerBinomial first offset • mu (mu left (parameter + offset) right) (first + last - offset) vector

def jacobiRightFirstTerm (first last parameter : ℤ) (left right vector : Carrier) (offset : ℕ) : Carrier :=
  weight parameter offset • mu left (first + parameter - offset) (mu right (last + offset) vector)

def jacobiRightSecondTerm (exchange : ℂ) (first last parameter : ℤ)
    (left right vector : Carrier) (offset : ℕ) : Carrier :=
  weight parameter offset • (exchangeEpsilon exchange parameter •
    mu right (last + parameter - offset) (mu left (first + offset) vector))

theorem firstTerm_finite (first last parameter : ℤ) (left right vector : Carrier) :
    Function.HasFiniteSupport (jacobiRightFirstTerm first last parameter left right vector) :=
  (forward_finite (Y left) (Y right) (first + parameter) last vector).smul_right (weight parameter)

theorem secondTerm_finite (exchange : ℂ) (first last parameter : ℤ) (left right vector : Carrier) :
    Function.HasFiniteSupport (jacobiRightSecondTerm exchange first last parameter left right vector) :=
  ((forward_finite (Y right) (Y left) (last + parameter) first vector).smul_right
    (fun _ => exchangeEpsilon exchange parameter)).smul_right (weight parameter)

theorem right_split (leftParity rightParity : ℕ) (first last parameter : ℤ)
    (left right vector : Carrier) :
    borcherdsRight leftParity rightParity first parameter last left right vector =
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm first last parameter left right vector offset) -
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm (koszul leftParity rightParity)
          first last parameter left right vector offset) := by
  have termEquality (offset : ℕ) :
      borcherdsRightTerm leftParity rightParity first parameter last left right vector offset =
        jacobiRightFirstTerm first last parameter left right vector offset -
          jacobiRightSecondTerm (koszul leftParity rightParity) first last parameter left right vector offset := by
    dsimp [borcherdsRightTerm, jacobiRightFirstTerm, jacobiRightSecondTerm, mu, exchangeEpsilon]
    rw [add_comm parameter last, smul_sub]
  unfold borcherdsRight
  simp_rw [termEquality]
  exact finsum_sub_distrib (firstTerm_finite first last parameter left right vector)
    (secondTerm_finite (koszul leftParity rightParity) first last parameter left right vector)

theorem positive_right_products (exchange : ℂ) (leftState rightState : Carrier)
    (degree : ℕ) (firstMode lastMode : ℤ) (vector : Carrier) :
    (∑ᶠ offset : ℕ, jacobiRightFirstTerm firstMode lastMode (degree : ℤ) leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange firstMode lastMode (degree : ℤ)
        leftState rightState vector offset) =
      ((deltaEnd ^ degree) (superCommutator exchange (Y leftState) (Y rightState))) firstMode lastMode vector := by
  have chooseNat (offset : ℕ) : integerBinomial degree offset = (degree.choose offset : ℂ) := by simp [integerBinomial, Ring.choose_natCast]
  have firstSum : (∑ᶠ offset : ℕ, jacobiRightFirstTerm firstMode lastMode degree leftState rightState vector offset) = ∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ))
    • (((Y leftState) [[firstMode + degree - offset]])) ((((Y rightState) [[lastMode + offset]])) vector) := by
    unfold jacobiRightFirstTerm mu weight; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
    by_contra outside
    have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    exact member (by simp [zeroChoose])
  have secondSum : (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange firstMode lastMode degree leftState rightState vector offset) = exchangeEpsilon exchange degree • ∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) *
    (degree.choose offset : ℂ)) • (((Y rightState) [[lastMode + degree - offset]])) ((((Y leftState) [[firstMode + offset]])) vector) := by
    unfold jacobiRightSecondTerm mu weight; simp_rw [chooseNat]; rw [Finset.smul_sum]; simp_rw [smul_comm (exchangeEpsilon exchange (degree : ℤ))]
    apply finsum_eq_sum_of_support_subset; intro offset member; by_contra outside
    have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    exact member (by simp [zeroChoose])
  have expansion := delta_binomial
    (superCommutator exchange (Y leftState) (Y rightState)) degree firstMode lastMode
  change (FieldNormalProductLocality.delta^[degree]
    (superCommutator exchange (Y leftState) (Y rightState))) firstMode lastMode = _ at expansion
  rw [delta_iterate_eq_pow] at expansion
  rw [firstSum, secondSum, expansion, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, superCommutator, Module.End.mul_apply, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
  apply congrArg ((∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) • (((Y leftState) [[firstMode + degree - offset]])) ((((Y rightState) [[lastMode + offset]])) vector)) -
    ·)
  rw [Finset.smul_sum, ← Finset.sum_range_reflect]; apply Finset.sum_congr rfl; intro offset member
  have within : offset ≤ degree := by simpa using Finset.mem_range.mp member
  simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, exchangeEpsilon, epsilon, zpow_natCast]
  have signs : (-1 : ℂ) ^ degree * ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) = (-1 : ℂ) ^ offset * (degree.choose offset : ℂ) := by
    have split : (-1 : ℂ) ^ degree = (-1 : ℂ) ^ offset * (-1 : ℂ) ^ (degree - offset) := by rw [← pow_add, Nat.add_sub_of_le within]
    rw [split]
    have squared : ((-1 : ℂ) ^ (degree - offset)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc
      _ = (-1 : ℂ) ^ offset * (((-1 : ℂ) ^ (degree - offset)) ^ 2) * (degree.choose offset : ℂ) := by ring
      _ = _ := by rw [squared]; ring
  have signedSigns : ((-1 : ℂ) ^ degree * exchange) *
      ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
        ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) * exchange := by
    calc
      _ = ((-1 : ℂ) ^ degree *
          ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ))) * exchange := by ring
      _ = _ := by rw [signs]
  rw [signedSigns]; push_cast [Int.natCast_sub within]
  rw [show lastMode + (degree : ℤ) - ((degree : ℤ) - offset) = lastMode + offset by omega, show firstMode + ((degree : ℤ) - offset) = firstMode + degree - offset by omega]

theorem borcherds (leftParity rightParity : ℕ) (leftState rightState vector : Carrier)
    (leftHomogeneous : leftState ∈ homogeneous leftParity)
    (rightHomogeneous : rightState ∈ homogeneous rightParity) (firstMode lastMode parameter : ℤ) :
    BorcherdsEquation leftParity rightParity firstMode parameter lastMode leftState rightState vector := by
  classical
  let exchange := koszul leftParity rightParity
  let discrepancy (first second parameter : ℤ) : Carrier :=
    (∑ᶠ offset : ℕ, jacobiLeftTerm first second parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second parameter leftState rightState vector offset) +
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange first second parameter leftState rightState vector offset)
  obtain ⟨cutoff, localityLaw⟩ := stateField_superLocal leftParity rightParity
    leftState rightState leftHomogeneous rightHomogeneous
  have residueZero (parameter : ℤ) (high : (cutoff : ℤ) ≤ parameter) :
      residue exchange parameter (Y leftState) (Y rightState) = 0 := by
    obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ parameter by omega)
    have vanished : SuperFieldProducts.delta^[degree]
        (superCommutator exchange (Y leftState) (Y rightState)) = 0 :=
      locality_raise exchange (Y leftState) (Y rightState) cutoff degree (by omega) localityLaw
    change FieldNormalProductLocality.delta^[degree]
      (superCommutator exchange (Y leftState) (Y rightState)) = 0 at vanished
    rw [delta_iterate_eq_pow] at vanished
    apply HVertexOperator.coeff_inj
    funext power
    apply LinearMap.ext
    intro input
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
      positive_residue_modes, vanished]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  have highSeed : ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter →
      discrepancy first second parameter = 0 := by
    intro first second parameter high
    have stateZero (offset : ℕ) : mu leftState (parameter + offset) rightState = 0 := by
      have closure := stateField_residue_closure leftParity rightParity leftState rightState
        (parameter + offset) leftHomogeneous rightHomogeneous
      rw [residueZero (parameter + offset) (by omega)] at closure
      change Y (mu leftState (parameter + offset) rightState) = 0 at closure
      have created := stateField_creation (mu leftState (parameter + offset) rightState)
      rw [closure] at created
      simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using created.symm
    have leftZero : (∑ᶠ offset : ℕ, jacobiLeftTerm first second parameter
        leftState rightState vector offset) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro offset
      rw [jacobiLeftTerm, stateZero]
      simp [mu]
    have rightZero : (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second parameter
        leftState rightState vector offset) -
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange first second parameter
          leftState rightState vector offset) = 0 := by
      obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ parameter by omega)
      have vanished := locality_raise exchange (Y leftState) (Y rightState)
        cutoff degree (by omega) localityLaw
      change FieldNormalProductLocality.delta^[degree]
        (superCommutator exchange (Y leftState) (Y rightState)) = 0 at vanished
      rw [delta_iterate_eq_pow] at vanished
      rw [positive_right_products, vanished]
      rfl
    change (∑ᶠ offset : ℕ, jacobiLeftTerm first second parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second parameter leftState rightState vector offset) +
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange first second parameter leftState rightState vector offset) = 0
    rw [leftZero, sub_eq_zero.mp rightZero]
    abel
  have zeroSeed (lastMode parameter : ℤ) : discrepancy 0 lastMode parameter = 0 := by
    have identity := borcherds_zero_first leftParity rightParity parameter lastMode
      leftState rightState vector leftHomogeneous rightHomogeneous
    rw [BorcherdsEquation, right_split] at identity
    change (∑ᶠ offset : ℕ, jacobiLeftTerm 0 lastMode parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm 0 lastMode parameter leftState rightState vector offset) +
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange 0 lastMode parameter leftState rightState vector offset) = 0
    change (∑ᶠ offset : ℕ, jacobiLeftTerm 0 lastMode parameter leftState rightState vector offset) =
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm 0 lastMode parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange 0 lastMode parameter leftState rightState vector offset) at identity
    rw [identity]
    abel
  have recurrence (firstMode lastMode parameter : ℤ) : discrepancy (firstMode + 1) lastMode parameter = discrepancy firstMode (lastMode + 1) parameter + discrepancy firstMode lastMode (parameter + 1) := by
    let weight (parameter : ℤ) (offset : ℕ) := (-1 : ℂ) ^ offset * integerBinomial parameter offset
    let zeroSucc : Option ℕ ≃ ℕ := {
      toFun value := match value with | none => 0 | some offset => offset + 1
      invFun value := match value with | 0 => none | offset + 1 => some offset
      left_inv value := by cases value <;> rfl
      right_inv value := by cases value <;> rfl }
    have splitSum (term : ℕ → Carrier) (finite : Function.HasFiniteSupport term) : ∑ᶠ offset : ℕ, term offset = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
      rw [← finsum_comp_equiv zeroSucc, finsum_option]
      · rfl
      · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have pascal (parameter : ℤ) (offset : ℕ) : integerBinomial (parameter + 1) (offset + 1) = integerBinomial parameter offset + integerBinomial parameter (offset + 1) := by
      unfold integerBinomial; rw [Ring.choose_succ_succ, Int.cast_add]
    have weightedPascal (parameter : ℤ) (offset : ℕ) : weight (parameter + 1) (offset + 1) = weight parameter (offset + 1) - weight parameter offset := by
      dsimp only [weight]; rw [pascal, pow_succ]; ring
    have chooseZero (parameter : ℤ) : integerBinomial parameter 0 = 1 := by simp [integerBinomial]
    have weightZero (parameter : ℤ) : weight parameter 0 = 1 := by simp [weight, chooseZero]
    have sumPascal (parameter : ℤ) (sequence : ℕ → Carrier) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, integerBinomial (parameter + 1) offset • sequence offset) =
      (∑ᶠ offset : ℕ, integerBinomial parameter offset • sequence offset) + (∑ᶠ offset : ℕ, integerBinomial parameter offset • sequence (offset + 1)) := by
      have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
      have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial (parameter + 1) offset • sequence offset) :=
        finite.smul_right (integerBinomial (parameter + 1))
      have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter offset • sequence offset) :=
        finite.smul_right (integerBinomial parameter)
      rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [chooseZero, one_smul]; simp_rw [pascal, add_smul]
      have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter offset • sequence (offset + 1)) :=
        tailFinite.smul_right (integerBinomial parameter)
      have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter (offset + 1) • sequence (offset + 1)) :=
        tailFinite.smul_right (fun offset => integerBinomial parameter (offset + 1))
      rw [finsum_add_distrib firstTail secondTail]; abel
    have sumWeightedPascal (parameter : ℤ) (sequence : ℕ → Carrier) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, weight (parameter + 1) offset • sequence offset) =
      (∑ᶠ offset : ℕ, weight parameter offset • sequence offset) - (∑ᶠ offset : ℕ, weight parameter offset • sequence (offset + 1)) := by
      have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
      have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          weight (parameter + 1) offset • sequence offset) :=
        finite.smul_right (weight (parameter + 1))
      have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter offset • sequence offset) := finite.smul_right (weight parameter)
      rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [weightZero, one_smul]; simp_rw [weightedPascal, sub_smul]
      have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter (offset + 1) • sequence (offset + 1)) :=
        tailFinite.smul_right (fun offset => weight parameter (offset + 1))
      have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter offset • sequence (offset + 1)) :=
        tailFinite.smul_right (weight parameter)
      rw [finsum_sub_distrib firstTail secondTail]; abel
    have firstFinite (start finish : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu (mu leftState (parameter + offset) rightState) (start + finish - offset) vector) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y leftState) rightState)).order - parameter).toNat, ?_⟩; intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu leftState (parameter + offset) rightState = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have secondFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu leftState (start + parameter - offset) (mu rightState (finish + offset) vector)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y rightState) vector)).order - finish).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu rightState (finish + offset) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have thirdFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu rightState (finish + parameter - offset) (mu leftState (start + offset) vector)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y leftState) vector)).order - start).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu leftState (start + offset) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have leftLaw : (∑ᶠ offset : ℕ, jacobiLeftTerm (firstMode + 1) lastMode parameter leftState rightState vector offset) = (∑ᶠ offset : ℕ, jacobiLeftTerm firstMode (lastMode + 1) parameter leftState rightState vector offset) + (∑ᶠ offset : ℕ, jacobiLeftTerm firstMode lastMode (parameter + 1)
      leftState rightState vector offset) := by
      let sequence (offset : ℕ) := mu (mu leftState (parameter + offset) rightState) (firstMode + 1 + lastMode - offset) vector
      have initial (offset : ℕ) : jacobiLeftTerm (firstMode + 1) lastMode parameter leftState rightState vector offset = integerBinomial (firstMode + 1) offset • sequence offset := by rfl
      have current (offset : ℕ) : jacobiLeftTerm firstMode (lastMode + 1) parameter leftState rightState vector offset = integerBinomial firstMode offset • sequence offset := by
        dsimp only [jacobiLeftTerm, sequence]; rw [show firstMode + (lastMode + 1) - (offset : ℤ) = firstMode + 1 + lastMode - offset by omega]
      have shifted (offset : ℕ) : jacobiLeftTerm firstMode lastMode (parameter + 1) leftState rightState vector offset = integerBinomial firstMode offset • sequence (offset + 1) := by
        dsimp only [jacobiLeftTerm, sequence]; push_cast
        rw [show parameter + ((offset : ℤ) + 1) = parameter + 1 + offset by omega, show firstMode + 1 + lastMode - ((offset : ℤ) + 1) = firstMode + lastMode - offset by omega]
      simp_rw [initial, current, shifted]; exact sumPascal firstMode sequence (firstFinite (firstMode + 1) lastMode)
    have firstRightLaw : (∑ᶠ offset : ℕ, jacobiRightFirstTerm (firstMode + 1) lastMode parameter leftState rightState vector offset) = (∑ᶠ offset : ℕ, jacobiRightFirstTerm firstMode (lastMode + 1) parameter leftState rightState vector offset) + (∑ᶠ offset : ℕ,
      jacobiRightFirstTerm firstMode lastMode (parameter + 1) leftState rightState vector offset) := by
      let sequence (offset : ℕ) := mu leftState (firstMode + (parameter + 1) - offset) (mu rightState (lastMode + offset) vector)
      have initial (offset : ℕ) : jacobiRightFirstTerm (firstMode + 1) lastMode parameter leftState rightState vector offset = weight parameter offset • sequence offset := by
        dsimp only [jacobiRightFirstTerm, weight, SuperFieldProducts.weight, sequence]; rw [show firstMode + 1 + parameter = firstMode + (parameter + 1) by omega]
      have current (offset : ℕ) : jacobiRightFirstTerm firstMode lastMode (parameter + 1) leftState rightState vector offset = weight (parameter + 1) offset • sequence offset := by rfl
      have shifted (offset : ℕ) : jacobiRightFirstTerm firstMode (lastMode + 1) parameter leftState rightState vector offset = weight parameter offset • sequence (offset + 1) := by
        dsimp only [jacobiRightFirstTerm, weight, SuperFieldProducts.weight, sequence]; push_cast
        rw [show firstMode + (parameter + 1) - ((offset : ℤ) + 1) = firstMode + parameter - offset by omega, show lastMode + ((offset : ℤ) + 1) = lastMode + 1 + offset by omega]
      simp_rw [initial, current, shifted]; exact sub_eq_iff_eq_add'.mp (sumWeightedPascal parameter sequence (secondFinite firstMode lastMode (parameter + 1))).symm
    have sign : exchangeEpsilon exchange (parameter + 1) =
        -exchangeEpsilon exchange parameter := by
      have epsilonStep : epsilon (parameter + 1) = -epsilon parameter := by
        rw [epsilon, epsilon, zpow_add₀ (by norm_num)]
        norm_num
      rw [exchangeEpsilon, exchangeEpsilon, epsilonStep, neg_mul]
    have secondRightLaw : (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange (firstMode + 1) lastMode parameter leftState rightState vector offset) = (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange firstMode (lastMode + 1) parameter leftState rightState vector offset) + (∑ᶠ offset : ℕ,
      jacobiRightSecondTerm exchange firstMode lastMode (parameter + 1) leftState rightState vector offset) := by
      let sequence (offset : ℕ) := mu rightState (lastMode + (parameter + 1) - offset) (mu leftState (firstMode + offset) vector)
      have initial (offset : ℕ) : jacobiRightSecondTerm exchange firstMode (lastMode + 1) parameter leftState rightState vector offset = exchangeEpsilon exchange parameter • (weight parameter offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, SuperFieldProducts.weight, sequence]; rw [show lastMode + 1 + parameter = lastMode + (parameter + 1) by omega, smul_comm]
      have current (offset : ℕ) : jacobiRightSecondTerm exchange firstMode lastMode (parameter + 1) leftState rightState vector offset = -exchangeEpsilon exchange parameter • (weight (parameter + 1) offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, SuperFieldProducts.weight, sequence]; rw [sign, smul_comm]
      have shifted (offset : ℕ) : jacobiRightSecondTerm exchange (firstMode + 1) lastMode parameter leftState rightState vector offset = exchangeEpsilon exchange parameter • (weight parameter offset • sequence (offset + 1)) := by
        dsimp only [jacobiRightSecondTerm, weight, SuperFieldProducts.weight, sequence]; push_cast
        rw [show lastMode + (parameter + 1) - ((offset : ℤ) + 1) = lastMode + parameter - offset by omega, show firstMode + ((offset : ℤ) + 1) = firstMode + 1 + offset by omega, smul_comm]
      simp_rw [initial, current, shifted, ← smul_finsum]; rw [sumWeightedPascal parameter sequence (thirdFinite firstMode lastMode (parameter + 1))]; module
    unfold discrepancy; rw [leftLaw, firstRightLaw, secondRightLaw]; abel
  have allIndices : ∀ firstMode lastMode parameter : ℤ, discrepancy firstMode lastMode parameter = 0 := by
    have positive (degree : ℕ) : ∀ lastMode parameter : ℤ, discrepancy degree lastMode parameter = 0 := by
      induction degree with
      | zero => exact zeroSeed
      | succ degree inductionHypothesis =>
        intro lastMode parameter; rw [Nat.cast_add, Nat.cast_one, recurrence, inductionHypothesis, inductionHypothesis, add_zero]
    have negative (distance : ℕ) : ∀ magnitude : ℕ, ∀ lastMode : ℤ, discrepancy (-(magnitude : ℤ)) lastMode ((cutoff : ℤ) - distance) = 0 := by
      induction distance with
      | zero =>
        intro magnitude lastMode; exact highSeed _ _ _ (by omega)
      | succ distance outerHypothesis =>
        intro magnitude
        induction magnitude with
        | zero => intro lastMode; exact zeroSeed _ _
        | succ magnitude innerHypothesis =>
          intro lastMode
          have law := recurrence (-((magnitude + 1 : ℕ) : ℤ)) (lastMode - 1) ((cutoff : ℤ) - (distance + 1 : ℕ))
          rw [show -((magnitude + 1 : ℕ) : ℤ) + 1 = -(magnitude : ℤ) by omega, show lastMode - 1 + 1 = lastMode by omega, show (cutoff : ℤ) - (distance + 1 : ℕ) + 1 = (cutoff : ℤ) - distance by
            omega, innerHypothesis, outerHypothesis, add_zero] at law
          exact law.symm
    intro firstMode lastMode parameter
    by_cases nonnegative : 0 ≤ firstMode
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
      exact positive degree lastMode parameter
    · by_cases high : (cutoff : ℤ) ≤ parameter
      · exact highSeed firstMode lastMode parameter high
      · let magnitude := (-firstMode).toNat
        let distance := ((cutoff : ℤ) - parameter).toNat
        have pEquality : firstMode = -(magnitude : ℤ) := by dsimp [magnitude]; omega
        have rEquality : parameter = (cutoff : ℤ) - distance := by dsimp [distance]; omega
        rw [pEquality, rEquality]; exact negative distance magnitude lastMode
  rw [BorcherdsEquation, right_split]
  have law := allIndices firstMode lastMode parameter
  change (∑ᶠ offset : ℕ, jacobiLeftTerm firstMode lastMode parameter leftState rightState vector offset) =
    (∑ᶠ offset : ℕ, jacobiRightFirstTerm firstMode lastMode parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm exchange firstMode lastMode parameter leftState rightState vector offset)
  apply sub_eq_zero.mp
  calc
    _ = discrepancy firstMode lastMode parameter := by dsimp [discrepancy]; abel
    _ = 0 := law

theorem mixed_borcherds (first parameter last : ℤ) (left right vector : Carrier) :
    MixedBorcherdsEquation first parameter last left right vector := by
  have expansion : borcherdsLeft first parameter last left right vector =
      (borcherdsLeft first parameter last (parityPart 0 left) (parityPart 0 right) vector +
        borcherdsLeft first parameter last (parityPart 0 left) (parityPart 1 right) vector) +
      (borcherdsLeft first parameter last (parityPart 1 left) (parityPart 0 right) vector +
        borcherdsLeft first parameter last (parityPart 1 left) (parityPart 1 right) vector) := by
    calc
      borcherdsLeft first parameter last left right vector =
          borcherdsLeft first parameter last (parityPart 0 left + parityPart 1 left)
            (parityPart 0 right + parityPart 1 right) vector := by
        rw [parity_decomposition, parity_decomposition]
      _ = _ := by
        rw [borcherdsLeft_add_left, borcherdsLeft_add_right, borcherdsLeft_add_right]
  rw [MixedBorcherdsEquation, expansion]
  simp only [mixedBorcherdsRight, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [borcherds 0 0 _ _ vector (parityPart_mem 0 left) (parityPart_mem 0 right) first last parameter,
    borcherds 0 1 _ _ vector (parityPart_mem 0 left) (parityPart_mem 1 right) first last parameter,
    borcherds 1 0 _ _ vector (parityPart_mem 1 left) (parityPart_mem 0 right) first last parameter,
    borcherds 1 1 _ _ vector (parityPart_mem 1 left) (parityPart_mem 1 right) first last parameter]

end
end D5.S3.VertexAlgebra.BcGhostSuperJacobi

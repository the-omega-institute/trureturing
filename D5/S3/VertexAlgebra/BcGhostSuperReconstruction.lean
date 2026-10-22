/- GID: D5/S3/VertexAlgebra/BcGhostSuperReconstruction
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostSuperReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Creative-field uniqueness reconstructs fields using explicitly supplied creativity, covariance and relative locality, not a assumed final endpoint. It yields translation-state differentiation, signed normal closure and factorial-normalized original translation powers. -/

import D5.S3.VertexAlgebra.BcGhostSuperLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperReconstruction

open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField BcGhostSuperLocality
open FieldNormalProduct SuperFieldProducts SuperFieldLocality
open scoped VertexOperator

noncomputable section

theorem delta_binomial (distribution : ℤ → ℤ → Module.End ℂ Carrier)
    (order : ℕ) (first second : ℤ) :
    (SuperFieldProducts.delta^[order] distribution) first second =
      ∑ offset ∈ Finset.range (order + 1),
        ((-1 : ℂ) ^ offset * (order.choose offset : ℂ)) •
          distribution (first + (order : ℤ) - offset) (second + offset) := by
  let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier) := {
    toFun value := fun left right => value (left + 1) right
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier) := {
    toFun value := fun left right => value left (right + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have commute : Commute (-shiftRight) shiftLeft := by
    apply LinearMap.ext
    intro value
    funext left right
    simp [shiftLeft, shiftRight]
  have leftPower (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Carrier) :
      (shiftLeft ^ degree) value = fun left right => value (left + degree) right := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
      funext left right
      change value (left + 1 + degree) right = value (left + (degree + 1 : ℕ)) right
      congr 1
      push_cast
      omega
  have rightPower (degree : ℕ) (value : ℤ → ℤ → Module.End ℂ Carrier) :
      ((-shiftRight) ^ degree) value = fun left right =>
        (-1 : ℂ) ^ degree • value left (right + degree) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
      funext left right
      change -((-1 : ℂ) ^ degree • value left (right + 1 + degree)) =
        (-1 : ℂ) ^ (degree + 1) • value left (right + (degree + 1 : ℕ))
      rw [pow_succ', mul_smul, neg_one_smul]
      have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by
        push_cast
        omega
      rw [indices]
  have equation :
      (FieldNormalProductLocality.deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Carrier)) =
        -shiftRight + shiftLeft := by
    apply LinearMap.ext
    intro value
    funext left right
    simp [FieldNormalProductLocality.deltaEnd, FieldNormalProductLocality.delta,
      shiftLeft, shiftRight]
    abel
  change (FieldNormalProductLocality.delta^[order] distribution) first second = _
  rw [delta_iterate_eq_pow]
  rw [equation, commute.add_pow, LinearMap.sum_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro offset member
  have within : offset ≤ order := by simpa using Finset.mem_range.mp member
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
    rightPower, leftPower, Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]
  congr 2
  push_cast [Int.natCast_sub within]
  omega

theorem relative_vacuum_uniqueness (parity : ℕ) (operator : VertexOperator ℂ Carrier)
    (creative : ∀ mode : ℤ, 0 ≤ mode → (operator[[mode]]) (vacuum : Carrier) = 0)
    (initial : (operator[[-1]]) (vacuum : Carrier) = 0)
    (covariant : ∀ mode : ℤ, translation * (operator[[mode]]) - (operator[[mode]]) * translation =
      -(mode : ℂ) • (operator[[mode - 1]]))
    (relative : ∀ grade : ℕ, ∀ state ∈ homogeneous grade,
      SuperLocal parity grade operator (Y state)) : operator = 0 := by
  have vacuumNegative (degree : ℕ) : (operator[[-(degree : ℤ) - 1]]) (vacuum : Carrier) = 0 := by
    induction degree with
    | zero => simpa using initial
    | succ degree inductionHypothesis =>
      have law := congrArg (fun endomorphism : Module.End ℂ Carrier =>
        endomorphism (vacuum : Carrier)) (covariant (-(degree : ℤ) - 1))
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        inductionHypothesis, translation_vacuum, map_zero, sub_self] at law
      rw [show -(degree : ℤ) - 1 - 1 = -((degree + 1 : ℕ) : ℤ) - 1 by omega] at law
      have scalar : -((-(degree : ℤ) - 1 : ℤ) : ℂ) = (degree : ℂ) + 1 := by
        push_cast
        ring
      rw [scalar] at law
      have nonzero : (degree : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
      exact (smul_eq_zero.mp law.symm).resolve_left nonzero
  have vacuumZero (mode : ℤ) : (operator[[mode]]) (vacuum : Carrier) = 0 := by
    by_cases nonnegative : 0 ≤ mode
    · exact creative mode nonnegative
    · let degree := (-mode - 1).toNat
      rw [show mode = -(degree : ℤ) - 1 by dsimp [degree]; omega]
      exact vacuumNegative degree
  have homogeneousModes (grade : ℕ) (state : Carrier) (stateHomogeneous : state ∈ homogeneous grade)
      (mode : ℤ) : (operator[[mode]]) state = 0 := by
    obtain ⟨order, killed⟩ := relative grade state stateHomogeneous
    have coefficient := congrArg (fun value : ℤ → ℤ → Module.End ℂ Carrier =>
      value (mode - order) (-1) (vacuum : Carrier)) killed
    rw [delta_binomial, LinearMap.sum_apply] at coefficient
    simp only [LinearMap.smul_apply] at coefficient
    have simplify : (∑ offset ∈ Finset.range (order + 1),
        ((-1 : ℂ) ^ offset * (order.choose offset : ℂ)) •
          superCommutator (koszul parity grade) operator (Y state)
            (mode - order + (order : ℤ) - offset) (-1 + offset) (vacuum : Carrier)) =
        (operator[[mode]]) state := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
          Nat.cast_zero, sub_zero, add_zero, show mode - (order : ℤ) + order = mode by omega,
          superCommutator, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
          vacuumZero, map_zero, smul_zero, sub_zero, stateField_creation]
      · intro offset member distinct
        have vanish : ((Y state)[[-1 + (offset : ℤ)]]) (vacuum : Carrier) = 0 :=
          stateField_creativity state _ (by omega)
        simp only [superCommutator, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.mul_apply, vanish, vacuumZero, map_zero, smul_zero, sub_self]
      · simp
    rw [simplify] at coefficient
    exact coefficient
  have allModes (mode : ℤ) (state : Carrier) : (operator[[mode]]) state = 0 := by
    rw [← parity_decomposition state, map_add,
      homogeneousModes 0 _ (parityPart_mem 0 state) mode,
      homogeneousModes 1 _ (parityPart_mem 1 state) mode, add_zero]
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using allModes (-power - 1) vector

theorem creative_local_field_eq (parity : ℕ) (operator : VertexOperator ℂ Carrier) (state : Carrier)
    (stateHomogeneous : state ∈ homogeneous parity)
    (creative : ∀ mode : ℤ, 0 ≤ mode → (operator[[mode]]) (vacuum : Carrier) = 0)
    (creation : (operator[[-1]]) (vacuum : Carrier) = state)
    (covariant : ∀ mode : ℤ, translation * (operator[[mode]]) - (operator[[mode]]) * translation =
      -(mode : ℂ) • (operator[[mode - 1]]))
    (relative : ∀ grade : ℕ, ∀ other ∈ homogeneous grade,
      SuperLocal parity grade operator (Y other)) : operator = Y state := by
  let difference := operator - Y state
  have differenceCreative (mode : ℤ) (nonnegative : 0 ≤ mode) :
      (difference[[mode]]) (vacuum : Carrier) = 0 := by
    simp only [difference, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      creative mode nonnegative, stateField_creativity state mode nonnegative, sub_self]
  have differenceInitial : (difference[[-1]]) (vacuum : Carrier) = 0 := by
    simp only [difference, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      creation, stateField_creation, sub_self]
  have differenceCovariant (mode : ℤ) :
      translation * (difference[[mode]]) - (difference[[mode]]) * translation =
        -(mode : ℂ) • (difference[[mode - 1]]) := by
    have firstZero : covarianceDefect mode operator = 0 := by
      change (translation * (operator[[mode]]) - (operator[[mode]]) * translation) +
        (mode : ℂ) • (operator[[mode - 1]]) = 0
      rw [covariant, neg_smul, neg_add_cancel]
    have secondZero : covarianceDefect mode (Y state) = 0 := by
      change (translation * ((Y state)[[mode]]) - ((Y state)[[mode]]) * translation) +
        (mode : ℂ) • ((Y state)[[mode - 1]]) = 0
      rw [stateField_covariance, neg_smul, neg_add_cancel]
    have zeroDefect : covarianceDefect mode difference = 0 := by
      dsimp only [difference]
      rw [map_sub, firstZero, secondZero, sub_self]
    change (translation * (difference[[mode]]) - (difference[[mode]]) * translation) +
      (mode : ℂ) • (difference[[mode - 1]]) = 0 at zeroDefect
    exact (eq_neg_of_add_eq_zero_left zeroDefect).trans (neg_smul _ _).symm
  have differenceRelative (grade : ℕ) (other : Carrier) (otherHomogeneous : other ∈ homogeneous grade) :
      SuperLocal parity grade difference (Y other) := by
    dsimp only [difference]
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (Y state)]
    exact superLocal_add_left parity grade _ _ _ (relative grade other otherHomogeneous)
      (superLocal_smul_left parity grade (-1) _ _
        (stateField_superLocal parity grade state other stateHomogeneous otherHomogeneous))
  have vanished := relative_vacuum_uniqueness parity difference differenceCreative
    differenceInitial differenceCovariant differenceRelative
  exact sub_eq_zero.mp vanished

theorem translation_mem (parity : ℕ) (state : Carrier) (stateHomogeneous : state ∈ homogeneous parity) :
    translation state ∈ homogeneous parity := by
  rw [stateField_translation_as_mode]
  have vacuumHomogeneous : (vacuum : Carrier) ∈ homogeneous 0 := by
    exact single_mem 0 ∅ 1 (by simp [subsetParity])
  simpa only [Nat.add_zero] using
    stateField_mem parity state stateHomogeneous (-2) 0 vacuum vacuumHomogeneous

theorem stateField_translation_homogeneous (parity : ℕ) (state : Carrier)
    (stateHomogeneous : state ∈ homogeneous parity) :
    Y (translation state) = dividedDerivative 1 (Y state) := by
  apply Eq.symm
  apply creative_local_field_eq parity _ (translation state)
    (translation_mem parity state stateHomogeneous)
  · exact derivative_creative 1 (Y state) vacuum (stateField_creativity state)
  · rw [derivative_modes]
    simp only [show -(-1 : ℤ) - 1 + (1 : ℕ) = 1 by norm_num,
      integerBinomial, Ring.choose_one_right, Int.cast_one, one_smul,
      show (-1 : ℤ) - (1 : ℕ) = -2 by norm_num]
    exact (stateField_translation_as_mode state).symm
  · exact derivative_translation translation (Y state) (stateField_covariance state) 1
  · intro grade other otherHomogeneous
    exact dividedDerivative_superLocal parity grade 1 _ _
      (stateField_superLocal parity grade state other stateHomogeneous otherHomogeneous)

theorem stateField_translation (state : Carrier) :
    Y (translation state) = dividedDerivative 1 (Y state) := by
  calc
    Y (translation state) =
        Y (translation (parityPart 0 state)) + Y (translation (parityPart 1 state)) := by
      rw [← map_add, ← map_add, parity_decomposition]
    _ = dividedDerivative 1 (Y (parityPart 0 state)) +
        dividedDerivative 1 (Y (parityPart 1 state)) := by
      rw [stateField_translation_homogeneous 0 _ (parityPart_mem 0 state),
        stateField_translation_homogeneous 1 _ (parityPart_mem 1 state)]
    _ = dividedDerivative 1 (Y (parityPart 0 state) + Y (parityPart 1 state)) :=
      (derivative_add 1 _ _).symm
    _ = dividedDerivative 1 (Y state) := by rw [← map_add, parity_decomposition]

theorem stateField_normal_closure (leftParity rightParity : ℕ) (left right : Carrier)
    (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    Y (((Y left)[[-1]]) right) = normal (koszul leftParity rightParity) (Y left) (Y right) := by
  have vacuumLaw := residue_vacuum (koszul leftParity rightParity) (-1) (Y left) (Y right)
    (vacuum : Carrier) (stateField_creativity left) (stateField_creativity right)
  apply Eq.symm
  apply creative_local_field_eq (leftParity + rightParity) _ (((Y left)[[-1]]) right)
    (stateField_mem leftParity left leftHomogeneous (-1) rightParity right rightHomogeneous)
  · exact vacuumLaw.2
  · simpa only [stateField_creation, normal] using vacuumLaw.1
  · exact residue_translation (koszul leftParity rightParity) (-1) translation (Y left) (Y right)
      (stateField_covariance left) (stateField_covariance right)
  · intro grade other otherHomogeneous
    exact normal_superLocal leftParity rightParity grade (Y left) (Y right) (Y other)
      (stateField_superLocal leftParity grade left other leftHomogeneous otherHomogeneous)
      (stateField_superLocal rightParity grade right other rightHomogeneous otherHomogeneous)
      (stateField_superLocal leftParity rightParity left right leftHomogeneous rightHomogeneous)



def stateHasse (degree : ℕ) (state : Carrier) : Carrier :=
  ((Y state)[[-(degree : ℤ) - 1]]) (vacuum : Carrier)

theorem stateHasse_step (degree : ℕ) (state : Carrier) :
    translation (stateHasse degree state) =
      ((degree + 1 : ℕ) : ℂ) • stateHasse (degree + 1) state := by
  have law := congrArg (fun endomorphism : Module.End ℂ Carrier => endomorphism (vacuum : Carrier))
    (stateField_covariance state (-(degree : ℤ) - 1))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    translation_vacuum, map_zero, sub_zero] at law
  have scalar : -((-(degree : ℤ) - 1 : ℤ) : ℂ) = ((degree + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [scalar, show -(degree : ℤ) - 1 - 1 = -((degree + 1 : ℕ) : ℤ) - 1 by omega] at law
  exact law

theorem stateHasse_factorial (degree : ℕ) (state : Carrier) :
    (degree.factorial : ℂ) • stateHasse degree state = (translation ^ degree) state := by
  induction degree with
  | zero => simp [stateHasse, stateField_creation]
  | succ degree inductionHypothesis =>
    rw [pow_succ', Module.End.mul_apply, ← inductionHypothesis, map_smul, stateHasse_step,
      smul_smul, Nat.factorial_succ, Nat.cast_mul]
    rw [mul_comm]



end
end D5.S3.VertexAlgebra.BcGhostSuperReconstruction

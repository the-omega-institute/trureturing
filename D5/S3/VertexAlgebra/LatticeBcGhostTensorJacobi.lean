/- GID: D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostTensorJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual tensor signed Borcherds terms and finite-support boundary on the original carrier. -/

import D5.S3.VertexAlgebra.LatticeBcGhostTensorLocality
import D5.S3.VertexAlgebra.SuperFieldProducts
import D5.S3.VertexAlgebra.SuperFieldLocality
import D5.S3.VertexAlgebra.SuperStateFieldReconstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostTensorJacobi

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality
open LatticeBcGhostTensorStateField LatticeBcGhostTensorLocality
open SuperFieldProducts SuperFieldLocality
open scoped TensorProduct VertexOperator

abbrev State (D : LatticeData) := LatticeBcGhostTensorStateField.State D

def mu (D : LatticeData) (left : State D) (mode : ℤ) (right : State D) : State D :=
  ((LatticeBcGhostTensorStateField.stateField D left)[[mode]]) right

def borcherdsLeftTerm (D : LatticeData) (first parameter last : ℤ)
    (left right vector : State D) (offset : ℕ) : State D :=
  integerBinomial first offset •
    ((LatticeBcGhostTensorStateField.stateField D
      (mu D left (parameter + offset) right))[[first + last - offset]]) vector

def borcherdsRightTerm (leftParity rightParity : ℕ) (D : LatticeData)
    (first parameter last : ℤ) (left right vector : State D) (offset : ℕ) : State D :=
  weight parameter offset •
    (((LatticeBcGhostTensorStateField.stateField D left)[[first + parameter - offset]])
        (((LatticeBcGhostTensorStateField.stateField D right)[[last + offset]]) vector) -
      (epsilon parameter * koszul leftParity rightParity) •
        ((LatticeBcGhostTensorStateField.stateField D right)[[parameter + last - offset]])
          (((LatticeBcGhostTensorStateField.stateField D left)[[first + offset]]) vector))

def borcherdsLeft (D : LatticeData) (first parameter last : ℤ)
    (left right vector : State D) : State D :=
  ∑ᶠ offset : ℕ, borcherdsLeftTerm D first parameter last left right vector offset

def borcherdsRight (leftParity rightParity : ℕ) (D : LatticeData)
    (first parameter last : ℤ) (left right vector : State D) : State D :=
  ∑ᶠ offset : ℕ,
    borcherdsRightTerm leftParity rightParity D first parameter last left right vector offset

def BorcherdsEquation (leftParity rightParity : ℕ) (D : LatticeData)
    (first parameter last : ℤ) (left right vector : State D) : Prop :=
  borcherdsLeft D first parameter last left right vector =
    borcherdsRight leftParity rightParity D first parameter last left right vector

theorem borcherds_left_finite (D : LatticeData) (first parameter last : ℤ)
    (left right vector : State D) :
    Function.HasFiniteSupport (borcherdsLeftTerm D first parameter last left right vector) := by
  refine (increasing_finite (LatticeBcGhostTensorStateField.stateField D left)
    parameter right).subset ?_
  intro offset member vanish
  apply member
  simp [borcherdsLeftTerm, mu, vanish]

theorem borcherds_right_finite (leftParity rightParity : ℕ) (D : LatticeData)
    (first parameter last : ℤ) (left right vector : State D) :
    Function.HasFiniteSupport
      (borcherdsRightTerm leftParity rightParity D first parameter last left right vector) :=
  ((forward_finite (LatticeBcGhostTensorStateField.stateField D left)
      (LatticeBcGhostTensorStateField.stateField D right) (first + parameter) last vector).sub
    ((forward_finite (LatticeBcGhostTensorStateField.stateField D right)
      (LatticeBcGhostTensorStateField.stateField D left) (parameter + last) first vector).smul_right
        (fun _ => epsilon parameter * koszul leftParity rightParity))).smul_right
          (weight parameter)

theorem borcherds_left_zero (D : LatticeData) (parameter last : ℤ)
    (left right vector : State D) :
    borcherdsLeft D 0 parameter last left right vector =
      ((LatticeBcGhostTensorStateField.stateField D
        (mu D left parameter right))[[last]]) vector := by
  unfold borcherdsLeft
  rw [finsum_eq_single _ 0]
  · simp [borcherdsLeftTerm, integerBinomial, mu]
  · intro offset different
    have positive : 0 < offset := Nat.pos_of_ne_zero different
    simp [borcherdsLeftTerm, integerBinomial, Ring.choose_zero_pos ℤ positive]

theorem borcherds_right_zero (leftParity rightParity : ℕ) (D : LatticeData)
    (parameter last : ℤ) (left right vector : State D) :
    borcherdsRight leftParity rightParity D 0 parameter last left right vector =
      residueLeft parameter last (LatticeBcGhostTensorStateField.stateField D left)
        (LatticeBcGhostTensorStateField.stateField D right) vector -
      (epsilon parameter * koszul leftParity rightParity) •
        residueRight parameter last (LatticeBcGhostTensorStateField.stateField D left)
          (LatticeBcGhostTensorStateField.stateField D right) vector := by
  unfold borcherdsRight
  have termEquality (offset : ℕ) :
      borcherdsRightTerm leftParity rightParity D 0 parameter last left right vector offset =
        weight parameter offset •
          ((LatticeBcGhostTensorStateField.stateField D left)[[parameter - offset]])
            (((LatticeBcGhostTensorStateField.stateField D right)[[last + offset]]) vector) -
        (epsilon parameter * koszul leftParity rightParity) •
          (weight parameter offset •
            ((LatticeBcGhostTensorStateField.stateField D right)
              [[parameter + last - offset]])
              (((LatticeBcGhostTensorStateField.stateField D left)[[offset]]) vector)) := by
    dsimp [borcherdsRightTerm]
    rw [zero_add, zero_add, smul_sub, smul_comm]
  simp_rw [termEquality]
  have reverseFinite :=
    (residue_right_finite parameter last (LatticeBcGhostTensorStateField.stateField D left)
      (LatticeBcGhostTensorStateField.stateField D right) vector).smul_right
      (fun _ => epsilon parameter * koszul leftParity rightParity)
  simp only [Pi.smul_def'] at reverseFinite
  rw [finsum_sub_distrib
      (residue_left_finite parameter last (LatticeBcGhostTensorStateField.stateField D left)
        (LatticeBcGhostTensorStateField.stateField D right) vector) reverseFinite,
    ← smul_finsum' (epsilon parameter * koszul leftParity rightParity)
      (residue_right_finite parameter last (LatticeBcGhostTensorStateField.stateField D left)
        (LatticeBcGhostTensorStateField.stateField D right) vector)]
  rfl

theorem stateField_translation_as_mode (D : LatticeData) (state : State D) :
    LatticeBcGhostTensorStateField.translation D state =
      ((LatticeBcGhostTensorStateField.stateField D state)[[-2]])
        (LatticeBcGhostTensorStateField.vacuum D) := by
  have law := congrArg (fun endomorphism : Module.End ℂ (State D) =>
    endomorphism (LatticeBcGhostTensorStateField.vacuum D))
    (LatticeBcGhostTensorStateField.stateField_covariance D state (-1))
  simpa only [LinearMap.sub_apply, Module.End.mul_apply,
    LatticeBcGhostTensorStateField.stateField_creation,
    LatticeBcGhostTensorStateField.translation_vacuum, map_zero, sub_zero,
    Int.cast_neg, Int.cast_one, neg_neg, one_smul,
    show (-1 : ℤ) - 1 = -2 by norm_num] using law

theorem translation_mem (D : LatticeData) (parity : ℕ) (state : State D)
    (member : state ∈ LatticeBcGhostTensorStateField.homogeneous parity) :
    LatticeBcGhostTensorStateField.translation D state ∈
      LatticeBcGhostTensorStateField.homogeneous parity := by
  rw [stateField_translation_as_mode]
  have vacuumMember : LatticeBcGhostTensorStateField.vacuum D ∈
      LatticeBcGhostTensorStateField.homogeneous 0 := by
    apply LatticeBcGhostTensorStateField.tmul_mem
    exact BcGhostSuperGenerators.single_mem 0 ∅ 1 (by simp [BcGhostSuperGenerators.subsetParity])
  simpa only [Nat.add_zero] using LatticeBcGhostTensorStateField.stateField_mem parity 0
    state (LatticeBcGhostTensorStateField.vacuum D) member vacuumMember (-2)

theorem stateField_translation_homogeneous (D : LatticeData) (parity : ℕ) (state : State D)
    (member : state ∈ LatticeBcGhostTensorStateField.homogeneous parity) :
    LatticeBcGhostTensorStateField.stateField D
      (LatticeBcGhostTensorStateField.translation D state) =
      FieldNormalProduct.dividedDerivative 1
        (LatticeBcGhostTensorStateField.stateField D state) := by
  let target := LatticeBcGhostTensorStateField.stateField D
    (LatticeBcGhostTensorStateField.translation D state)
  let derived := FieldNormalProduct.dividedDerivative 1
    (LatticeBcGhostTensorStateField.stateField D state)
  have derivedInitial : (derived[[-1]]) (LatticeBcGhostTensorStateField.vacuum D) =
      LatticeBcGhostTensorStateField.translation D state := by
    dsimp only [derived]
    rw [derivative_modes]
    simp only [show -(-1 : ℤ) - 1 + (1 : ℕ) = 1 by norm_num,
      integerBinomial, Ring.choose_one_right, Int.cast_one, one_smul,
      show (-1 : ℤ) - (1 : ℕ) = -2 by norm_num]
    exact (stateField_translation_as_mode D state).symm
  have derivedCreative := derivative_creative 1
    (LatticeBcGhostTensorStateField.stateField D state) (LatticeBcGhostTensorStateField.vacuum D)
    (LatticeBcGhostTensorStateField.stateField_creativity D state)
  have derivedCovariant := derivative_translation (LatticeBcGhostTensorStateField.translation D)
    (LatticeBcGhostTensorStateField.stateField D state)
    (LatticeBcGhostTensorStateField.stateField_covariance D state) 1
  have targetCovariant := LatticeBcGhostTensorStateField.stateField_covariance D
    (LatticeBcGhostTensorStateField.translation D state)
  have vanish : derived - target = 0 := by
    apply SuperStateFieldReconstruction.relative_vacuum_uniqueness
      (LatticeBcGhostTensorStateField.stateField D)
      (LatticeBcGhostTensorStateField.vacuum D)
      (LatticeBcGhostTensorStateField.translation D)
      LatticeBcGhostTensorStateField.parityPart LatticeBcGhostTensorStateField.homogeneous
      LatticeBcGhostTensorStateField.parity_decomposition
      LatticeBcGhostTensorStateField.parityPart_mem
      (LatticeBcGhostTensorStateField.translation_vacuum D)
      (LatticeBcGhostTensorStateField.stateField_creation D)
      (LatticeBcGhostTensorStateField.stateField_creativity D) parity
    · intro mode nonnegative
      dsimp only [derived]
      simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply,
        derivedCreative mode nonnegative,
        target, LatticeBcGhostTensorStateField.stateField_creativity D
          (LatticeBcGhostTensorStateField.translation D state) mode nonnegative, sub_self]
    · simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, derivedInitial,
        target, LatticeBcGhostTensorStateField.stateField_creation, sub_self]
    · intro mode
      simp only [map_sub, Pi.sub_apply, mul_sub, sub_mul, smul_sub]
      calc
        _ = (LatticeBcGhostTensorStateField.translation D * (derived[[mode]]) -
          (derived[[mode]]) * LatticeBcGhostTensorStateField.translation D) -
          (LatticeBcGhostTensorStateField.translation D * (target[[mode]]) -
          (target[[mode]]) * LatticeBcGhostTensorStateField.translation D) := by abel
        _ = _ := by rw [derivedCovariant, targetCovariant]
    · intro grade other otherMember
      rw [sub_eq_add_neg, ← neg_one_smul ℂ target]
      apply superLocal_add_left
      · exact dividedDerivative_superLocal parity grade 1 _ _
          (homogeneous_superFieldLocal D parity grade state other member otherMember)
      · exact superLocal_smul_left parity grade (-1) _ _
          (homogeneous_superFieldLocal D parity grade
            (LatticeBcGhostTensorStateField.translation D state) other
            (translation_mem D parity state member) otherMember)
  exact (sub_eq_zero.mp vanish).symm

theorem stateField_translation (D : LatticeData) (state : State D) :
    LatticeBcGhostTensorStateField.stateField D
      (LatticeBcGhostTensorStateField.translation D state) =
      FieldNormalProduct.dividedDerivative 1
        (LatticeBcGhostTensorStateField.stateField D state) := by
  calc
    _ = LatticeBcGhostTensorStateField.stateField D
          (LatticeBcGhostTensorStateField.translation D
            (LatticeBcGhostTensorStateField.parityPart 0 state)) +
        LatticeBcGhostTensorStateField.stateField D
          (LatticeBcGhostTensorStateField.translation D
            (LatticeBcGhostTensorStateField.parityPart 1 state)) := by
      rw [← map_add, ← map_add, LatticeBcGhostTensorStateField.parity_decomposition]
    _ = _ := by
      rw [stateField_translation_homogeneous D 0 _
        (LatticeBcGhostTensorStateField.parityPart_mem 0 state),
        stateField_translation_homogeneous D 1 _
        (LatticeBcGhostTensorStateField.parityPart_mem 1 state),
        ← derivative_add, ← map_add, LatticeBcGhostTensorStateField.parity_decomposition]

theorem stateField_residue_mem (D : LatticeData) (leftParity rightParity inputParity : ℕ)
    (left right vector : State D) (parameter mode : ℤ)
    (leftMember : left ∈ LatticeBcGhostTensorStateField.homogeneous leftParity)
    (rightMember : right ∈ LatticeBcGhostTensorStateField.homogeneous rightParity)
    (vectorMember : vector ∈ LatticeBcGhostTensorStateField.homogeneous inputParity) :
    ((residue (koszul leftParity rightParity) parameter
      (LatticeBcGhostTensorStateField.stateField D left)
      (LatticeBcGhostTensorStateField.stateField D right))[[mode]]) vector ∈
        LatticeBcGhostTensorStateField.homogeneous (leftParity + rightParity + inputParity) := by
  classical
  have sumMember (term : ℕ → State D) (finite : Function.HasFiniteSupport term)
      (members : ∀ offset, term offset ∈
        LatticeBcGhostTensorStateField.homogeneous (leftParity + rightParity + inputParity)) :
      (∑ᶠ offset : ℕ, term offset) ∈
        LatticeBcGhostTensorStateField.homogeneous (leftParity + rightParity + inputParity) := by
    rw [finsum_eq_sum_of_support_subset _ (s := finite.toFinset) (by
      intro index member
      exact finite.mem_toFinset.mpr member)]
    exact (LatticeBcGhostTensorStateField.homogeneous _).sum_mem (fun offset _ => members offset)
  rw [residue_modes]
  apply (LatticeBcGhostTensorStateField.homogeneous _).sub_mem
  · apply sumMember _ (residue_left_finite parameter mode _ _ vector)
    intro offset
    apply (LatticeBcGhostTensorStateField.homogeneous _).smul_mem
    rw [show leftParity + rightParity + inputParity =
      leftParity + (rightParity + inputParity) by omega]
    exact LatticeBcGhostTensorStateField.stateField_mem leftParity
      (rightParity + inputParity) left _ leftMember
      (LatticeBcGhostTensorStateField.stateField_mem rightParity inputParity right vector
        rightMember vectorMember (mode + offset)) (parameter - offset)
  · apply (LatticeBcGhostTensorStateField.homogeneous _).smul_mem
    apply sumMember _ (residue_right_finite parameter mode _ _ vector)
    intro offset
    apply (LatticeBcGhostTensorStateField.homogeneous _).smul_mem
    rw [show leftParity + rightParity + inputParity =
      rightParity + (leftParity + inputParity) by omega]
    exact LatticeBcGhostTensorStateField.stateField_mem rightParity
      (leftParity + inputParity) right _ rightMember
      (LatticeBcGhostTensorStateField.stateField_mem leftParity inputParity left vector
        leftMember vectorMember offset) (parameter + mode - offset)

theorem stateField_residue_closure (D : LatticeData) (leftParity rightParity : ℕ)
    (left right : State D) (parameter : ℤ)
    (leftMember : left ∈ LatticeBcGhostTensorStateField.homogeneous leftParity)
    (rightMember : right ∈ LatticeBcGhostTensorStateField.homogeneous rightParity) :
    LatticeBcGhostTensorStateField.stateField D (mu D left parameter right) =
      residue (koszul leftParity rightParity) parameter
        (LatticeBcGhostTensorStateField.stateField D left)
        (LatticeBcGhostTensorStateField.stateField D right) := by
  let target := LatticeBcGhostTensorStateField.stateField D (mu D left parameter right)
  let product := residue (koszul leftParity rightParity) parameter
    (LatticeBcGhostTensorStateField.stateField D left)
    (LatticeBcGhostTensorStateField.stateField D right)
  have vacuumLaw := residue_vacuum (koszul leftParity rightParity) parameter
    (LatticeBcGhostTensorStateField.stateField D left)
    (LatticeBcGhostTensorStateField.stateField D right)
    (LatticeBcGhostTensorStateField.vacuum D)
    (LatticeBcGhostTensorStateField.stateField_creativity D left)
    (LatticeBcGhostTensorStateField.stateField_creativity D right)
  have productInitial : (product[[-1]]) (LatticeBcGhostTensorStateField.vacuum D) =
      mu D left parameter right := by
    simpa only [product, mu, LatticeBcGhostTensorStateField.stateField_creation] using vacuumLaw.1
  have vacuumMember : LatticeBcGhostTensorStateField.vacuum D ∈
      LatticeBcGhostTensorStateField.homogeneous 0 := by
    apply LatticeBcGhostTensorStateField.tmul_mem
    exact BcGhostSuperGenerators.single_mem 0 ∅ 1 (by simp [BcGhostSuperGenerators.subsetParity])
  have targetMember : mu D left parameter right ∈
      LatticeBcGhostTensorStateField.homogeneous (leftParity + rightParity) := by
    rw [← productInitial]
    exact stateField_residue_mem D leftParity rightParity 0 left right
      (LatticeBcGhostTensorStateField.vacuum D) parameter (-1)
      leftMember rightMember vacuumMember
  have productCovariant := residue_translation (koszul leftParity rightParity) parameter
    (LatticeBcGhostTensorStateField.translation D)
    (LatticeBcGhostTensorStateField.stateField D left)
    (LatticeBcGhostTensorStateField.stateField D right)
    (LatticeBcGhostTensorStateField.stateField_covariance D left)
    (LatticeBcGhostTensorStateField.stateField_covariance D right)
  have targetCovariant := LatticeBcGhostTensorStateField.stateField_covariance D
    (mu D left parameter right)
  have vanish : product - target = 0 := by
    apply SuperStateFieldReconstruction.relative_vacuum_uniqueness
      (LatticeBcGhostTensorStateField.stateField D)
      (LatticeBcGhostTensorStateField.vacuum D)
      (LatticeBcGhostTensorStateField.translation D)
      LatticeBcGhostTensorStateField.parityPart LatticeBcGhostTensorStateField.homogeneous
      LatticeBcGhostTensorStateField.parity_decomposition
      LatticeBcGhostTensorStateField.parityPart_mem
      (LatticeBcGhostTensorStateField.translation_vacuum D)
      (LatticeBcGhostTensorStateField.stateField_creation D)
      (LatticeBcGhostTensorStateField.stateField_creativity D) (leftParity + rightParity)
    · intro mode nonnegative
      simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, product, vacuumLaw.2 mode nonnegative,
        target, LatticeBcGhostTensorStateField.stateField_creativity D
          (mu D left parameter right) mode nonnegative, sub_self]
    · simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, productInitial,
        target, LatticeBcGhostTensorStateField.stateField_creation, sub_self]
    · intro mode
      simp only [map_sub, Pi.sub_apply, mul_sub, sub_mul, smul_sub]
      calc
        _ = (LatticeBcGhostTensorStateField.translation D * (product[[mode]]) -
          (product[[mode]]) * LatticeBcGhostTensorStateField.translation D) -
          (LatticeBcGhostTensorStateField.translation D * (target[[mode]]) -
          (target[[mode]]) * LatticeBcGhostTensorStateField.translation D) := by abel
        _ = _ := by rw [productCovariant, targetCovariant]
    · intro grade other otherMember
      rw [sub_eq_add_neg, ← neg_one_smul ℂ target]
      apply superLocal_add_left
      · exact SuperStateFieldReconstruction.residue_superLocal leftParity rightParity grade
          _ _ _ parameter
          (homogeneous_superFieldLocal D leftParity grade left other leftMember otherMember)
          (homogeneous_superFieldLocal D rightParity grade right other rightMember otherMember)
          (homogeneous_superFieldLocal D leftParity rightParity left right leftMember rightMember)
      · exact superLocal_smul_left (leftParity + rightParity) grade (-1) _ _
          (homogeneous_superFieldLocal D (leftParity + rightParity) grade
            (mu D left parameter right) other targetMember otherMember)
  exact (sub_eq_zero.mp vanish).symm

theorem borcherds_zero_first (leftParity rightParity : ℕ) (D : LatticeData)
    (parameter last : ℤ) (left right vector : State D)
    (leftMember : left ∈ LatticeBcGhostTensorStateField.homogeneous leftParity)
    (rightMember : right ∈ LatticeBcGhostTensorStateField.homogeneous rightParity) :
    BorcherdsEquation leftParity rightParity D 0 parameter last left right vector := by
  rw [BorcherdsEquation, borcherds_left_zero, borcherds_right_zero,
    stateField_residue_closure D leftParity rightParity left right parameter leftMember rightMember,
    residue_modes]
  rfl

section Borcherds

variable (D : LatticeData)

local notation "Y" => LatticeBcGhostTensorStateField.stateField D

def exchangeEpsilon (exchange : ℂ) (parameter : ℤ) : ℂ := SuperFieldProducts.epsilon parameter * exchange

def jacobiLeftTerm (first last parameter : ℤ) (left right vector : State D) (offset : ℕ) : State D :=
  integerBinomial first offset • mu D (mu D left (parameter + offset) right) (first + last - offset) vector

def jacobiRightFirstTerm (first last parameter : ℤ) (left right vector : State D) (offset : ℕ) : State D :=
  weight parameter offset • mu D left (first + parameter - offset) (mu D right (last + offset) vector)

def jacobiRightSecondTerm (exchange : ℂ) (first last parameter : ℤ)
    (left right vector : State D) (offset : ℕ) : State D :=
  weight parameter offset • (exchangeEpsilon exchange parameter •
    mu D right (last + parameter - offset) (mu D left (first + offset) vector))

theorem firstTerm_finite (first last parameter : ℤ) (left right vector : State D) :
    Function.HasFiniteSupport (jacobiRightFirstTerm D first last parameter left right vector) :=
  (forward_finite (Y left) (Y right) (first + parameter) last vector).smul_right (weight parameter)

theorem secondTerm_finite (exchange : ℂ) (first last parameter : ℤ) (left right vector : State D) :
    Function.HasFiniteSupport (jacobiRightSecondTerm D exchange first last parameter left right vector) :=
  ((forward_finite (Y right) (Y left) (last + parameter) first vector).smul_right
    (fun _ => exchangeEpsilon exchange parameter)).smul_right (weight parameter)

theorem right_split (leftParity rightParity : ℕ) (first last parameter : ℤ)
    (left right vector : State D) :
    borcherdsRight leftParity rightParity D first parameter last left right vector =
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first last parameter left right vector offset) -
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm D (koszul leftParity rightParity)
          first last parameter left right vector offset) := by
  have termEquality (offset : ℕ) :
      borcherdsRightTerm leftParity rightParity D first parameter last left right vector offset =
        jacobiRightFirstTerm D first last parameter left right vector offset -
          jacobiRightSecondTerm D (koszul leftParity rightParity) first last parameter left right vector offset := by
    dsimp [borcherdsRightTerm, jacobiRightFirstTerm, jacobiRightSecondTerm, mu, exchangeEpsilon]
    rw [add_comm parameter last, smul_sub]
  unfold borcherdsRight
  simp_rw [termEquality]
  exact finsum_sub_distrib (firstTerm_finite D first last parameter left right vector)
    (secondTerm_finite D (koszul leftParity rightParity) first last parameter left right vector)

theorem positive_right_products (exchange : ℂ) (leftState rightState : State D)
    (degree : ℕ) (firstMode lastMode : ℤ) (vector : State D) :
    (∑ᶠ offset : ℕ, jacobiRightFirstTerm D firstMode lastMode (degree : ℤ) leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange firstMode lastMode (degree : ℤ)
        leftState rightState vector offset) =
      ((FieldNormalProductLocality.deltaEnd ^ degree) (superCommutator exchange (Y leftState) (Y rightState))) firstMode lastMode vector := by
  have chooseNat (offset : ℕ) : integerBinomial degree offset = (degree.choose offset : ℂ) := by simp [integerBinomial, Ring.choose_natCast]
  have firstSum : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D firstMode lastMode degree leftState rightState vector offset) = ∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ))
    • (((Y leftState) [[firstMode + degree - offset]])) ((((Y rightState) [[lastMode + offset]])) vector) := by
    unfold jacobiRightFirstTerm mu weight; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
    by_contra outside
    have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    exact member (by simp [zeroChoose])
  have secondSum : (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange firstMode lastMode degree leftState rightState vector offset) = exchangeEpsilon exchange degree • ∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) *
    (degree.choose offset : ℂ)) • (((Y rightState) [[lastMode + degree - offset]])) ((((Y leftState) [[firstMode + offset]])) vector) := by
    unfold jacobiRightSecondTerm mu weight; simp_rw [chooseNat]; rw [Finset.smul_sum]; simp_rw [smul_comm (exchangeEpsilon exchange (degree : ℤ))]
    apply finsum_eq_sum_of_support_subset; intro offset member; by_contra outside
    have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    exact member (by simp [zeroChoose])
  have expansion := SuperStateFieldReconstruction.delta_binomial
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
  simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, exchangeEpsilon, SuperFieldProducts.epsilon, zpow_natCast]
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

theorem borcherds (leftParity rightParity : ℕ) (leftState rightState vector : State D)
    (leftHomogeneous : leftState ∈ LatticeBcGhostTensorStateField.homogeneous leftParity)
    (rightHomogeneous : rightState ∈ LatticeBcGhostTensorStateField.homogeneous rightParity) (firstMode lastMode parameter : ℤ) :
    BorcherdsEquation leftParity rightParity D firstMode parameter lastMode leftState rightState vector := by
  classical
  let exchange := koszul leftParity rightParity
  let discrepancy (first second parameter : ℤ) : State D :=
    (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second parameter leftState rightState vector offset) +
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange first second parameter leftState rightState vector offset)
  obtain ⟨cutoff, localityLaw⟩ := homogeneous_superFieldLocal D leftParity rightParity
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
      SuperStateFieldReconstruction.positive_residue_modes, vanished]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  have highSeed : ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter →
      discrepancy first second parameter = 0 := by
    intro first second parameter high
    have stateZero (offset : ℕ) : mu D leftState (parameter + offset) rightState = 0 := by
      have closure := stateField_residue_closure D leftParity rightParity leftState rightState
        (parameter + offset) leftHomogeneous rightHomogeneous
      rw [residueZero (parameter + offset) (by omega)] at closure
      change Y (mu D leftState (parameter + offset) rightState) = 0 at closure
      have created := LatticeBcGhostTensorStateField.stateField_creation D (mu D leftState (parameter + offset) rightState)
      rw [closure] at created
      simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using created.symm
    have leftZero : (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter
        leftState rightState vector offset) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro offset
      rw [jacobiLeftTerm, stateZero]
      simp [mu]
    have rightZero : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second parameter
        leftState rightState vector offset) -
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange first second parameter
          leftState rightState vector offset) = 0 := by
      obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ parameter by omega)
      have vanished := locality_raise exchange (Y leftState) (Y rightState)
        cutoff degree (by omega) localityLaw
      change FieldNormalProductLocality.delta^[degree]
        (superCommutator exchange (Y leftState) (Y rightState)) = 0 at vanished
      rw [delta_iterate_eq_pow] at vanished
      rw [positive_right_products D, vanished]
      rfl
    change (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second parameter leftState rightState vector offset) +
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange first second parameter leftState rightState vector offset) = 0
    rw [leftZero, sub_eq_zero.mp rightZero]
    abel
  have zeroSeed (lastMode parameter : ℤ) : discrepancy 0 lastMode parameter = 0 := by
    have identity := borcherds_zero_first leftParity rightParity D parameter lastMode
      leftState rightState vector leftHomogeneous rightHomogeneous
    rw [BorcherdsEquation, right_split D] at identity
    change (∑ᶠ offset : ℕ, jacobiLeftTerm D 0 lastMode parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm D 0 lastMode parameter leftState rightState vector offset) +
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange 0 lastMode parameter leftState rightState vector offset) = 0
    change (∑ᶠ offset : ℕ, jacobiLeftTerm D 0 lastMode parameter leftState rightState vector offset) =
      (∑ᶠ offset : ℕ, jacobiRightFirstTerm D 0 lastMode parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange 0 lastMode parameter leftState rightState vector offset) at identity
    rw [identity]
    abel
  have recurrence (firstMode lastMode parameter : ℤ) : discrepancy (firstMode + 1) lastMode parameter = discrepancy firstMode (lastMode + 1) parameter + discrepancy firstMode lastMode (parameter + 1) := by
    let weight (parameter : ℤ) (offset : ℕ) := (-1 : ℂ) ^ offset * integerBinomial parameter offset
    let zeroSucc : Option ℕ ≃ ℕ := {
      toFun value := match value with | none => 0 | some offset => offset + 1
      invFun value := match value with | 0 => none | offset + 1 => some offset
      left_inv value := by cases value <;> rfl
      right_inv value := by cases value <;> rfl }
    have splitSum (term : ℕ → State D) (finite : Function.HasFiniteSupport term) : ∑ᶠ offset : ℕ, term offset = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
      rw [← finsum_comp_equiv zeroSucc, finsum_option]
      · rfl
      · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have pascal (parameter : ℤ) (offset : ℕ) : integerBinomial (parameter + 1) (offset + 1) = integerBinomial parameter offset + integerBinomial parameter (offset + 1) := by
      unfold integerBinomial; rw [Ring.choose_succ_succ, Int.cast_add]
    have weightedPascal (parameter : ℤ) (offset : ℕ) : weight (parameter + 1) (offset + 1) = weight parameter (offset + 1) - weight parameter offset := by
      dsimp only [weight]; rw [pascal, pow_succ]; ring
    have chooseZero (parameter : ℤ) : integerBinomial parameter 0 = 1 := by simp [integerBinomial]
    have weightZero (parameter : ℤ) : weight parameter 0 = 1 := by simp [weight, chooseZero]
    have sumPascal (parameter : ℤ) (sequence : ℕ → State D) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, integerBinomial (parameter + 1) offset • sequence offset) =
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
    have sumWeightedPascal (parameter : ℤ) (sequence : ℕ → State D) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, weight (parameter + 1) offset • sequence offset) =
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
        mu D (mu D leftState (parameter + offset) rightState) (start + finish - offset) vector) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y leftState) rightState)).order - parameter).toNat, ?_⟩; intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu D leftState (parameter + offset) rightState = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have secondFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu D leftState (start + parameter - offset) (mu D rightState (finish + offset) vector)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y rightState) vector)).order - finish).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu D rightState (finish + offset) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have thirdFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu D rightState (finish + parameter - offset) (mu D leftState (start + offset) vector)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y leftState) vector)).order - start).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu D leftState (start + offset) vector = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have leftLaw : (∑ᶠ offset : ℕ, jacobiLeftTerm D (firstMode + 1) lastMode parameter leftState rightState vector offset) = (∑ᶠ offset : ℕ, jacobiLeftTerm D firstMode (lastMode + 1) parameter leftState rightState vector offset) + (∑ᶠ offset : ℕ, jacobiLeftTerm D firstMode lastMode (parameter + 1)
      leftState rightState vector offset) := by
      let sequence (offset : ℕ) := mu D (mu D leftState (parameter + offset) rightState) (firstMode + 1 + lastMode - offset) vector
      have initial (offset : ℕ) : jacobiLeftTerm D (firstMode + 1) lastMode parameter leftState rightState vector offset = integerBinomial (firstMode + 1) offset • sequence offset := by rfl
      have current (offset : ℕ) : jacobiLeftTerm D firstMode (lastMode + 1) parameter leftState rightState vector offset = integerBinomial firstMode offset • sequence offset := by
        dsimp only [jacobiLeftTerm, sequence]; rw [show firstMode + (lastMode + 1) - (offset : ℤ) = firstMode + 1 + lastMode - offset by omega]
      have shifted (offset : ℕ) : jacobiLeftTerm D firstMode lastMode (parameter + 1) leftState rightState vector offset = integerBinomial firstMode offset • sequence (offset + 1) := by
        dsimp only [jacobiLeftTerm, sequence]; push_cast
        rw [show parameter + ((offset : ℤ) + 1) = parameter + 1 + offset by omega, show firstMode + 1 + lastMode - ((offset : ℤ) + 1) = firstMode + lastMode - offset by omega]
      simp_rw [initial, current, shifted]; exact sumPascal firstMode sequence (firstFinite (firstMode + 1) lastMode)
    have firstRightLaw : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D (firstMode + 1) lastMode parameter leftState rightState vector offset) = (∑ᶠ offset : ℕ, jacobiRightFirstTerm D firstMode (lastMode + 1) parameter leftState rightState vector offset) + (∑ᶠ offset : ℕ,
      jacobiRightFirstTerm D firstMode lastMode (parameter + 1) leftState rightState vector offset) := by
      let sequence (offset : ℕ) := mu D leftState (firstMode + (parameter + 1) - offset) (mu D rightState (lastMode + offset) vector)
      have initial (offset : ℕ) : jacobiRightFirstTerm D (firstMode + 1) lastMode parameter leftState rightState vector offset = weight parameter offset • sequence offset := by
        dsimp only [jacobiRightFirstTerm, weight, SuperFieldProducts.weight, sequence]; rw [show firstMode + 1 + parameter = firstMode + (parameter + 1) by omega]
      have current (offset : ℕ) : jacobiRightFirstTerm D firstMode lastMode (parameter + 1) leftState rightState vector offset = weight (parameter + 1) offset • sequence offset := by rfl
      have shifted (offset : ℕ) : jacobiRightFirstTerm D firstMode (lastMode + 1) parameter leftState rightState vector offset = weight parameter offset • sequence (offset + 1) := by
        dsimp only [jacobiRightFirstTerm, weight, SuperFieldProducts.weight, sequence]; push_cast
        rw [show firstMode + (parameter + 1) - ((offset : ℤ) + 1) = firstMode + parameter - offset by omega, show lastMode + ((offset : ℤ) + 1) = lastMode + 1 + offset by omega]
      simp_rw [initial, current, shifted]; exact sub_eq_iff_eq_add'.mp (sumWeightedPascal parameter sequence (secondFinite firstMode lastMode (parameter + 1))).symm
    have sign : exchangeEpsilon exchange (parameter + 1) =
        -exchangeEpsilon exchange parameter := by
      have epsilonStep : SuperFieldProducts.epsilon (parameter + 1) = -SuperFieldProducts.epsilon parameter := by
        rw [SuperFieldProducts.epsilon, SuperFieldProducts.epsilon, zpow_add₀ (by norm_num)]
        norm_num
      rw [exchangeEpsilon, exchangeEpsilon, epsilonStep, neg_mul]
    have secondRightLaw : (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange (firstMode + 1) lastMode parameter leftState rightState vector offset) = (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange firstMode (lastMode + 1) parameter leftState rightState vector offset) + (∑ᶠ offset : ℕ,
      jacobiRightSecondTerm D exchange firstMode lastMode (parameter + 1) leftState rightState vector offset) := by
      let sequence (offset : ℕ) := mu D rightState (lastMode + (parameter + 1) - offset) (mu D leftState (firstMode + offset) vector)
      have initial (offset : ℕ) : jacobiRightSecondTerm D exchange firstMode (lastMode + 1) parameter leftState rightState vector offset = exchangeEpsilon exchange parameter • (weight parameter offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, SuperFieldProducts.weight, sequence]; rw [show lastMode + 1 + parameter = lastMode + (parameter + 1) by omega, smul_comm]
      have current (offset : ℕ) : jacobiRightSecondTerm D exchange firstMode lastMode (parameter + 1) leftState rightState vector offset = -exchangeEpsilon exchange parameter • (weight (parameter + 1) offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, SuperFieldProducts.weight, sequence]; rw [sign, smul_comm]
      have shifted (offset : ℕ) : jacobiRightSecondTerm D exchange (firstMode + 1) lastMode parameter leftState rightState vector offset = exchangeEpsilon exchange parameter • (weight parameter offset • sequence (offset + 1)) := by
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
  rw [BorcherdsEquation, right_split D]
  have law := allIndices firstMode lastMode parameter
  change (∑ᶠ offset : ℕ, jacobiLeftTerm D firstMode lastMode parameter leftState rightState vector offset) =
    (∑ᶠ offset : ℕ, jacobiRightFirstTerm D firstMode lastMode parameter leftState rightState vector offset) -
      (∑ᶠ offset : ℕ, jacobiRightSecondTerm D exchange firstMode lastMode parameter leftState rightState vector offset)
  apply sub_eq_zero.mp
  calc
    _ = discrepancy firstMode lastMode parameter := by dsimp [discrepancy]; abel
    _ = 0 := law

end Borcherds

theorem mixed_borcherds (D : LatticeData) (first parameter last : ℤ)
    (left right vector : State D) :
    borcherdsLeft D first parameter last left right vector =
      (borcherdsRight 0 0 D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 0 left)
          (LatticeBcGhostTensorStateField.parityPart 0 right) vector +
        borcherdsRight 0 1 D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 0 left)
          (LatticeBcGhostTensorStateField.parityPart 1 right) vector) +
      (borcherdsRight 1 0 D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 1 left)
          (LatticeBcGhostTensorStateField.parityPart 0 right) vector +
        borcherdsRight 1 1 D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 1 left)
          (LatticeBcGhostTensorStateField.parityPart 1 right) vector) := by
  have addLeft (firstState secondState right vector : State D) :
      borcherdsLeft D first parameter last (firstState + secondState) right vector =
        borcherdsLeft D first parameter last firstState right vector +
          borcherdsLeft D first parameter last secondState right vector := by
    have terms (offset : ℕ) :
        borcherdsLeftTerm D first parameter last (firstState + secondState) right vector offset =
          borcherdsLeftTerm D first parameter last firstState right vector offset +
            borcherdsLeftTerm D first parameter last secondState right vector offset := by
      simp only [borcherdsLeftTerm, mu, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    unfold borcherdsLeft
    simp_rw [terms]
    exact finsum_add_distrib (borcherds_left_finite D first parameter last firstState right vector)
      (borcherds_left_finite D first parameter last secondState right vector)
  have addRight (left firstState secondState vector : State D) :
      borcherdsLeft D first parameter last left (firstState + secondState) vector =
        borcherdsLeft D first parameter last left firstState vector +
          borcherdsLeft D first parameter last left secondState vector := by
    have terms (offset : ℕ) :
        borcherdsLeftTerm D first parameter last left (firstState + secondState) vector offset =
          borcherdsLeftTerm D first parameter last left firstState vector offset +
            borcherdsLeftTerm D first parameter last left secondState vector offset := by
      simp only [borcherdsLeftTerm, mu, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    unfold borcherdsLeft
    simp_rw [terms]
    exact finsum_add_distrib (borcherds_left_finite D first parameter last left firstState vector)
      (borcherds_left_finite D first parameter last left secondState vector)
  have expansion : borcherdsLeft D first parameter last left right vector =
      (borcherdsLeft D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 0 left)
          (LatticeBcGhostTensorStateField.parityPart 0 right) vector +
        borcherdsLeft D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 0 left)
          (LatticeBcGhostTensorStateField.parityPart 1 right) vector) +
      (borcherdsLeft D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 1 left)
          (LatticeBcGhostTensorStateField.parityPart 0 right) vector +
        borcherdsLeft D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 1 left)
          (LatticeBcGhostTensorStateField.parityPart 1 right) vector) := by
    calc
      _ = borcherdsLeft D first parameter last
          (LatticeBcGhostTensorStateField.parityPart 0 left +
            LatticeBcGhostTensorStateField.parityPart 1 left)
          (LatticeBcGhostTensorStateField.parityPart 0 right +
            LatticeBcGhostTensorStateField.parityPart 1 right) vector := by
        rw [LatticeBcGhostTensorStateField.parity_decomposition,
          LatticeBcGhostTensorStateField.parity_decomposition]
      _ = _ := by rw [addLeft, addRight, addRight]
  rw [expansion]
  rw [borcherds D 0 0 _ _ vector
      (LatticeBcGhostTensorStateField.parityPart_mem 0 left)
      (LatticeBcGhostTensorStateField.parityPart_mem 0 right) first last parameter,
    borcherds D 0 1 _ _ vector
      (LatticeBcGhostTensorStateField.parityPart_mem 0 left)
      (LatticeBcGhostTensorStateField.parityPart_mem 1 right) first last parameter,
    borcherds D 1 0 _ _ vector
      (LatticeBcGhostTensorStateField.parityPart_mem 1 left)
      (LatticeBcGhostTensorStateField.parityPart_mem 0 right) first last parameter,
    borcherds D 1 1 _ _ vector
      (LatticeBcGhostTensorStateField.parityPart_mem 1 left)
      (LatticeBcGhostTensorStateField.parityPart_mem 1 right) first last parameter]

end D5.S3.VertexAlgebra.LatticeBcGhostTensorJacobi

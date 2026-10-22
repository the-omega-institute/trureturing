/- GID: D5/S3/VertexAlgebra/BcGhostSuperBorcherdsTerms
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostSuperBorcherdsTerms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-support coefficient Borcherds summands with arbitrary integer first, parameter and last indices on the original Y-mode products. Homogeneous and four-component mixed equation predicates are definitions, not an extra theorem or a completed formal-delta assembly. -/

import D5.S3.VertexAlgebra.BcGhostSuperResidues

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperBorcherdsTerms

open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField
open BcGhostSuperReconstruction BcGhostSuperResidues SuperFieldProducts
open scoped VertexOperator

noncomputable section

def borcherdsLeftTerm (first parameter last : ℤ) (left right vector : Carrier) (offset : ℕ) : Carrier :=
  integerBinomial first offset •
    ((Y (((Y left)[[parameter + offset]]) right))[[first + last - offset]]) vector

def borcherdsRightTerm (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : Carrier) (offset : ℕ) : Carrier :=
  weight parameter offset •
    (((Y left)[[first + parameter - offset]]) (((Y right)[[last + offset]]) vector) -
      (epsilon parameter * koszul leftParity rightParity) •
        ((Y right)[[parameter + last - offset]]) (((Y left)[[first + offset]]) vector))

theorem borcherds_left_finite (first parameter last : ℤ) (left right vector : Carrier) :
    Function.HasFiniteSupport (borcherdsLeftTerm first parameter last left right vector) := by
  refine (increasing_finite (Y left) parameter right).subset ?_
  intro offset member vanish
  apply member
  change ((Y left)[[parameter + offset]]) right = 0 at vanish
  simp only [borcherdsLeftTerm, vanish, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]

theorem borcherds_right_finite (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : Carrier) :
    Function.HasFiniteSupport (borcherdsRightTerm leftParity rightParity first parameter last
      left right vector) :=
  ((forward_finite (Y left) (Y right) (first + parameter) last vector).sub
    ((forward_finite (Y right) (Y left) (parameter + last) first vector).smul_right
      (fun _ => epsilon parameter * koszul leftParity rightParity))).smul_right (weight parameter)

def borcherdsLeft (first parameter last : ℤ) (left right vector : Carrier) : Carrier :=
  ∑ᶠ offset : ℕ, borcherdsLeftTerm first parameter last left right vector offset

def borcherdsRight (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : Carrier) : Carrier :=
  ∑ᶠ offset : ℕ, borcherdsRightTerm leftParity rightParity first parameter last left right vector offset

def BorcherdsEquation (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : Carrier) : Prop :=
  borcherdsLeft first parameter last left right vector =
    borcherdsRight leftParity rightParity first parameter last left right vector

theorem borcherds_left_zero (parameter last : ℤ) (left right vector : Carrier) :
    borcherdsLeft 0 parameter last left right vector =
      ((Y (((Y left)[[parameter]]) right))[[last]]) vector := by
  unfold borcherdsLeft
  rw [finsum_eq_single _ 0]
  · simp [borcherdsLeftTerm, integerBinomial]
  · intro offset distinct
    have positive : 0 < offset := Nat.pos_of_ne_zero distinct
    simp [borcherdsLeftTerm, integerBinomial, Ring.choose_zero_pos ℤ positive]

theorem borcherds_right_zero (leftParity rightParity : ℕ) (parameter last : ℤ)
    (left right vector : Carrier) :
    borcherdsRight leftParity rightParity 0 parameter last left right vector =
      residueLeft parameter last (Y left) (Y right) vector -
        (epsilon parameter * koszul leftParity rightParity) •
          residueRight parameter last (Y left) (Y right) vector := by
  unfold borcherdsRight
  have termEquality (offset : ℕ) :
      borcherdsRightTerm leftParity rightParity 0 parameter last left right vector offset =
        weight parameter offset • ((Y left)[[parameter - offset]]) (((Y right)[[last + offset]]) vector) -
          (epsilon parameter * koszul leftParity rightParity) •
            (weight parameter offset • ((Y right)[[parameter + last - offset]]) (((Y left)[[offset]]) vector)) := by
    dsimp [borcherdsRightTerm]
    rw [zero_add, zero_add, smul_sub, smul_comm]
  simp_rw [termEquality]
  have reverseFinite := (residue_right_finite parameter last (Y left) (Y right) vector).smul_right
    (fun _ => epsilon parameter * koszul leftParity rightParity)
  simp only [Pi.smul_def'] at reverseFinite
  rw [finsum_sub_distrib (residue_left_finite parameter last (Y left) (Y right) vector)
    reverseFinite,
    ← smul_finsum' (epsilon parameter * koszul leftParity rightParity)
      (residue_right_finite parameter last (Y left) (Y right) vector)]
  rfl

theorem borcherds_zero_first (leftParity rightParity : ℕ) (parameter last : ℤ)
    (left right vector : Carrier) (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    BorcherdsEquation leftParity rightParity 0 parameter last left right vector := by
  rw [BorcherdsEquation, borcherds_left_zero, borcherds_right_zero]
  exact stateField_iterate leftParity rightParity left right vector parameter last
    leftHomogeneous rightHomogeneous

def mixedBorcherdsRight (first parameter last : ℤ) (left right vector : Carrier) : Carrier :=
  ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
    borcherdsRight leftParity rightParity first parameter last
      (parityPart leftParity left) (parityPart rightParity right) vector

def MixedBorcherdsEquation (first parameter last : ℤ) (left right vector : Carrier) : Prop :=
  borcherdsLeft first parameter last left right vector =
    mixedBorcherdsRight first parameter last left right vector



theorem borcherdsLeft_add_left (first parameter last : ℤ) (firstState secondState right vector : Carrier) :
    borcherdsLeft first parameter last (firstState + secondState) right vector =
      borcherdsLeft first parameter last firstState right vector +
        borcherdsLeft first parameter last secondState right vector := by
  have terms (offset : ℕ) :
      borcherdsLeftTerm first parameter last (firstState + secondState) right vector offset =
        borcherdsLeftTerm first parameter last firstState right vector offset +
          borcherdsLeftTerm first parameter last secondState right vector offset := by
    simp only [borcherdsLeftTerm, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  unfold borcherdsLeft
  simp_rw [terms]
  exact finsum_add_distrib (borcherds_left_finite first parameter last firstState right vector)
    (borcherds_left_finite first parameter last secondState right vector)

theorem borcherdsLeft_add_right (first parameter last : ℤ) (left firstState secondState vector : Carrier) :
    borcherdsLeft first parameter last left (firstState + secondState) vector =
      borcherdsLeft first parameter last left firstState vector +
        borcherdsLeft first parameter last left secondState vector := by
  have terms (offset : ℕ) :
      borcherdsLeftTerm first parameter last left (firstState + secondState) vector offset =
        borcherdsLeftTerm first parameter last left firstState vector offset +
          borcherdsLeftTerm first parameter last left secondState vector offset := by
    simp only [borcherdsLeftTerm, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  unfold borcherdsLeft
  simp_rw [terms]
  exact finsum_add_distrib (borcherds_left_finite first parameter last left firstState vector)
    (borcherds_left_finite first parameter last left secondState vector)

end
end D5.S3.VertexAlgebra.BcGhostSuperBorcherdsTerms

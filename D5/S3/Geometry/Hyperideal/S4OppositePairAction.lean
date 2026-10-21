/- GID: D5/S3/Geometry/Hyperideal/S4OppositePairAction
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/S4OppositePairAction
   mirror-E: none(waiver:finite-s4-opposite-pair-action)
   anchors: []
   utility: none
   digest: The S4 action on three opposite edge pairs has six actions and four named trivial permutations. -/

/-
proof_shape: opposite_pair_action_image_card, trivial_pair_action_iff,
  transposition_generates_pair_swap, and three_cycle_generates_pair_cycle: content
admission_basis: escape-witness.
escape_witness: these declarations compute the induced action of all finite
permutations of four vertices on the three opposite edge pairs; the exact image
cardinality and kernel are not instances of a frozen theorem.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19015
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Geometry.Hyperideal.S4OppositePairAction

abbrev Vertex := Fin 4
abbrev Pair := Fin 3
abbrev Perm4 := Equiv.Perm Vertex

instance : DecidableEq Perm4 := fun σ τ =>
  decidable_of_iff (∀ x, σ x = τ x) (by
    constructor
    · intro h
      exact Equiv.Perm.ext h
    · intro h x
      rw [h])

/- The six edge slots are 01, 02, 03, 23, 13, 12. -/
def edgeIndex : Vertex → Vertex → Fin 6 :=
  ![![0, 0, 1, 2],
    ![0, 0, 5, 4],
    ![1, 5, 0, 3],
    ![2, 4, 3, 0]]

def oppositePair : Fin 6 → Pair := ![0, 1, 2, 0, 1, 2]

def pairFirst : Pair → Vertex := ![0, 0, 0]
def pairSecond : Pair → Vertex := ![1, 2, 3]

def inducedPairAction (σ : Perm4) : Pair → Pair := fun p =>
  oppositePair (edgeIndex (σ (pairFirst p)) (σ (pairSecond p)))

def isTrivialPairAction (σ : Perm4) : Prop :=
  ∀ p, inducedPairAction σ p = p

def doubleSwap01_23 : Perm4 where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide
  right_inv := by decide

def doubleSwap02_13 : Perm4 where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

def doubleSwap03_12 : Perm4 where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide
  right_inv := by decide

def transposition01 : Perm4 where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide
  right_inv := by decide

def threeCycle012 : Perm4 where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide
  right_inv := by decide

set_option maxHeartbeats 4000000 in
theorem induced_pair_action_bijective (σ : Perm4) :
    Function.Bijective (inducedPairAction σ) := by
  revert σ
  decide

set_option maxHeartbeats 4000000 in
theorem opposite_pair_action_image_card :
    (Finset.univ.image inducedPairAction).card = 6 := by
  decide

theorem four_named_kernel_elements :
    isTrivialPairAction (1 : Perm4) ∧
      isTrivialPairAction doubleSwap01_23 ∧
      isTrivialPairAction doubleSwap02_13 ∧
      isTrivialPairAction doubleSwap03_12 ∧
      (1 : Perm4) ≠ doubleSwap01_23 ∧
      (1 : Perm4) ≠ doubleSwap02_13 ∧
      doubleSwap01_23 ≠ doubleSwap02_13 ∧
      doubleSwap01_23 ≠ doubleSwap03_12 ∧
      doubleSwap02_13 ≠ doubleSwap03_12 := by
  constructor
  · intro p
    fin_cases p <;> decide
  constructor
  · intro p
    fin_cases p <;> decide
  constructor
  · intro p
    fin_cases p <;> decide
  constructor
  · intro p
    fin_cases p <;> decide
  constructor
  · intro h
    have h0 := congrArg (fun σ : Perm4 => σ 0) h
    norm_num [doubleSwap01_23, doubleSwap02_13, doubleSwap03_12] at h0
  constructor
  · intro h
    have h0 := congrArg (fun σ : Perm4 => σ 0) h
    norm_num [doubleSwap01_23, doubleSwap02_13, doubleSwap03_12] at h0
  constructor
  · intro h
    have h0 := congrArg (fun σ : Perm4 => σ 0) h
    norm_num [doubleSwap01_23, doubleSwap02_13, doubleSwap03_12] at h0
  constructor
  · intro h
    have h0 := congrArg (fun σ : Perm4 => σ 0) h
    norm_num [doubleSwap01_23, doubleSwap02_13, doubleSwap03_12] at h0
  · intro h
    have h0 := congrArg (fun σ : Perm4 => σ 0) h
    norm_num [doubleSwap01_23, doubleSwap02_13, doubleSwap03_12] at h0

theorem transposition_generates_pair_swap :
    inducedPairAction transposition01 = ![0, 2, 1] := by
  decide

theorem three_cycle_generates_pair_cycle :
    inducedPairAction threeCycle012 = ![2, 0, 1] := by
  decide

end D5.S3.Geometry.Hyperideal.S4OppositePairAction

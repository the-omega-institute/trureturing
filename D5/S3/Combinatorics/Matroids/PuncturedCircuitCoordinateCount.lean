/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinateCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitCoordinateCount
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Coordinate counts after omitting one paired subset. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitCoordinateCount
public import Mathlib.Logic.Equiv.Sum

/-! The subsets containing exactly one of two elements are paired by their common deletion. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinateCount

open Finset
open UniformCircuitCoordinateCount (removeSpecifiedEquiv card_include_nonpivot card_avoid_both)
set_option autoImplicit false

variable {I : Type*}

/-- The common deletion indexing a pair of subsets. -/
abbrev PairIndex (x z w : I) (r : ℕ) :=
  {J : Set.powersetCard I r // x ∉ J ∧ z ∉ J ∧ w ∉ J}

/-- Subsets excluding the pivot and containing both specified elements. -/
abbrev BothIndex (x z w : I) (r : ℕ) :=
  {F : Set.powersetCard I r // x ∉ F ∧ z ∈ F ∧ w ∈ F}

/-- Subsets excluding the pivot and both specified elements. -/
abbrev NeitherIndex (x z w : I) (r : ℕ) :=
  PairIndex x z w r

variable [DecidableEq I]

/-- Insert the first specified element into a common deletion. -/
def insertFirstEquiv (x z w : I) (hxz : x ≠ z) (hzw : z ≠ w) (r : ℕ) :
    PairIndex x z w r ≃ {F : Set.powersetCard I (r + 1) // x ∉ F ∧ z ∈ F ∧ w ∉ F} where
  toFun J :=
    let F := (removeSpecifiedEquiv x z hxz r).symm ⟨J.val, J.prop.1, J.prop.2.1⟩
    ⟨F.val, F.prop.1, F.prop.2, fun h => (mem_insert.mp h).elim hzw.symm J.prop.2.2⟩
  invFun F :=
    let J := removeSpecifiedEquiv x z hxz r ⟨F.val, F.prop.1, F.prop.2.1⟩
    ⟨J.val, J.prop.1, J.prop.2, fun h => F.prop.2.2 (mem_of_mem_erase h)⟩
  left_inv J := Subtype.ext (Subtype.ext (erase_insert J.prop.2.1))
  right_inv F := Subtype.ext (Subtype.ext (insert_erase F.prop.2.1))

/-- Insert the second specified element into a common deletion. -/
def insertSecondEquiv (x z w : I) (hxw : x ≠ w) (hzw : z ≠ w) (r : ℕ) :
    PairIndex x z w r ≃ {F : Set.powersetCard I (r + 1) // x ∉ F ∧ z ∉ F ∧ w ∈ F} :=
  (Equiv.subtypeEquivRight (fun _ => and_congr_right' and_comm)).trans
    ((insertFirstEquiv x w z hxw hzw.symm r).trans
      (Equiv.subtypeEquivRight (fun _ => and_congr_right' and_comm)))

/-- A subset containing the first specified element either contains both or is the first
member of a pair. -/
noncomputable def includeFirstEquiv (x z w : I) (hxz : x ≠ z) (hzw : z ≠ w) (r : ℕ) :
    BothIndex x z w (r + 1) ⊕ PairIndex x z w r ≃
      {F : Set.powersetCard I (r + 1) // x ∉ F ∧ z ∈ F} := by
  classical
  let present := fun F : Set.powersetCard I (r + 1) => x ∉ F ∧ z ∈ F
  let both := (Equiv.subtypeEquivRight fun _ => and_assoc.symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter present (fun F => w ∈ F)).symm
  let firstOnly := (Equiv.subtypeEquivRight fun _ => and_assoc.symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter present (fun F => w ∉ F)).symm
  exact (Equiv.sumCongr both ((insertFirstEquiv x z w hxz hzw r).trans firstOnly)).trans
    (Equiv.sumCompl fun F : Subtype present => w ∈ F.val)

/-- A subset excluding the first specified element either excludes both or is the second
member of a pair. -/
noncomputable def excludeFirstEquiv (x z w : I) (hxw : x ≠ w) (hzw : z ≠ w) (r : ℕ) :
    NeitherIndex x z w (r + 1) ⊕ PairIndex x z w r ≃
      {F : Set.powersetCard I (r + 1) // x ∉ F ∧ z ∉ F} := by
  classical
  let absent := fun F : Set.powersetCard I (r + 1) => x ∉ F ∧ z ∉ F
  let neither := (Equiv.subtypeEquivRight fun _ => and_assoc.symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter absent (fun F => w ∉ F)).symm
  let secondOnly := (Equiv.subtypeEquivRight
      (fun _ => and_assoc.symm.trans (and_congr_right' not_not.symm))).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter absent (fun F => ¬w ∉ F)).symm
  exact (Equiv.sumCongr neither ((insertSecondEquiv x z w hxw hzw r).trans secondOnly)).trans
    (Equiv.sumCompl fun F : Subtype absent => w ∉ F.val)

omit [DecidableEq I] in
/-- Omitting a common deletion reduces each of the two uniform coordinate counts by one. -/
theorem card_after_omitting_pair [Fintype I] (x z w : I) (hxz : x ≠ z) (hxw : x ≠ w)
    (hzw : z ≠ w) (r : ℕ) (exception : PairIndex x z w r) :
    Nat.card (BothIndex x z w (r + 1) ⊕ {J : PairIndex x z w r // J ≠ exception}) =
        (Fintype.card I - 2).choose r - 1 ∧
      Nat.card (NeitherIndex x z w (r + 1) ⊕ {J : PairIndex x z w r // J ≠ exception}) =
        (Fintype.card I - 2).choose (r + 1) - 1 := by
  classical
  have one : Nat.card {J : PairIndex x z w r // J = exception} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨exception, rfl⟩, fun J => Subtype.ext J.prop⟩
  have exception_count :
      1 + Nat.card {J : PairIndex x z w r // J ≠ exception} = Nat.card (PairIndex x z w r) := by
    rw [← one, ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (· = exception))
  constructor
  · rw [← card_include_nonpivot x z hxz r,
      ← Nat.card_congr (includeFirstEquiv x z w hxz hzw r), Nat.card_sum, Nat.card_sum]
    omega
  · rw [← card_avoid_both x z hxz (r + 1),
      ← Nat.card_congr (excludeFirstEquiv x z w hxw hzw r), Nat.card_sum, Nat.card_sum]
    omega

end D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinateCount

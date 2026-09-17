/- GID: D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: A nine-vertex counterexample to weighted bond poset real-rootedness. -/

import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation

open Finset

noncomputable section

/- The total weight function is zero-normalized away from the actual blocks.
   On an actual block its bound is exactly the paper's `weight < |block|`. -/
private structure WeightedPartition (V : Type*) [Fintype V] [DecidableEq V] where
  partition : Finpartition (univ : Finset V)
  weight : Finset V -> Fin (Fintype.card V + 1)
  weight_lt_card : ∀ block ∈ partition.parts, (weight block : Nat) < block.card
  weight_eq_zero : ∀ block ∉ partition.parts, weight block = 0

private instance weightedPartitionDecidableEq
    (V : Type*) [Fintype V] [DecidableEq V] : DecidableEq (WeightedPartition V) :=
  Classical.decEq _

private instance weightedPartitionFintype
    (V : Type*) [Fintype V] [DecidableEq V] : Fintype (WeightedPartition V) := by
  classical
  refine Fintype.ofInjective (fun P => (P.partition, P.weight)) ?_
  rintro ⟨P, weightP, boundP, zeroP⟩ ⟨Q, weightQ, boundQ, zeroQ⟩ h
  change (P, weightP) = (Q, weightQ) at h
  cases h
  rfl

/- The lower blocks contained in one specified upper block. -/
private def children {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (univ : Finset V)) (upper : Finset V) : Finset P.parts :=
  P.parts.attach.filter fun lower => lower.val ⊆ upper

@[simp] private theorem mem_children_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finpartition (univ : Finset V)} {upper : Finset V} {lower : P.parts} :
    lower ∈ children P upper ↔ lower.val ⊆ upper := by
  simp [children]

private theorem children_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (univ : Finset V)) (upper : P.parts) :
    children P upper.val = {upper} := by
  ext lower
  simp only [mem_children_iff, mem_singleton]
  constructor
  · intro hle
    apply Subtype.ext
    exact P.disjoint.eq_of_le lower.property upper.property
      (P.ne_bot lower.property) hle
  · rintro rfl
    exact Subset.rfl

/- Refinement gives every lower block a unique containing upper block. -/
private noncomputable def parentBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hPQ : P ≤ Q)
    (lower : P.parts) : Q.parts :=
  ⟨(hPQ lower.property).choose, (hPQ lower.property).choose_spec.1⟩

private theorem lower_subset_parentBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hPQ : P ≤ Q)
    (lower : P.parts) : lower.val ⊆ (parentBlock hPQ lower).val :=
  (hPQ lower.property).choose_spec.2

private theorem parentBlock_eq_of_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hPQ : P ≤ Q)
    (lower : P.parts) (upper : Q.parts) (hsub : lower.val ⊆ upper.val) :
    parentBlock hPQ lower = upper := by
  apply Subtype.ext
  by_contra hne
  have hdisjoint := Q.disjoint (parentBlock hPQ lower).property upper.property hne
  obtain ⟨vertex, hvertex⟩ := nonempty_iff_ne_empty.mpr (P.ne_bot lower.property)
  exact Finset.disjoint_left.mp hdisjoint
    (lower_subset_parentBlock hPQ lower hvertex) (hsub hvertex)

private theorem parentBlock_eq_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hPQ : P ≤ Q)
    (lower : P.parts) (upper : Q.parts) :
    parentBlock hPQ lower = upper ↔ lower.val ⊆ upper.val := by
  constructor
  · rintro rfl
    exact lower_subset_parentBlock hPQ lower
  · exact parentBlock_eq_of_subset hPQ lower upper

private theorem parentBlock_trans
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q R : Finpartition (univ : Finset V)}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (lower : P.parts) :
    parentBlock hQR (parentBlock hPQ lower) = parentBlock (hPQ.trans hQR) lower := by
  apply Subtype.ext
  by_contra hne
  have hdisjoint := R.disjoint
    (parentBlock hQR (parentBlock hPQ lower)).property
    (parentBlock (hPQ.trans hQR) lower).property hne
  obtain ⟨vertex, hvertex⟩ := nonempty_iff_ne_empty.mpr (P.ne_bot lower.property)
  exact Finset.disjoint_left.mp hdisjoint
    (lower_subset_parentBlock hQR (parentBlock hPQ lower)
      (lower_subset_parentBlock hPQ lower hvertex))
    (lower_subset_parentBlock (hPQ.trans hQR) lower hvertex)

private theorem parentBlock_mem_children
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q R : Finpartition (univ : Finset V)}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (upper : R.parts)
    {lower : P.parts} (hlower : lower ∈ children P upper.val) :
    parentBlock hPQ lower ∈ children Q upper.val := by
  rw [mem_children_iff]
  have hparent : parentBlock (hPQ.trans hQR) lower = upper :=
    parentBlock_eq_of_subset (hPQ.trans hQR) lower upper
      (mem_children_iff.mp hlower)
  rw [← hparent, ← parentBlock_trans hPQ hQR lower]
  exact lower_subset_parentBlock hQR (parentBlock hPQ lower)

private theorem children_parent_fiber
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q R : Finpartition (univ : Finset V)}
    (hPQ : P ≤ Q) (upper : R.parts) {middle : Q.parts}
    (hmiddle : middle ∈ children Q upper.val) :
    (children P upper.val).filter (fun lower => parentBlock hPQ lower = middle) =
      children P middle.val := by
  ext lower
  simp only [mem_filter, mem_children_iff]
  rw [parentBlock_eq_iff]
  constructor
  · exact And.right
  · intro hsub
    exact ⟨hsub.trans (mem_children_iff.mp hmiddle), hsub⟩

private def childWeightSum {V : Type*} [Fintype V] [DecidableEq V]
    (P : WeightedPartition V) (upper : Finset V) : Nat :=
  ∑ lower ∈ children P.partition upper, (P.weight lower.val : Nat)

private theorem childWeightSum_decompose
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : WeightedPartition V) (R : Finpartition (univ : Finset V))
    (hPQ : P.partition ≤ Q.partition) (hQR : Q.partition ≤ R)
    (upper : R.parts) :
    childWeightSum P upper.val =
      ∑ middle ∈ children Q.partition upper.val,
        childWeightSum P middle.val := by
  classical
  let lowerChildren := children P.partition upper.val
  let middleChildren := children Q.partition upper.val
  have hmaps : Set.MapsTo (parentBlock hPQ)
      (lowerChildren : Set P.partition.parts)
      (middleChildren : Set Q.partition.parts) :=
    fun lower hlower => parentBlock_mem_children hPQ hQR upper hlower
  symm
  calc
    ∑ middle ∈ middleChildren, childWeightSum P middle.val =
        ∑ middle ∈ middleChildren,
          ∑ lower ∈ lowerChildren with parentBlock hPQ lower = middle,
            (P.weight lower.val : Nat) := by
      apply Finset.sum_congr rfl
      intro middle hmiddle
      rw [children_parent_fiber hPQ upper hmiddle]
      rfl
    _ = ∑ lower ∈ lowerChildren, (P.weight lower.val : Nat) :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = childWeightSum P upper.val := rfl

private theorem children_card_decompose
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q R : Finpartition (univ : Finset V)}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (upper : R.parts) :
    (children P upper.val).card =
      ∑ middle ∈ children Q upper.val, (children P middle.val).card := by
  classical
  let lowerChildren := children P upper.val
  let middleChildren := children Q upper.val
  have hmaps : Set.MapsTo (parentBlock hPQ)
      (lowerChildren : Set P.parts) (middleChildren : Set Q.parts) :=
    fun lower hlower => parentBlock_mem_children hPQ hQR upper hlower
  calc
    lowerChildren.card =
        ∑ middle ∈ middleChildren,
          (lowerChildren.filter (fun lower => parentBlock hPQ lower = middle)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ middle ∈ middleChildren, (children P middle.val).card := by
      apply Finset.sum_congr rfl
      intro middle hmiddle
      rw [children_parent_fiber hPQ upper hmiddle]

/- This is the literal weighted refinement rule: an upper block formed from
   `l` lower blocks receives their total weight plus some `d < l`. -/
private def WeightedRefines {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : WeightedPartition V) : Prop :=
  P.partition ≤ Q.partition ∧
    ∀ upper : Q.partition.parts,
      ∃ d : Nat, d < (children P.partition upper.val).card ∧
        (Q.weight upper.val : Nat) = childWeightSum P upper.val + d

private theorem weightedRefines_refl
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : WeightedPartition V) : WeightedRefines P P := by
  refine ⟨le_rfl, fun upper => ⟨0, ?_, ?_⟩⟩
  · simp [children_self]
  · simp [childWeightSum, children_self]

private theorem weightedPartition_ext
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : WeightedPartition V} (hpartition : P.partition = Q.partition)
    (hweight : P.weight = Q.weight) : P = Q := by
  rcases P with ⟨P, weightP, boundP, zeroP⟩
  rcases Q with ⟨Q, weightQ, boundQ, zeroQ⟩
  simp only at hpartition hweight
  cases hpartition
  cases hweight
  rfl

private theorem weightedRefines_antisymm
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : WeightedPartition V}
    (hPQ : WeightedRefines P Q) (hQP : WeightedRefines Q P) : P = Q := by
  have hpartition : P.partition = Q.partition := le_antisymm hPQ.1 hQP.1
  apply weightedPartition_ext hpartition
  funext block
  by_cases hblock : block ∈ P.partition.parts
  · have hblockQ : block ∈ Q.partition.parts := hpartition ▸ hblock
    rcases hPQ.2 ⟨block, hblockQ⟩ with ⟨d, hd, heq⟩
    have hchildren : children P.partition block = {⟨block, hblock⟩} :=
      children_self P.partition ⟨block, hblock⟩
    have hd0 : d = 0 := by
      rw [hchildren, Finset.card_singleton] at hd
      omega
    apply Fin.ext
    symm
    rw [childWeightSum, hchildren] at heq
    simpa [hd0] using heq
  · have hblockQ : block ∉ Q.partition.parts := by simpa [hpartition] using hblock
    rw [P.weight_eq_zero block hblock, Q.weight_eq_zero block hblockQ]

private theorem weightedRefines_trans
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q R : WeightedPartition V}
    (hPQ : WeightedRefines P Q) (hQR : WeightedRefines Q R) :
    WeightedRefines P R := by
  refine ⟨hPQ.1.trans hQR.1, ?_⟩
  intro upper
  choose delta hdelta hweight using hPQ.2
  rcases hQR.2 upper with ⟨outerDelta, houterDelta, houterWeight⟩
  let middleChildren := children Q.partition upper.val
  let totalDelta := (∑ middle ∈ middleChildren, delta middle) + outerDelta
  refine ⟨totalDelta, ?_, ?_⟩
  · have hsum :
        (∑ middle ∈ middleChildren, delta middle) + middleChildren.card ≤
          ∑ middle ∈ middleChildren, (children P.partition middle.val).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun middle _ => Nat.succ_le_of_lt (hdelta middle)
    have hcard := children_card_decompose hPQ.1 hQR.1 upper
    have htotalBound :
        (∑ middle ∈ middleChildren, delta middle) + middleChildren.card ≤
          (children P.partition upper.val).card := by
      rw [hcard]
      exact hsum
    dsimp only [totalDelta]
    exact (Nat.add_lt_add_left houterDelta _).trans_le htotalBound
  · calc
      (R.weight upper.val : Nat) = childWeightSum Q upper.val + outerDelta :=
        houterWeight
      _ = (∑ middle ∈ middleChildren,
            (childWeightSum P middle.val + delta middle)) + outerDelta := by
        dsimp only [middleChildren]
        apply congrArg (fun n => n + outerDelta)
        apply Finset.sum_congr rfl
        intro middle _
        exact hweight middle
      _ = childWeightSum P upper.val + totalDelta := by
        rw [Finset.sum_add_distrib,
          ← childWeightSum_decompose P Q R.partition hPQ.1 hQR.1 upper]
        simp only [totalDelta, middleChildren, Nat.add_assoc]

private instance weightedPartitionLE
    {V : Type*} [Fintype V] [DecidableEq V] : LE (WeightedPartition V) :=
  ⟨WeightedRefines⟩

private instance weightedPartitionPartialOrder
    {V : Type*} [Fintype V] [DecidableEq V] : PartialOrder (WeightedPartition V) where
  le_refl := weightedRefines_refl
  le_trans _ _ _ := weightedRefines_trans
  le_antisymm _ _ := weightedRefines_antisymm

private def weightedBottom
    (V : Type*) [Fintype V] [DecidableEq V] : WeightedPartition V where
  partition := ⊥
  weight := fun _ => 0
  weight_lt_card := by
    intro block hblock
    rw [Finpartition.mem_bot_iff] at hblock
    obtain ⟨vertex, _, rfl⟩ := hblock
    simp
  weight_eq_zero := by simp

private theorem children_bot_card
    {V : Type*} [Fintype V] [DecidableEq V] (upper : Finset V) :
    (children (⊥ : Finpartition (univ : Finset V)) upper).card = upper.card := by
  classical
  symm
  apply Finset.card_bij
    (fun vertex _ =>
      (⟨{vertex}, Finpartition.mem_bot_iff.mpr ⟨vertex, mem_univ _, rfl⟩⟩ :
        (⊥ : Finpartition (univ : Finset V)).parts))
  · intro vertex hvertex
    rw [mem_children_iff]
    simpa using hvertex
  · intro left _ right _ heq
    have hsets := congrArg Subtype.val heq
    simpa using hsets
  · intro block hblock
    obtain ⟨vertex, _, hsingleton⟩ :=
      Finpartition.mem_bot_iff.mp block.property
    have hvertex : vertex ∈ upper := by
      have hsubset := mem_children_iff.mp hblock
      exact hsubset (hsingleton ▸ mem_singleton_self vertex)
    refine ⟨vertex, hvertex, ?_⟩
    apply Subtype.ext
    exact hsingleton

private theorem childWeightSum_bottom
    {V : Type*} [Fintype V] [DecidableEq V] (upper : Finset V) :
    childWeightSum (weightedBottom V) upper = 0 := by
  simp [childWeightSum, weightedBottom]

private theorem weightedBottom_le
    {V : Type*} [Fintype V] [DecidableEq V] (P : WeightedPartition V) :
    WeightedRefines (weightedBottom V) P := by
  refine ⟨bot_le, ?_⟩
  intro upper
  refine ⟨P.weight upper.val, ?_, ?_⟩
  · change (P.weight upper.val : Nat) <
      (children (⊥ : Finpartition (univ : Finset V)) upper.val).card
    rw [children_bot_card]
    exact P.weight_lt_card upper.val upper.property
  · simp [childWeightSum_bottom]

private instance weightedPartitionOrderBot
    {V : Type*} [Fintype V] [DecidableEq V] : OrderBot (WeightedPartition V) where
  bot := weightedBottom V
  bot_le := weightedBottom_le

private instance weightedPartitionLocallyFiniteOrder
    {V : Type*} [Fintype V] [DecidableEq V] : LocallyFiniteOrder (WeightedPartition V) := by
  classical
  exact Fintype.toLocallyFiniteOrder

end

end D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation

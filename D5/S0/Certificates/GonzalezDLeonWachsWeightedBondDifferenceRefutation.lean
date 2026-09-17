/- GID: D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: Weighted bond carrier and Mobius polynomial for a planned counterexample. -/

import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
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
  (show Function.Injective (fun P : WeightedPartition V => (P.partition, P.weight)) from by
    rintro ⟨P, weightP, boundP, zeroP⟩ ⟨Q, weightQ, boundQ, zeroQ⟩ h
    change (P, weightP) = (Q, weightQ) at h
    cases h
    rfl).decidableEq

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

/- The graph-dependent carrier is the literal connected-block restriction from
   the source: every actual partition block induces a connected subgraph. -/
private def ConnectedWeightedPartition
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :=
  {P : WeightedPartition V //
    ∀ block ∈ P.partition.parts, (G.induce (block : Set V)).Connected}

private instance connectedWeightedPartitionDecidableEq
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    DecidableEq (ConnectedWeightedPartition G) :=
  Subtype.instDecidableEq

private instance connectedWeightedPartitionFintype
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Fintype (ConnectedWeightedPartition G) := by
  classical
  unfold ConnectedWeightedPartition
  infer_instance

private instance connectedWeightedPartitionPartialOrder
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    PartialOrder (ConnectedWeightedPartition G) := by
  unfold ConnectedWeightedPartition
  infer_instance

private instance connectedWeightedPartitionLocallyFiniteOrder
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    LocallyFiniteOrder (ConnectedWeightedPartition G) := by
  classical
  exact Fintype.toLocallyFiniteOrder

private def connectedWeightedBottom
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ConnectedWeightedPartition G := by
  refine ⟨(weightedBottom V : WeightedPartition V), ?_⟩
  intro block hblock
  change block ∈ (⊥ : Finpartition (univ : Finset V)).parts at hblock
  rw [Finpartition.mem_bot_iff] at hblock
  obtain ⟨vertex, _, rfl⟩ := hblock
  refine @SimpleGraph.Connected.mk _ _ ?_ ⟨⟨vertex, by simp⟩⟩
  intro left right
  have heq : left = right := Subtype.ext (by
    have hleft : left.val = vertex := by simpa using left.property
    have hright : right.val = vertex := by simpa using right.property
    exact hleft.trans hright.symm)
  subst right
  exact SimpleGraph.Reachable.rfl

private instance connectedWeightedPartitionOrderBot
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    OrderBot (ConnectedWeightedPartition G) where
  bot := connectedWeightedBottom G
  bot_le P := weightedBottom_le P.val

/- The exponent in the source polynomial is the sum of the weights of the
   actual blocks, not a statistic of an auxiliary recurrence. -/
private def totalBlockWeight
    {V : Type*} [Fintype V] [DecidableEq V] (P : WeightedPartition V) : Nat :=
  ∑ block ∈ P.partition.parts, (P.weight block : Nat)

/- The source Möbius polynomial: sum over maximal connected weighted
   partitions, with incidence-algebra Möbius value from the singleton bottom. -/
private def sourceMobiusPolynomial
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Polynomial ℝ := by
  classical
  exact ∑ P ∈ (Finset.univ.filter (IsMax : ConnectedWeightedPartition G → Prop)),
    Polynomial.C (((IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) P : ℤ) : ℝ) *
      Polynomial.X ^ totalBlockWeight P.val

private def triangleThree : SimpleGraph (Fin 3) :=
  SimpleGraph.completeGraph (Fin 3)

private def pathThree : SimpleGraph (Fin 3) :=
  SimpleGraph.pathGraph 3

private theorem triangleThree_connected : triangleThree.Connected := by
  exact SimpleGraph.connected_top

private theorem pathThree_connected : pathThree.Connected := by
  simpa [pathThree] using SimpleGraph.pathGraph_connected 2

private theorem pathThree_lt_triangleThree : pathThree < triangleThree := by
  refine lt_of_le_of_ne le_top ?_
  intro heq
  have hadj := congrArg (fun G : SimpleGraph (Fin 3) ↦ G.Adj 0 2) heq
  simp [pathThree, triangleThree, SimpleGraph.pathGraph_adj] at hadj

/- A genuine undirected edge on the three-vertex carrier.  The strict order on
   endpoints removes the directed duplicate without quotienting the edge. -/
private structure LocalEdge (G : SimpleGraph (Fin 3)) where
  left : Fin 3
  right : Fin 3
  left_lt_right : left < right
  adjacent : G.Adj left right
  deriving DecidableEq

private instance localEdgeFintype (G : SimpleGraph (Fin 3)) : Fintype (LocalEdge G) := by
  refine Fintype.ofInjective (fun edge => (edge.left, edge.right)) ?_
  intro edge other h
  cases edge
  cases other
  simp only [Prod.mk.injEq] at h
  cases h.1
  cases h.2
  rfl

private inductive LocalNormalForm (G : SimpleGraph (Fin 3)) where
  | bottom
  | middle (edge : LocalEdge G) (weight : Fin 2)
  | top (weight : Fin 3)
  deriving DecidableEq, Fintype

private def localEdgeBlock {G : SimpleGraph (Fin 3)} (edge : LocalEdge G) :
    Finset (Fin 3) :=
  {edge.left, edge.right}

private theorem localEdgeBlock_card {G : SimpleGraph (Fin 3)} (edge : LocalEdge G) :
    (localEdgeBlock edge).card = 2 := by
  simp [localEdgeBlock, ne_of_lt edge.left_lt_right]

private theorem localEdgeBlock_compl_nonempty {G : SimpleGraph (Fin 3)}
    (edge : LocalEdge G) :
    ((univ : Finset (Fin 3)) \ localEdgeBlock edge).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h
  have hcard := Finset.card_le_card h
  rw [Finset.card_univ, Fintype.card_fin, localEdgeBlock_card] at hcard
  omega

private def localMiddlePartition {G : SimpleGraph (Fin 3)} (edge : LocalEdge G) :
    Finpartition (univ : Finset (Fin 3)) := by
  let block := localEdgeBlock edge
  let complement := (univ : Finset (Fin 3)) \ block
  refine Finpartition.ofExistsUnique {block, complement} ?_ ?_ ?_
  · intro part hpart
    simp only [mem_insert, mem_singleton] at hpart
    rcases hpart with rfl | rfl
    · exact subset_univ _
    · exact sdiff_subset
  · intro vertex _
    by_cases hvertex : vertex ∈ block
    · refine ⟨block, by simp [hvertex], ?_⟩
      intro part hpart
      rcases hpart with ⟨hpart, hmem⟩
      simp only [mem_insert, mem_singleton] at hpart
      rcases hpart with rfl | rfl
      · rfl
      · simp [complement, hvertex] at hmem
    · refine ⟨complement, by simp [complement, hvertex], ?_⟩
      intro part hpart
      rcases hpart with ⟨hpart, hmem⟩
      simp only [mem_insert, mem_singleton] at hpart
      rcases hpart with rfl | rfl
      · exact False.elim (hvertex hmem)
      · rfl
  · simp only [mem_insert, mem_singleton]
    push Not
    constructor
    · intro hzero
      have hcard := localEdgeBlock_card edge
      change ∅ = localEdgeBlock edge at hzero
      rw [← hzero, Finset.card_empty] at hcard
      omega
    · exact (localEdgeBlock_compl_nonempty edge).ne_empty.symm

@[simp] private theorem localMiddlePartition_parts {G : SimpleGraph (Fin 3)}
    (edge : LocalEdge G) :
    (localMiddlePartition edge).parts =
      {localEdgeBlock edge, (univ : Finset (Fin 3)) \ localEdgeBlock edge} :=
  rfl

private theorem singleton_induce_connected (G : SimpleGraph (Fin 3)) (vertex : Fin 3) :
    (G.induce ({vertex} : Set (Fin 3))).Connected := by
  refine @SimpleGraph.Connected.mk _ _ ?_ ⟨⟨vertex, by simp⟩⟩
  intro left right
  have heq : left = right := Subtype.ext (by
    have hleft : left.val = vertex := Set.mem_singleton_iff.mp left.property
    have hright : right.val = vertex := Set.mem_singleton_iff.mp right.property
    exact hleft.trans hright.symm)
  subst right
  exact SimpleGraph.Reachable.rfl

private theorem localEdgeBlock_compl_singleton {G : SimpleGraph (Fin 3)}
    (edge : LocalEdge G) :
    ∃ vertex : Fin 3,
      (univ : Finset (Fin 3)) \ localEdgeBlock edge = {vertex} := by
  have hcard : ((univ : Finset (Fin 3)) \ localEdgeBlock edge).card = 1 := by
    rw [card_sdiff, Finset.inter_eq_left.mpr (subset_univ _), Finset.card_univ,
      Fintype.card_fin, localEdgeBlock_card]
  exact Finset.card_eq_one.mp hcard

private theorem localEdgeBlock_ne_compl {G : SimpleGraph (Fin 3)}
    (edge : LocalEdge G) :
    localEdgeBlock edge ≠ (univ : Finset (Fin 3)) \ localEdgeBlock edge := by
  intro heq
  have hcard := congrArg Finset.card heq
  rw [localEdgeBlock_card] at hcard
  obtain ⟨vertex, hvertex⟩ := localEdgeBlock_compl_singleton edge
  rw [hvertex, Finset.card_singleton] at hcard
  omega

private theorem localEdge_eq_of_block_eq {G : SimpleGraph (Fin 3)}
    {edge other : LocalEdge G}
    (hblock : localEdgeBlock edge = localEdgeBlock other) : edge = other := by
  have hcoe := congrArg (fun block : Finset (Fin 3) => (block : Set (Fin 3))) hblock
  have hset : ({edge.left, edge.right} : Set (Fin 3)) =
      {other.left, other.right} := by
    ext vertex
    have hvertex := Set.ext_iff.mp hcoe vertex
    simpa [localEdgeBlock] using hvertex
  rw [Set.pair_eq_pair_iff] at hset
  rcases hset with hsame | hswap
  · cases edge
    cases other
    simp only at hsame
    cases hsame.1
    cases hsame.2
    rfl
  · have hleft : edge.left = other.right := hswap.1
    have hright : edge.right = other.left := hswap.2
    have := edge.left_lt_right
    rw [hleft, hright] at this
    exact False.elim ((lt_asymm other.left_lt_right) this)

private def localMiddleWeighted {G : SimpleGraph (Fin 3)}
    (edge : LocalEdge G) (w : Fin 2) : WeightedPartition (Fin 3) where
  partition := localMiddlePartition edge
  weight := fun block => if block = localEdgeBlock edge then
    ⟨w, lt_trans w.isLt (by decide : 2 < 4)⟩ else 0
  weight_lt_card := by
    intro block hblock
    simp only [localMiddlePartition_parts, mem_insert, mem_singleton] at hblock
    rcases hblock with rfl | hcomplement
    · simp only [ite_true, localEdgeBlock_card]
      exact w.isLt
    · subst block
      have hne : (univ : Finset (Fin 3)) \ localEdgeBlock edge ≠
          localEdgeBlock edge := (localEdgeBlock_ne_compl edge).symm
      simp only [hne, ite_false, Fin.val_zero]
      exact Finset.card_pos.mpr (localEdgeBlock_compl_nonempty edge)
  weight_eq_zero := by
    intro block hblock
    simp only [localMiddlePartition_parts, mem_insert, mem_singleton, not_or] at hblock
    simp [hblock.1]

private theorem localMiddleWeighted_connected {G : SimpleGraph (Fin 3)}
    (edge : LocalEdge G) (w : Fin 2) :
    ∀ block ∈ (localMiddleWeighted edge w).partition.parts,
      (G.induce (block : Set (Fin 3))).Connected := by
  intro block hblock
  simp only [localMiddleWeighted, localMiddlePartition_parts, mem_insert,
    mem_singleton] at hblock
  rcases hblock with rfl | rfl
  · have hset : (↑(localEdgeBlock edge) : Set (Fin 3)) =
        {edge.left, edge.right} := by
      ext vertex
      simp [localEdgeBlock]
    rw [hset]
    exact G.induce_pair_connected_of_adj edge.adjacent
  · obtain ⟨vertex, hvertex⟩ := localEdgeBlock_compl_singleton edge
    rw [hvertex]
    have hset : (↑({vertex} : Finset (Fin 3)) : Set (Fin 3)) = {vertex} := by
      ext other
      simp
    rw [hset]
    exact singleton_induce_connected G vertex

private def localTopWeighted (w : Fin 3) : WeightedPartition (Fin 3) where
  partition := Finpartition.indiscrete Finset.univ_nonempty.ne_empty
  weight := fun block => if block = (univ : Finset (Fin 3)) then
    ⟨w, lt_trans w.isLt (by decide : 3 < 4)⟩ else 0
  weight_lt_card := by
    intro block hblock
    simp only [Finpartition.indiscrete_parts, mem_singleton] at hblock
    subst block
    simp
  weight_eq_zero := by
    intro block hblock
    simp only [Finpartition.indiscrete_parts, mem_singleton] at hblock
    simp [hblock]

private def localNormalFormToSource {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    LocalNormalForm G → ConnectedWeightedPartition G
  | .bottom => connectedWeightedBottom G
  | .middle edge w => ⟨localMiddleWeighted edge w, localMiddleWeighted_connected edge w⟩
  | .top w => ⟨localTopWeighted w, by
      intro block hblock
      simp only [localTopWeighted, Finpartition.indiscrete_parts, mem_singleton] at hblock
      subst block
      have hset : (↑(univ : Finset (Fin 3)) : Set (Fin 3)) = Set.univ := by
        ext vertex
        simp
      rw [hset]
      exact (G.induceUnivIso.connected_iff).mpr hG⟩

@[simp] private theorem localNormalFormToSource_partition_card
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (normal : LocalNormalForm G) :
    (localNormalFormToSource hG normal).val.partition.parts.card =
      match normal with
      | .bottom => 3
      | .middle _ _ => 2
      | .top _ => 1 := by
  cases normal with
  | bottom =>
      simp [localNormalFormToSource, connectedWeightedBottom, weightedBottom]
  | middle edge w =>
      simp [localNormalFormToSource, localMiddleWeighted, localMiddlePartition_parts,
        localEdgeBlock_ne_compl edge]
  | top w =>
      simp [localNormalFormToSource, localTopWeighted]

@[simp] private theorem localNormalFormToSource_totalBlockWeight
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (normal : LocalNormalForm G) :
    totalBlockWeight (localNormalFormToSource hG normal).val =
      match normal with
      | .bottom => 0
      | .middle _ w => w
      | .top w => w := by
  cases normal with
  | bottom =>
      simp [localNormalFormToSource, totalBlockWeight, connectedWeightedBottom,
        weightedBottom]
  | middle edge w =>
      have hne := localEdgeBlock_ne_compl edge
      have hedge : localEdgeBlock edge ≠ ∅ := by
        intro hzero
        have hcard := localEdgeBlock_card edge
        rw [hzero, Finset.card_empty] at hcard
        omega
      simp [localNormalFormToSource, totalBlockWeight, localMiddleWeighted,
        localMiddlePartition_parts, hne, hedge, Finset.univ_nonempty.ne_empty]
  | top w =>
      simp [localNormalFormToSource, totalBlockWeight, localTopWeighted]

private theorem localNormalFormToSource_injective
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    Function.Injective (localNormalFormToSource hG) := by
  intro normal other heq
  cases normal with
  | bottom =>
      cases other with
      | bottom => rfl
      | middle edge w =>
          have hcard := congrArg (fun P => P.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hcard
          omega
      | top w =>
          have hcard := congrArg (fun P => P.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hcard
          omega
  | middle edge w =>
      cases other with
      | bottom =>
          have hcard := congrArg (fun P => P.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hcard
          omega
      | middle other v =>
          have hpartition := congrArg (fun P => P.val.partition.parts) heq
          change (localMiddlePartition edge).parts =
            (localMiddlePartition other).parts at hpartition
          have hmem : localEdgeBlock edge ∈ (localMiddlePartition other).parts := by
            rw [← hpartition, localMiddlePartition_parts]
            simp
          rw [localMiddlePartition_parts] at hmem
          simp only [mem_insert, mem_singleton] at hmem
          have hedge : edge = other := by
            rcases hmem with hsame | hcomplement
            · exact localEdge_eq_of_block_eq hsame
            · have hcard := congrArg Finset.card hcomplement
              rw [localEdgeBlock_card] at hcard
              obtain ⟨vertex, hvertex⟩ := localEdgeBlock_compl_singleton other
              rw [hvertex, Finset.card_singleton] at hcard
              omega
          subst other
          have hweight := congrArg
            (fun P => (P.val.weight (localEdgeBlock edge) : Nat)) heq
          simp only [localNormalFormToSource, localMiddleWeighted, ite_true] at hweight
          have hwv : w = v := Fin.ext hweight
          subst v
          rfl
      | top w =>
          have hcard := congrArg (fun P => P.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hcard
          omega
  | top w =>
      cases other with
      | bottom =>
          have hcard := congrArg (fun P => P.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hcard
          omega
      | middle edge v =>
          have hcard := congrArg (fun P => P.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hcard
          omega
      | top v =>
          have hweight := congrArg
            (fun P => (P.val.weight (univ : Finset (Fin 3)) : Nat)) heq
          simp only [localNormalFormToSource, localTopWeighted, ite_true] at hweight
          have hwv : w = v := Fin.ext hweight
          subst v
          rfl

private theorem finThreePartition_card_pos
    (P : Finpartition (univ : Finset (Fin 3))) : 0 < P.parts.card := by
  exact Finset.card_pos.mpr (P.parts_nonempty Finset.univ_nonempty.ne_empty)

private theorem finThreePartition_block_card_le
    (P : Finpartition (univ : Finset (Fin 3))) {block : Finset (Fin 3)}
    (hblock : block ∈ P.parts) : block.card + P.parts.card ≤ 4 := by
  have hrest : (P.parts.erase block).card ≤
      ∑ part ∈ P.parts.erase block, part.card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun part hpart =>
      Finset.card_pos.mpr (P.nonempty_of_mem_parts
        (Finset.mem_of_mem_erase hpart)))
  have hsum := P.sum_card_parts
  rw [← Finset.sum_erase_add P.parts Finset.card hblock] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hcard : (P.parts.erase block).card + 1 = P.parts.card := by
    rw [Finset.card_erase_of_mem hblock]
    have hpositive := Finset.card_pos.mpr ⟨block, hblock⟩
    omega
  omega

private theorem finThreePartition_eq_bot_of_card_three
    (P : Finpartition (univ : Finset (Fin 3))) (hcard : P.parts.card = 3) :
    P = ⊥ := by
  have hsingle : ∀ block ∈ P.parts, ∃ vertex : Fin 3, block = {vertex} := by
    intro block hb
    have hupper := finThreePartition_block_card_le P hb
    have hpositive := Finset.card_pos.mpr (P.nonempty_of_mem_parts hb)
    have hblockcard : block.card = 1 := by omega
    exact Finset.card_eq_one.mp hblockcard
  apply Finpartition.ext
  ext block
  constructor
  · intro hb
    obtain ⟨vertex, rfl⟩ := hsingle block hb
    exact Finpartition.mem_bot_iff.mpr ⟨vertex, mem_univ _, rfl⟩
  · intro hb
    obtain ⟨vertex, _, rfl⟩ := Finpartition.mem_bot_iff.mp hb
    obtain ⟨part, hp, hv⟩ := P.exists_mem (mem_univ vertex)
    obtain ⟨other, heq⟩ := hsingle part hp
    have : vertex = other := by simpa [heq] using hv
    subst other
    exact heq ▸ hp

private theorem finThreePartition_eq_indiscrete_of_card_one
    (P : Finpartition (univ : Finset (Fin 3))) (hcard : P.parts.card = 1) :
    P = Finpartition.indiscrete Finset.univ_nonempty.ne_empty := by
  obtain ⟨block, hparts⟩ := Finset.card_eq_one.mp hcard
  have huniv : block = (univ : Finset (Fin 3)) := by
    have hsum := P.sum_card_parts
    rw [hparts, Finset.sum_singleton] at hsum
    have hsub : block ⊆ (univ : Finset (Fin 3)) := subset_univ _
    exact Finset.eq_of_subset_of_card_le hsub (by simpa using hsum.ge)
  apply Finpartition.ext
  simp [hparts, huniv]

private theorem finThreePartition_exists_pair_of_card_two
    (P : Finpartition (univ : Finset (Fin 3))) (hcard : P.parts.card = 2) :
    ∃ block ∈ P.parts, block.card = 2 := by
  by_contra hnone
  push Not at hnone
  have hsingle : ∀ block ∈ P.parts, block.card = 1 := by
    intro block hb
    have hupper := finThreePartition_block_card_le P hb
    have hpos := Finset.card_pos.mpr (P.nonempty_of_mem_parts hb)
    have hne := hnone block hb
    omega
  have hsum : (∑ block ∈ P.parts, block.card) = P.parts.card := by
    calc
      (∑ block ∈ P.parts, block.card) = ∑ _block ∈ P.parts, 1 := by
        exact Finset.sum_congr rfl hsingle
      _ = P.parts.card := by simp
  rw [P.sum_card_parts] at hsum
  simp only [Finset.card_univ, Fintype.card_fin, hcard] at hsum
  omega

private theorem finThreePartition_pair_complement
    (P : Finpartition (univ : Finset (Fin 3)))
    (hcard : P.parts.card = 2) {block : Finset (Fin 3)}
    (hblock : block ∈ P.parts) :
    P.parts = {block, (univ : Finset (Fin 3)) \ block} := by
  obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp hcard
  have hchoice : block = a ∨ block = b := by
    rw [hpairs] at hblock
    simpa using hblock
  let other := if block = a then b else a
  have hother : other ∈ P.parts := by
    rcases hchoice with ha | hb
    · simp [other, ha, hpairs]
    · have hba : block ≠ a := by
        intro heq
        exact hab (heq.symm.trans hb)
      simp [other, hba, hpairs]
  have hne : block ≠ other := by
    rcases hchoice with ha | hb
    · simp [other, ha, hab]
    · have hba : block ≠ a := by
        intro heq
        exact hab (heq.symm.trans hb)
      simp [other, hb, hab.symm]
  have hparts : P.parts = {block, other} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro part hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hblock
      · exact hother
    · simp [hne, hcard]
  have hcomplement : other = (univ : Finset (Fin 3)) \ block := by
    ext vertex
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hv hvblock
      exact Finset.disjoint_left.mp (P.disjoint hother hblock hne.symm) hv hvblock
    · intro hvnot
      obtain ⟨part, hp, hv⟩ := P.exists_mem (mem_univ vertex)
      rw [hparts] at hp
      rcases Finset.mem_insert.mp hp with heq | heq
      · exact False.elim (hvnot (heq ▸ hv))
      · exact (Finset.mem_singleton.mp heq) ▸ hv
  rw [hparts, hcomplement]

private theorem localEdge_of_connected_pair
    {G : SimpleGraph (Fin 3)} {block : Finset (Fin 3)}
    (hpair : block.card = 2)
    (hconnected : (G.induce (block : Set (Fin 3))).Connected) :
    ∃ edge : LocalEdge G, localEdgeBlock edge = block := by
  obtain ⟨left, right, hne, hblock⟩ := Finset.card_eq_two.mp hpair
  have hset : (block : Set (Fin 3)) = {left, right} := by
    ext vertex
    simp [hblock]
  rw [hset] at hconnected
  have : Nontrivial ({left, right} : Set (Fin 3)) :=
    ⟨⟨⟨left, by simp⟩, ⟨right, by simp⟩, by
      intro heq
      exact hne (congrArg Subtype.val heq)⟩⟩
  obtain ⟨neighbor, hadj⟩ := hconnected.preconnected.exists_adj_of_nontrivial
    (⟨left, by simp⟩ : ({left, right} : Set (Fin 3)))
  have hright : neighbor.val = right := by
    have hmember : neighbor.val = left ∨ neighbor.val = right := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using neighbor.property
    rcases hmember with hleft | hright
    · exact False.elim (hadj.ne (Subtype.ext hleft.symm))
    · exact hright
  have hadj' : G.Adj left right := by
    simpa [hright] using hadj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⟨left, right, hlt, hadj'⟩, ?_⟩
    simp [localEdgeBlock, hblock]
  · refine ⟨⟨right, left, hgt, hadj'.symm⟩, ?_⟩
    simp [localEdgeBlock, hblock, Finset.pair_comm]

private theorem localNormalFormToSource_surjective
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    Function.Surjective (localNormalFormToSource hG) := by
  intro P
  let p := P.val.partition
  have hpos : 0 < p.parts.card := finThreePartition_card_pos p
  have hupper : p.parts.card ≤ 3 := by
    simpa [p] using p.card_parts_le_card
  by_cases hcount : p.parts.card = 1
  · have hpartition : P.val.partition =
        Finpartition.indiscrete Finset.univ_nonempty.ne_empty :=
        finThreePartition_eq_indiscrete_of_card_one _ hcount
    have hmem : (univ : Finset (Fin 3)) ∈ P.val.partition.parts := by
      rw [hpartition]
      simp
    let w : Fin 3 := ⟨P.val.weight univ,
      by simpa using P.val.weight_lt_card univ hmem⟩
    refine ⟨.top w, ?_⟩
    apply Subtype.ext
    change localTopWeighted w = P.val
    symm
    apply weightedPartition_ext hpartition
    funext block
    by_cases hb : block = (univ : Finset (Fin 3))
    · subst block
      apply Fin.ext
      rfl
    · have hnot : block ∉ P.val.partition.parts := by
        rw [hpartition]
        simpa using hb
      rw [P.val.weight_eq_zero block hnot]
      simp [localTopWeighted, hb]
  · by_cases hcount2 : p.parts.card = 2
    · obtain ⟨block, hblock, hcard⟩ :=
        finThreePartition_exists_pair_of_card_two p hcount2
      obtain ⟨edge, hedge⟩ := localEdge_of_connected_pair hcard (P.property block hblock)
      have hparts := finThreePartition_pair_complement p hcount2 hblock
      have hpartition : P.val.partition = localMiddlePartition edge := by
        apply Finpartition.ext
        rw [hparts, ← hedge]
        exact (localMiddlePartition_parts edge).symm
      let w : Fin 2 := ⟨P.val.weight block,
        by simpa [hcard] using P.val.weight_lt_card block hblock⟩
      refine ⟨.middle edge w, ?_⟩
      apply Subtype.ext
      change localMiddleWeighted edge w = P.val
      symm
      apply weightedPartition_ext hpartition
      funext part
      by_cases heq : part = block
      · subst part
        apply Fin.ext
        simp [localMiddleWeighted, hedge, w]
      · have hother : part ∈ P.val.partition.parts →
            part = (univ : Finset (Fin 3)) \ block := by
          rw [hparts]
          simp [heq]
        have hzero : P.val.weight part = 0 := by
          by_cases hp : part ∈ P.val.partition.parts
          · have hpart : part = (univ : Finset (Fin 3)) \ block := hother hp
            have hsize : part.card = 1 := by
              rw [hpart, Finset.card_sdiff, Finset.inter_eq_left.mpr (subset_univ _),
                Finset.card_univ, Fintype.card_fin, hcard]
            have hbound := P.val.weight_lt_card part hp
            apply Fin.ext
            simp only [Fin.val_zero]
            omega
          · exact P.val.weight_eq_zero part hp
        rw [hzero]
        simp [localMiddleWeighted, hedge, heq]
    · have hcount3 : p.parts.card = 3 := by omega
      have hpartition : P.val.partition = ⊥ :=
        finThreePartition_eq_bot_of_card_three _ hcount3
      refine ⟨.bottom, ?_⟩
      apply Subtype.ext
      change weightedBottom (Fin 3) = P.val
      symm
      apply weightedPartition_ext hpartition
      funext block
      by_cases hb : block ∈ P.val.partition.parts
      · have hsingleton : ∃ vertex : Fin 3, block = {vertex} := by
          rw [hpartition] at hb
          obtain ⟨vertex, _, heq⟩ := Finpartition.mem_bot_iff.mp hb
          exact ⟨vertex, heq.symm⟩
        obtain ⟨vertex, heq⟩ := hsingleton
        have hsize : block.card = 1 := by rw [heq]; simp
        have hbound := P.val.weight_lt_card block hb
        rw [hsize] at hbound
        apply Fin.ext
        change (P.val.weight block : Nat) = 0
        omega
      · rw [P.val.weight_eq_zero block hb]
        rfl

private instance localNormalFormPartialOrder
    (G : SimpleGraph (Fin 3)) [Fact G.Connected] :
    PartialOrder (LocalNormalForm G) where
  le := fun left right =>
    localNormalFormToSource Fact.out left ≤ localNormalFormToSource Fact.out right
  lt := fun left right =>
    localNormalFormToSource Fact.out left < localNormalFormToSource Fact.out right
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  le_antisymm _ _ hleft hright :=
    localNormalFormToSource_injective Fact.out (le_antisymm hleft hright)
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

private def localNormalFormOrderIso
    (G : SimpleGraph (Fin 3)) [Fact G.Connected] :
    LocalNormalForm G ≃o ConnectedWeightedPartition G := by
  let hG : G.Connected := Fact.out
  exact {
    toFun := localNormalFormToSource hG
    invFun := Function.surjInv (localNormalFormToSource_surjective hG)
    left_inv := Function.leftInverse_surjInv
      ⟨localNormalFormToSource_injective hG, localNormalFormToSource_surjective hG⟩
    right_inv := Function.rightInverse_surjInv (localNormalFormToSource_surjective hG)
    map_rel_iff' := Iff.rfl }

private theorem weightedRefines_eq_of_partition_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : WeightedPartition V} (hle : WeightedRefines P Q)
    (hpartition : P.partition = Q.partition) : P = Q := by
  apply weightedPartition_ext hpartition
  funext block
  by_cases hb : block ∈ P.partition.parts
  · have hq : block ∈ Q.partition.parts := hpartition ▸ hb
    rcases hle.2 ⟨block, hq⟩ with ⟨d, hd, heq⟩
    rw [children_self P.partition ⟨block, hb⟩, Finset.card_singleton] at hd
    have hd0 : d = 0 := by omega
    apply Fin.ext
    rw [childWeightSum, children_self P.partition ⟨block, hb⟩] at heq
    simpa [hd0] using heq.symm
  · have hq : block ∉ Q.partition.parts := by simpa [hpartition] using hb
    rw [P.weight_eq_zero block hb, Q.weight_eq_zero block hq]

private theorem children_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (univ : Finset V)) :
    children P (univ : Finset V) = P.parts.attach := by
  ext lower
  simp [children]

private theorem childWeightSum_univ
    {V : Type*} [Fintype V] [DecidableEq V] (P : WeightedPartition V) :
    childWeightSum P (univ : Finset V) = totalBlockWeight P := by
  simp only [childWeightSum, totalBlockWeight, children_univ]
  exact Finset.sum_attach P.partition.parts
    (fun block : Finset V => (P.weight block : Nat))

private theorem local_middle_le_top_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) (j : Fin 3) :
    (localNormalFormToSource hG (.middle edge w) ≤
      localNormalFormToSource hG (.top j)) ↔
      (w : Nat) ≤ j ∧ (j : Nat) ≤ w + 1 := by
  have hparts : (localMiddlePartition edge).parts.card = 2 := by
    simp [localMiddlePartition_parts, localEdgeBlock_ne_compl edge]
  have htop : (localTopWeighted j).partition.parts =
      {(univ : Finset (Fin 3))} := rfl
  have hchildren : (children (localMiddlePartition edge)
      (univ : Finset (Fin 3))).card = 2 := by
    rw [children_univ, Finset.card_attach, hparts]
  constructor
  · intro hle
    change WeightedRefines (localMiddleWeighted edge w) (localTopWeighted j) at hle
    rcases hle.2 ⟨univ, by simp [localTopWeighted]⟩ with ⟨d, hd, heq⟩
    change d < (children (localMiddlePartition edge) univ).card at hd
    change (j : Nat) = childWeightSum (localMiddleWeighted edge w) univ + d at heq
    rw [hchildren] at hd
    rw [childWeightSum_univ] at heq
    have hweight := localNormalFormToSource_totalBlockWeight hG
      (LocalNormalForm.middle edge w)
    change totalBlockWeight (localMiddleWeighted edge w) = (w : Nat) at hweight
    rw [hweight] at heq
    omega
  · rintro ⟨hlo, hhi⟩
    change WeightedRefines (localMiddleWeighted edge w) (localTopWeighted j)
    refine ⟨?_, ?_⟩
    · exact le_top
    · intro upper
      have hupper : upper.val = (univ : Finset (Fin 3)) := by
        simpa [localTopWeighted] using upper.property
      refine ⟨(j : Nat) - w, ?_, ?_⟩
      · change (j : Nat) - w <
            (children (localMiddlePartition edge) upper.val).card
        rw [hupper, hchildren]
        omega
      · rw [hupper, childWeightSum_univ]
        have hweight := localNormalFormToSource_totalBlockWeight hG
          (LocalNormalForm.middle edge w)
        change totalBlockWeight (localMiddleWeighted edge w) = (w : Nat) at hweight
        rw [hweight]
        simp [localTopWeighted]
        omega

private theorem local_middle_le_middle_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge other : LocalEdge G) (w v : Fin 2) :
    (localNormalFormToSource hG (.middle edge w) ≤
      localNormalFormToSource hG (.middle other v)) ↔
      edge = other ∧ w = v := by
  constructor
  · intro hle
    change WeightedRefines (localMiddleWeighted edge w)
      (localMiddleWeighted other v) at hle
    have hmem : localEdgeBlock edge ∈ (localMiddlePartition edge).parts := by
      simp [localMiddlePartition_parts]
    obtain ⟨upper, hu, hsub⟩ := hle.1 hmem
    have htarget : upper = localEdgeBlock other ∨
        upper = (univ : Finset (Fin 3)) \ localEdgeBlock other := by
      change upper ∈ (localMiddlePartition other).parts at hu
      simpa [localMiddlePartition_parts] using hu
    have hblock : localEdgeBlock edge = localEdgeBlock other := by
      rcases htarget with heq | heq
      · exact Finset.eq_of_subset_of_card_le (heq ▸ hsub) (by
          rw [localEdgeBlock_card, localEdgeBlock_card])
      · have hsize := Finset.card_le_card hsub
        rw [heq, localEdgeBlock_card] at hsize
        obtain ⟨vertex, hvertex⟩ := localEdgeBlock_compl_singleton other
        rw [hvertex, Finset.card_singleton] at hsize
        omega
    have hedges : edge = other := localEdge_eq_of_block_eq hblock
    subst other
    have heq : localMiddleWeighted edge w = localMiddleWeighted edge v :=
      weightedRefines_eq_of_partition_eq hle rfl
    have hweights := congrArg
      (fun P : WeightedPartition (Fin 3) => (P.weight (localEdgeBlock edge) : Nat)) heq
    simp only [localMiddleWeighted, ite_true] at hweights
    exact ⟨rfl, Fin.ext hweights⟩
  · rintro ⟨rfl, rfl⟩
    exact le_refl _

private theorem local_top_le_top_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (w v : Fin 3) :
    (localNormalFormToSource hG (.top w) ≤
      localNormalFormToSource hG (.top v)) ↔ w = v := by
  constructor
  · intro hle
    change WeightedRefines (localTopWeighted w) (localTopWeighted v) at hle
    have heq := weightedRefines_eq_of_partition_eq hle rfl
    have hweights := congrArg
      (fun P : WeightedPartition (Fin 3) => (P.weight (univ : Finset (Fin 3)) : Nat)) heq
    simp only [localTopWeighted, ite_true] at hweights
    exact Fin.ext hweights
  · rintro rfl
    exact le_refl _

private theorem local_top_not_le_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (w : Fin 3) (edge : LocalEdge G) (v : Fin 2) :
    ¬localNormalFormToSource hG (.top w) ≤
      localNormalFormToSource hG (.middle edge v) := by
  intro hle
  have hcard := Finpartition.card_mono hle.1
  change (localMiddlePartition edge).parts.card ≤
    (localTopWeighted w).partition.parts.card at hcard
  simp [localMiddlePartition_parts, localEdgeBlock_ne_compl edge,
    localTopWeighted] at hcard

private theorem local_middle_not_le_bottom
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    ¬localNormalFormToSource hG (.middle edge w) ≤
      localNormalFormToSource hG .bottom := by
  intro hle
  have hcard := Finpartition.card_mono hle.1
  change (⊥ : Finpartition (univ : Finset (Fin 3))).parts.card ≤
    (localMiddlePartition edge).parts.card at hcard
  simp [localMiddlePartition_parts, localEdgeBlock_ne_compl edge] at hcard

private theorem local_top_not_le_bottom
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (w : Fin 3) :
    ¬localNormalFormToSource hG (.top w) ≤
      localNormalFormToSource hG .bottom := by
  intro hle
  have hcard := Finpartition.card_mono hle.1
  change (⊥ : Finpartition (univ : Finset (Fin 3))).parts.card ≤
    (localTopWeighted w).partition.parts.card at hcard
  simp [localTopWeighted] at hcard

private theorem local_top_isMax
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (w : Fin 3) :
    IsMax (localNormalFormToSource hG (.top w)) := by
  intro Q hle
  have hcard := Finpartition.card_mono hle.1
  change Q.val.partition.parts.card ≤ (localTopWeighted w).partition.parts.card at hcard
  have hpositive := finThreePartition_card_pos Q.val.partition
  have htop : Q.val.partition =
      Finpartition.indiscrete Finset.univ_nonempty.ne_empty := by
    apply finThreePartition_eq_indiscrete_of_card_one
    simp [localTopWeighted] at hcard
    omega
  have heq : localTopWeighted w = Q.val :=
    weightedRefines_eq_of_partition_eq hle htop.symm
  change WeightedRefines Q.val (localTopWeighted w)
  rw [← heq]
  exact weightedRefines_refl _

private theorem local_isMax_iff_top
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (normal : LocalNormalForm G) :
    IsMax (localNormalFormToSource hG normal) ↔
      ∃ w : Fin 3, normal = .top w := by
  cases normal with
  | bottom =>
      constructor
      · intro hmax
        have hle : localNormalFormToSource hG .bottom ≤
            localNormalFormToSource hG (.top 0) := bot_le
        have heq := le_antisymm hle (hmax hle)
        have hcard := congrArg (fun P : ConnectedWeightedPartition G =>
          P.val.partition.parts.card) heq
        simp only [localNormalFormToSource_partition_card] at hcard
        omega
      · rintro ⟨w, h⟩
        cases h
  | middle edge w =>
      constructor
      · intro hmax
        let j : Fin 3 := ⟨w, lt_trans w.isLt (by decide : 2 < 3)⟩
        have hle : localNormalFormToSource hG (.middle edge w) ≤
            localNormalFormToSource hG (.top j) :=
          (local_middle_le_top_iff hG edge w j).mpr (by dsimp [j]; omega)
        have heq := le_antisymm hle (hmax hle)
        have hcard := congrArg (fun P : ConnectedWeightedPartition G =>
          P.val.partition.parts.card) heq
        simp only [localNormalFormToSource_partition_card] at hcard
        omega
      · rintro ⟨v, h⟩
        cases h
  | top w =>
      constructor
      · intro _
        exact ⟨w, rfl⟩
      · intro _
        exact local_top_isMax hG w

private theorem local_bottom_lt_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    (⊥ : ConnectedWeightedPartition G) <
      localNormalFormToSource hG (.middle edge w) := by
  refine lt_of_le_of_ne bot_le ?_
  intro heq
  have hcard := congrArg (fun P : ConnectedWeightedPartition G =>
    P.val.partition.parts.card) heq
  change (localNormalFormToSource hG (LocalNormalForm.bottom)).val.partition.parts.card =
    (localNormalFormToSource hG (LocalNormalForm.middle edge w)).val.partition.parts.card
    at hcard
  simp only [localNormalFormToSource_partition_card] at hcard
  omega

private theorem local_Ico_bottom_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    Finset.Ico (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.middle edge w)) = {⊥} := by
  ext P
  simp only [Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hlt⟩
    obtain ⟨normal, rfl⟩ := localNormalFormToSource_surjective hG P
    cases normal with
    | bottom => rfl
    | middle other v =>
        have heq := (local_middle_le_middle_iff hG other edge v w).mp hlt.le
        rcases heq with ⟨rfl, rfl⟩
        exact False.elim (lt_irrefl _ hlt)
    | top v => exact False.elim (local_top_not_le_middle hG v edge w hlt.le)
  · rintro rfl
    exact ⟨le_refl _, local_bottom_lt_middle hG edge w⟩

private theorem local_mu_bottom_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.middle edge w)) = -1 := by
  have hne : (⊥ : ConnectedWeightedPartition G) ≠
      localNormalFormToSource hG (.middle edge w) :=
    ne_of_lt (local_bottom_lt_middle hG edge w)
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne,
    local_Ico_bottom_middle hG edge w, Finset.sum_singleton,
    IncidenceAlgebra.mu_self]

private def localEligibleMiddle
    (G : SimpleGraph (Fin 3)) (j : Fin 3) : Finset (LocalEdge G × Fin 2) :=
  Finset.univ.filter fun ew => (ew.2 : Nat) ≤ j ∧ (j : Nat) ≤ ew.2 + 1

private theorem local_Ico_bottom_top
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (j : Fin 3) :
    Finset.Ico (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.top j)) =
      insert (⊥ : ConnectedWeightedPartition G)
        ((localEligibleMiddle G j).image fun ew =>
          localNormalFormToSource hG (.middle ew.1 ew.2)) := by
  ext P
  simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨_, hlt⟩
    obtain ⟨normal, rfl⟩ := localNormalFormToSource_surjective hG P
    cases normal with
    | bottom => exact Or.inl rfl
    | middle edge w =>
        refine Or.inr ⟨(edge, w), ?_, rfl⟩
        simpa [localEligibleMiddle] using
          (local_middle_le_top_iff hG edge w j).mp hlt.le
    | top w =>
        have heq := (local_top_le_top_iff hG w j).mp hlt.le
        subst j
        exact False.elim (lt_irrefl _ hlt)
  · rintro (heq | ⟨⟨edge, w⟩, hpair, heq⟩)
    · subst P
      exact ⟨le_refl _, by
        have hcard : (⊥ : ConnectedWeightedPartition G) ≠
            localNormalFormToSource hG (.top j) := by
          intro h
          have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
            Q.val.partition.parts.card) h
          change (localNormalFormToSource hG LocalNormalForm.bottom).val.partition.parts.card =
            (localNormalFormToSource hG (LocalNormalForm.top j)).val.partition.parts.card
            at hc
          simp only [localNormalFormToSource_partition_card] at hc
          omega
        exact lt_of_le_of_ne bot_le hcard⟩
    · subst P
      have heligible : (w : Nat) ≤ j ∧ (j : Nat) ≤ w + 1 := by
        simpa [localEligibleMiddle] using hpair
      exact ⟨bot_le, lt_of_le_of_ne
        ((local_middle_le_top_iff hG edge w j).mpr heligible) (by
          intro heq
          have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
            Q.val.partition.parts.card) heq
          simp only [localNormalFormToSource_partition_card] at hc
          omega)⟩

private theorem local_mu_bottom_top
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (j : Fin 3) :
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.top j)) =
      (localEligibleMiddle G j).card - 1 := by
  let imageMiddle (ew : LocalEdge G × Fin 2) :=
    localNormalFormToSource hG (LocalNormalForm.middle ew.1 ew.2)
  have hne : (⊥ : ConnectedWeightedPartition G) ≠
      localNormalFormToSource hG (.top j) := by
    intro heq
    have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
      Q.val.partition.parts.card) heq
    change (localNormalFormToSource hG LocalNormalForm.bottom).val.partition.parts.card =
      (localNormalFormToSource hG (LocalNormalForm.top j)).val.partition.parts.card at hc
    simp only [localNormalFormToSource_partition_card] at hc
    omega
  have hnotmem : (⊥ : ConnectedWeightedPartition G) ∉
      (localEligibleMiddle G j).image imageMiddle := by
    intro hmem
    obtain ⟨⟨edge, w⟩, _, heq⟩ := Finset.mem_image.mp hmem
    have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
      Q.val.partition.parts.card) heq
    change (localNormalFormToSource hG (LocalNormalForm.middle edge w)).val.partition.parts.card =
      (localNormalFormToSource hG LocalNormalForm.bottom).val.partition.parts.card at hc
    simp only [localNormalFormToSource_partition_card] at hc
    omega
  have hinj : Set.InjOn imageMiddle (localEligibleMiddle G j : Set _) := by
    intro a _ b _ hab
    have h := localNormalFormToSource_injective hG hab
    cases a with
    | mk edge w =>
        cases b with
        | mk other v =>
            injection h with he hw
            cases he
            cases hw
            rfl
  have hsum : ∑ ew ∈ localEligibleMiddle G j,
        (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (imageMiddle ew) =
      -((localEligibleMiddle G j).card : ℤ) := by
    calc
      _ = ∑ _ew ∈ localEligibleMiddle G j, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro ⟨edge, w⟩ _
        exact local_mu_bottom_middle hG edge w
      _ = -((localEligibleMiddle G j).card : ℤ) := by simp
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne,
    local_Ico_bottom_top hG j, Finset.sum_insert hnotmem,
    IncidenceAlgebra.mu_self]
  change -(1 + ∑ P ∈ (localEligibleMiddle G j).image imageMiddle,
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) P) = _
  rw [Finset.sum_image hinj, hsum]
  ring

private theorem localEligibleMiddle_card
    (G : SimpleGraph (Fin 3)) (j : Fin 3) :
    (localEligibleMiddle G j).card =
      (if (j : Nat) = 1 then 2 else 1) * Fintype.card (LocalEdge G) := by
  fin_cases j
  · have heq : localEligibleMiddle G 0 =
        (Finset.univ : Finset (LocalEdge G)).product ({0} : Finset (Fin 2)) := by
      ext ⟨edge, w⟩
      fin_cases w <;> simp [localEligibleMiddle]
    simp [heq]
  · have heq : localEligibleMiddle G 1 =
        (Finset.univ : Finset (LocalEdge G)).product (Finset.univ : Finset (Fin 2)) := by
      ext ⟨edge, w⟩
      fin_cases w <;> simp [localEligibleMiddle]
    simp [heq, Fintype.card_fin, mul_comm]
  · have heq : localEligibleMiddle G 2 =
        (Finset.univ : Finset (LocalEdge G)).product ({1} : Finset (Fin 2)) := by
      ext ⟨edge, w⟩
      fin_cases w <;> simp [localEligibleMiddle]
    simp [heq]

private theorem localEdge_endpoints {G : SimpleGraph (Fin 3)} (edge : LocalEdge G) :
    (edge.left = 0 ∧ edge.right = 1) ∨
    (edge.left = 0 ∧ edge.right = 2) ∨
    (edge.left = 1 ∧ edge.right = 2) := by
  cases edge with
  | mk left right hlt hadj =>
      fin_cases left <;> fin_cases right <;> simp_all <;> norm_num at hlt

private theorem localEdge_ext {G : SimpleGraph (Fin 3)}
    {edge other : LocalEdge G} (hl : edge.left = other.left)
    (hr : edge.right = other.right) : edge = other := by
  cases edge
  cases other
  simp only at hl hr
  cases hl
  cases hr
  rfl

private def triangleEdge01 : LocalEdge triangleThree :=
  ⟨0, 1, by decide, by simp [triangleThree]⟩

private def triangleEdge02 : LocalEdge triangleThree :=
  ⟨0, 2, by decide, by simp [triangleThree]⟩

private def triangleEdge12 : LocalEdge triangleThree :=
  ⟨1, 2, by decide, by simp [triangleThree]⟩

private def pathEdge01 : LocalEdge pathThree :=
  ⟨0, 1, by decide, by simp [pathThree, SimpleGraph.pathGraph_adj]⟩

private def pathEdge12 : LocalEdge pathThree :=
  ⟨1, 2, by decide, by simp [pathThree, SimpleGraph.pathGraph_adj]⟩

private theorem triangleThree_edge_count : Fintype.card (LocalEdge triangleThree) = 3 := by
  have huniv : (Finset.univ : Finset (LocalEdge triangleThree)) =
      {triangleEdge01, triangleEdge02, triangleEdge12} := by
    ext edge
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases localEdge_endpoints edge with h | h | h
    · exact Or.inl (localEdge_ext h.1 h.2)
    · exact Or.inr (Or.inl (localEdge_ext h.1 h.2))
    · exact Or.inr (Or.inr (localEdge_ext h.1 h.2))
  have h01ne02 : triangleEdge01 ≠ triangleEdge02 := by
    intro h
    have hc := congrArg LocalEdge.right h
    exact (by decide : (1 : Fin 3) ≠ 2) hc
  have h01ne12 : triangleEdge01 ≠ triangleEdge12 := by
    intro h
    have hc := congrArg LocalEdge.left h
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  have h02ne12 : triangleEdge02 ≠ triangleEdge12 := by
    intro h
    have hc := congrArg LocalEdge.left h
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  change (Finset.univ : Finset (LocalEdge triangleThree)).card = 3
  rw [huniv]
  simp [h01ne02, h01ne12, h02ne12]

private theorem pathThree_edge_count : Fintype.card (LocalEdge pathThree) = 2 := by
  have huniv : (Finset.univ : Finset (LocalEdge pathThree)) =
      {pathEdge01, pathEdge12} := by
    ext edge
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases localEdge_endpoints edge with h | h | h
    · exact Or.inl (localEdge_ext h.1 h.2)
    · have hn : ¬pathThree.Adj (0 : Fin 3) 2 := by
        simp [pathThree, SimpleGraph.pathGraph_adj]
      exact False.elim (hn (h.1 ▸ h.2 ▸ edge.adjacent))
    · exact Or.inr (localEdge_ext h.1 h.2)
  have hne : pathEdge01 ≠ pathEdge12 := by
    intro h
    have hc := congrArg LocalEdge.left h
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  change (Finset.univ : Finset (LocalEdge pathThree)).card = 2
  rw [huniv]
  simp [hne]

private theorem sourceMobiusPolynomial_local
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    sourceMobiusPolynomial G =
      Polynomial.C ((Fintype.card (LocalEdge G) : ℝ) - 1) +
      Polynomial.C (2 * (Fintype.card (LocalEdge G) : ℝ) - 1) * Polynomial.X +
        Polynomial.C ((Fintype.card (LocalEdge G) : ℝ) - 1) * Polynomial.X ^ 2 := by
  classical
  have hmax : (Finset.univ.filter (IsMax : ConnectedWeightedPartition G → Prop)) =
      (Finset.univ : Finset (Fin 3)).image
        (fun j => localNormalFormToSource hG (LocalNormalForm.top j)) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨normal, rfl⟩ := localNormalFormToSource_surjective hG P
      obtain ⟨j, hnormal⟩ := (local_isMax_iff_top hG normal).mp hp
      subst normal
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact local_top_isMax hG j
  have hinj : Set.InjOn
      (fun j : Fin 3 => localNormalFormToSource hG (LocalNormalForm.top j))
      (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
    intro j _ k _ h
    have hnormal := localNormalFormToSource_injective hG h
    exact LocalNormalForm.top.inj hnormal
  unfold sourceMobiusPolynomial
  rw [hmax, Finset.sum_image hinj]
  simp only [local_mu_bottom_top, localEligibleMiddle_card,
    localNormalFormToSource_totalBlockWeight]
  simp [Fin.sum_univ_succ]
  ring

private theorem triangleThree_sourceMobiusPolynomial :
    sourceMobiusPolynomial triangleThree =
      2 + 5 * Polynomial.X + 2 * Polynomial.X ^ 2 := by
  rw [sourceMobiusPolynomial_local triangleThree_connected, triangleThree_edge_count]
  norm_num [Polynomial.C_eq_natCast]
  simp only [Polynomial.C_ofNat]

private theorem pathThree_sourceMobiusPolynomial :
    sourceMobiusPolynomial pathThree =
      1 + 3 * Polynomial.X + Polynomial.X ^ 2 := by
  rw [sourceMobiusPolynomial_local pathThree_connected, pathThree_edge_count]
  norm_num [Polynomial.C_eq_natCast]
  simp only [Polynomial.C_ofNat]


end

end D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation

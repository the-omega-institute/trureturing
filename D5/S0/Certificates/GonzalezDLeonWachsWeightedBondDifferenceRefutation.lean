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

/- Each first coordinate is one genuine connected component. -/
private def fiberGraph (G : SimpleGraph (Fin 3)) : SimpleGraph (Fin 3 × Fin 3) where
  Adj x y := x.1 = y.1 ∧ G.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x.2 h.2⟩

private def fiberInclusion (G : SimpleGraph (Fin 3)) (i : Fin 3) :
    G →g fiberGraph G where
  toFun u := (i, u)
  map_rel' h := ⟨rfl, h⟩

private theorem fiberGraph_reachable_first
    {G : SimpleGraph (Fin 3)} {x y : Fin 3 × Fin 3}
    (h : (fiberGraph G).Reachable x y) : x.1 = y.1 := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => rfl
  | cons h _ ih => exact h.1.trans ih

private theorem fiberGraph_reachable_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (x y : Fin 3 × Fin 3) :
    (fiberGraph G).Reachable x y ↔ x.1 = y.1 := by
  refine ⟨fiberGraph_reachable_first, ?_⟩
  rcases x with ⟨i, u⟩
  rcases y with ⟨j, v⟩
  intro h
  change i = j at h
  subst j
  exact (hG u v).map (fiberInclusion G i)

private def fiberComponentEquiv
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    (fiberGraph G).ConnectedComponent ≃ Fin 3 where
  toFun := Quot.lift Prod.fst (fun _ _ h => fiberGraph_reachable_first h)
  invFun i := (fiberGraph G).connectedComponentMk (i, 0)
  left_inv := by
    intro component
    induction component using Quot.ind with
    | _ x =>
      exact SimpleGraph.ConnectedComponent.sound
        ((fiberGraph_reachable_iff hG (x.1, 0) x).mpr rfl)
  right_inv i := rfl

private theorem fiberGraph_vertex_count : Fintype.card (Fin 3 × Fin 3) = 9 := by
  simp

private theorem fiberGraph_component_count
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    Nat.card (fiberGraph G).ConnectedComponent = 3 := by
  rw [Nat.card_congr (fiberComponentEquiv hG)]
  simp

private theorem fiberPath_lt_fiberTriangle : fiberGraph pathThree < fiberGraph triangleThree := by
  refine lt_of_le_of_ne (fun x y h => ⟨h.1, pathThree_lt_triangleThree.le h.2⟩) ?_
  intro heq
  have hadj := congrArg
    (fun G : SimpleGraph (Fin 3 × Fin 3) => G.Adj (0, 0) (0, 2)) heq
  simp [fiberGraph, pathThree, triangleThree, SimpleGraph.pathGraph_adj] at hadj

/- Connectivity in the induced block, not mere containment, excludes crossing
   between fibers. This applies to every block of the original source carrier. -/
private theorem fiberBlock_first_eq
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    {block : Finset (Fin 3 × Fin 3)} (hb : block ∈ P.val.partition.parts)
    {x y : Fin 3 × Fin 3} (hx : x ∈ block) (hy : y ∈ block) : x.1 = y.1 := by
  have hr := (P.property block hb) ⟨x, hx⟩ ⟨y, hy⟩
  exact fiberGraph_reachable_first (hr.map (SimpleGraph.Embedding.induce _).toHom)

private def fiberLift (i : Fin 3) (block : Finset (Fin 3)) : Finset (Fin 3 × Fin 3) :=
  block.image fun u => (i, u)

@[simp] private theorem mem_fiberLift
    {i : Fin 3} {block : Finset (Fin 3)} {x : Fin 3 × Fin 3} :
    x ∈ fiberLift i block ↔ x.1 = i ∧ x.2 ∈ block := by
  rcases x with ⟨j, u⟩
  simp [fiberLift, eq_comm, and_comm]

private theorem fiberLift_injective (i : Fin 3) : Function.Injective (fiberLift i) := by
  intro A B h
  ext u
  have hm := congrArg (fun S => (i, u) ∈ S) h
  simpa using hm

@[simp] private theorem fiberLift_card (i : Fin 3) (block : Finset (Fin 3)) :
    (fiberLift i block).card = block.card :=
  Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)

private theorem fiberBlock_eq_lift
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    {block : Finset (Fin 3 × Fin 3)} (hb : block ∈ P.val.partition.parts)
    {x : Fin 3 × Fin 3} (hx : x ∈ block) :
    block = fiberLift x.1 (block.image Prod.snd) := by
  ext y
  simp only [mem_fiberLift, Finset.mem_image]
  constructor
  · intro hy
    exact ⟨fiberBlock_first_eq P hb hy hx, ⟨y, hy, rfl⟩⟩
  · rintro ⟨hi, z, hz, hzy⟩
    have hzi := fiberBlock_first_eq P hb hz hx
    have heq : z = y := Prod.ext (hzi.trans hi.symm) hzy
    exact heq ▸ hz

private def fiberRestrictionPartition
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    Finpartition (univ : Finset (Fin 3)) := by
  let parts := (univ : Finset (Fin 3)).powerset.filter
    (fun block => fiberLift i block ∈ P.val.partition.parts)
  have hmem : ∀ block, block ∈ parts ↔ fiberLift i block ∈ P.val.partition.parts := by
    intro block
    simp [parts]
  refine Finpartition.ofExistsUnique parts (fun _ _ => subset_univ _) ?_ ?_
  · intro u _
    obtain ⟨block, hb, hu⟩ := P.val.partition.exists_mem (mem_univ (i, u))
    let localBlock := block.image Prod.snd
    have heq := fiberBlock_eq_lift P hb hu
    refine ⟨localBlock, ⟨(hmem _).mpr (heq ▸ hb), ?_⟩, ?_⟩
    · exact mem_image.mpr ⟨(i, u), hu, rfl⟩
    · intro other hother
      apply fiberLift_injective i
      have hotherMem := (hmem other).mp hother.1
      have huOther : (i, u) ∈ fiberLift i other := by simpa using hother.2
      exact (P.val.partition.existsUnique_mem (mem_univ (i, u))).unique
        ⟨hotherMem, huOther⟩ ⟨heq ▸ hb, heq ▸ hu⟩
  · intro hzero
    have hbad := (hmem ∅).mp hzero
    simpa [fiberLift] using P.val.partition.ne_bot hbad

@[simp] private theorem mem_fiberRestrictionPartition
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (block : Finset (Fin 3)) :
    block ∈ (fiberRestrictionPartition P i).parts ↔
      fiberLift i block ∈ P.val.partition.parts := by
  simp [fiberRestrictionPartition]

private def fiberRestrictionWeighted
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    WeightedPartition (Fin 3) where
  partition := fiberRestrictionPartition P i
  weight block :=
    if hb : block ∈ (fiberRestrictionPartition P i).parts then
      ⟨P.val.weight (fiberLift i block), by
        have hlt := P.val.weight_lt_card _ ((mem_fiberRestrictionPartition P i block).mp hb)
        rw [fiberLift_card] at hlt
        have hcard : block.card ≤ 3 := by
          simpa using Finset.card_le_card (subset_univ block)
        simpa using (show (P.val.weight (fiberLift i block) : Nat) < 4 by omega)⟩
    else 0
  weight_lt_card := by
    intro block hb
    simp only [dif_pos hb]
    simpa using P.val.weight_lt_card _ ((mem_fiberRestrictionPartition P i block).mp hb)
  weight_eq_zero := by intro block hb; simp [hb]

@[simp] private theorem fiberRestriction_weight
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (block : Finset (Fin 3)) :
    ((fiberRestrictionWeighted P i).weight block : Nat) =
      (P.val.weight (fiberLift i block) : Nat) := by
  by_cases hb : block ∈ (fiberRestrictionPartition P i).parts
  · simp only [fiberRestrictionWeighted, dif_pos hb]
  · have hz := P.val.weight_eq_zero _ (by simpa using hb)
    simp only [fiberRestrictionWeighted, dif_neg hb, hz, Fin.val_zero]

private def fiberBlockProjectionHom
    (G : SimpleGraph (Fin 3)) (i : Fin 3) (block : Finset (Fin 3)) :
    (fiberGraph G).induce (fiberLift i block : Set (Fin 3 × Fin 3)) →g
      G.induce (block : Set (Fin 3)) where
  toFun x := ⟨x.val.2, (mem_fiberLift.mp x.property).2⟩
  map_rel' h := h.2

private def fiberRestriction
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    ConnectedWeightedPartition G := by
  refine ⟨fiberRestrictionWeighted P i, ?_⟩
  intro block hb
  have hc := P.property _ ((mem_fiberRestrictionPartition P i block).mp hb)
  exact hc.map (fiberBlockProjectionHom G i block) (by
    intro u
    exact ⟨⟨(i, u.val), by simp⟩, rfl⟩)

private theorem fiberLift_eq_fiberLift
    {i j : Fin 3} {A B : Finset (Fin 3)} (hA : A.Nonempty)
    (h : fiberLift i A = fiberLift j B) : i = j ∧ A = B := by
  obtain ⟨u, hu⟩ := hA
  have hm : (i, u) ∈ fiberLift j B := h ▸ (by simpa using hu)
  have hij := (mem_fiberLift.mp hm).1
  subst j
  exact ⟨rfl, fiberLift_injective i h⟩

private def fiberGlueParts
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    Finset (Finset (Fin 3 × Fin 3)) :=
  univ.biUnion fun i => (components i).val.partition.parts.image (fiberLift i)

@[simp] private theorem mem_fiberGlueParts
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (block : Finset (Fin 3 × Fin 3)) :
    block ∈ fiberGlueParts components ↔
      ∃ i A, A ∈ (components i).val.partition.parts ∧ fiberLift i A = block := by
  simp [fiberGlueParts]

private def fiberGluePartition
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    Finpartition (univ : Finset (Fin 3 × Fin 3)) := by
  refine Finpartition.ofExistsUnique (fiberGlueParts components)
    (fun _ _ => subset_univ _) ?_ ?_
  · rintro ⟨i, u⟩ _
    obtain ⟨A, hA, hu⟩ := (components i).val.partition.exists_mem (mem_univ u)
    refine ⟨fiberLift i A, ⟨(mem_fiberGlueParts components _).mpr ⟨i, A, hA, rfl⟩,
      by simpa using hu⟩, ?_⟩
    intro other hother
    obtain ⟨j, B, hB, rfl⟩ := (mem_fiberGlueParts components other).mp hother.1
    have hm := mem_fiberLift.mp hother.2
    change i = j ∧ u ∈ B at hm
    rcases hm with ⟨rfl, huB⟩
    have hBA := ((components i).val.partition.existsUnique_mem (mem_univ u)).unique
      ⟨hB, huB⟩ ⟨hA, hu⟩
    exact congrArg (fiberLift i) hBA
  · intro hzero
    obtain ⟨i, A, hA, heq⟩ := (mem_fiberGlueParts components ∅).mp hzero
    have hc := congrArg Finset.card heq
    rw [fiberLift_card, Finset.card_empty, Finset.card_eq_zero] at hc
    exact (components i).val.partition.ne_bot hA hc

private def fiberGlueOrigin
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (block : Finset (Fin 3 × Fin 3)) (hb : block ∈ fiberGlueParts components) :
    Σ i : Fin 3, (components i).val.partition.parts := by
  let h := (mem_fiberGlueParts components block).mp hb
  exact ⟨h.choose, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩⟩

private theorem fiberGlueOrigin_spec
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (block : Finset (Fin 3 × Fin 3)) (hb : block ∈ fiberGlueParts components) :
    fiberLift (fiberGlueOrigin components block hb).1
      (fiberGlueOrigin components block hb).2.val = block := by
  exact ((mem_fiberGlueParts components block).mp hb).choose_spec.choose_spec.2

private def fiberGlueWeighted
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    WeightedPartition (Fin 3 × Fin 3) where
  partition := fiberGluePartition components
  weight block := if hb : block ∈ fiberGlueParts components then
    let origin := fiberGlueOrigin components block hb
    ⟨(components origin.1).val.weight origin.2.val, by
      have hlt := (components origin.1).val.weight origin.2.val |>.isLt
      simp only [Fintype.card_prod, Fintype.card_fin] at *
      omega⟩
    else 0
  weight_lt_card := by
    intro block hb
    change block ∈ fiberGlueParts components at hb
    simp only [dif_pos hb]
    have hlt := (components (fiberGlueOrigin components block hb).1).val.weight_lt_card
      _ (fiberGlueOrigin components block hb).2.property
    have hc := congrArg Finset.card (fiberGlueOrigin_spec components block hb)
    rw [fiberLift_card] at hc
    exact hc ▸ hlt
  weight_eq_zero := by
    intro block hb
    change block ∉ fiberGlueParts components at hb
    simp only [dif_neg hb]

private def fiberBlockInclusionHom
    (G : SimpleGraph (Fin 3)) (i : Fin 3) (block : Finset (Fin 3)) :
    G.induce (block : Set (Fin 3)) →g
      (fiberGraph G).induce (fiberLift i block : Set (Fin 3 × Fin 3)) where
  toFun u := ⟨(i, u.val), by simp⟩
  map_rel' h := ⟨rfl, h⟩

private def fiberGlue
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    ConnectedWeightedPartition (fiberGraph G) := by
  refine ⟨fiberGlueWeighted components, ?_⟩
  intro block hb
  change block ∈ fiberGlueParts components at hb
  obtain ⟨i, A, hA, rfl⟩ := (mem_fiberGlueParts components block).mp hb
  exact ((components i).property A hA).map (fiberBlockInclusionHom G i A) (by
    intro x
    refine ⟨⟨x.val.2, (mem_fiberLift.mp x.property).2⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext (mem_fiberLift.mp x.property).1.symm rfl)

@[simp] private theorem fiberGlue_lift_mem
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (i : Fin 3) (A : Finset (Fin 3)) :
    fiberLift i A ∈ (fiberGlue components).val.partition.parts ↔
      A ∈ (components i).val.partition.parts := by
  change fiberLift i A ∈ fiberGlueParts components ↔ _
  constructor
  · intro h
    obtain ⟨j, B, hB, heq⟩ := (mem_fiberGlueParts components _).mp h
    obtain ⟨hji, hBA⟩ := fiberLift_eq_fiberLift
      ((components j).val.partition.nonempty_of_mem_parts hB) heq
    subst j
    exact hBA ▸ hB
  · intro hA
    exact (mem_fiberGlueParts components _).mpr ⟨i, A, hA, rfl⟩

@[simp] private theorem fiberGlue_weight_lift
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (i : Fin 3) (A : Finset (Fin 3)) :
    ((fiberGlue components).val.weight (fiberLift i A) : Nat) =
      ((components i).val.weight A : Nat) := by
  by_cases hA : A ∈ (components i).val.partition.parts
  · have hb : fiberLift i A ∈ fiberGlueParts components :=
      (mem_fiberGlueParts components _).mpr ⟨i, A, hA, rfl⟩
    change ((fiberGlueWeighted components).weight (fiberLift i A) : Nat) = _
    simp only [fiberGlueWeighted, dif_pos hb]
    have hs := fiberGlueOrigin_spec components (fiberLift i A) hb
    generalize fiberGlueOrigin components (fiberLift i A) hb = origin at hs ⊢
    rcases origin with ⟨j, B⟩
    obtain ⟨hji, hBA⟩ := fiberLift_eq_fiberLift
      ((components j).val.partition.nonempty_of_mem_parts B.property) hs
    change j = i at hji
    subst j
    simp only [hBA]
  · have hb : fiberLift i A ∉ (fiberGlue components).val.partition.parts := by
      simpa using hA
    rw [(fiberGlue components).val.weight_eq_zero _ hb,
      (components i).val.weight_eq_zero _ hA]
    rfl

private theorem fiberRestriction_glue
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (i : Fin 3) : fiberRestriction (fiberGlue components) i = components i := by
  apply Subtype.ext
  apply weightedPartition_ext
  · apply Finpartition.ext
    ext A
    exact (mem_fiberRestrictionPartition (fiberGlue components) i A).trans
      (fiberGlue_lift_mem components i A)
  · funext A
    apply Fin.ext
    exact (fiberRestriction_weight (fiberGlue components) i A).trans
      (fiberGlue_weight_lift components i A)

private theorem fiberGlue_restriction
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    fiberGlue (fiberRestriction P) = P := by
  have hparts : (fiberGlue (fiberRestriction P)).val.partition = P.val.partition := by
    apply Finpartition.ext
    ext block
    change block ∈ fiberGlueParts (fiberRestriction P) ↔ _
    constructor
    · intro hb
      obtain ⟨i, A, hA, rfl⟩ := (mem_fiberGlueParts (fiberRestriction P) block).mp hb
      exact (mem_fiberRestrictionPartition P i A).mp hA
    · intro hb
      obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts hb
      have heq := fiberBlock_eq_lift P hb hx
      exact (mem_fiberGlueParts (fiberRestriction P) block).mpr
        ⟨x.1, block.image Prod.snd,
          (mem_fiberRestrictionPartition P _ _).mpr (heq ▸ hb), heq.symm⟩
  apply Subtype.ext
  apply weightedPartition_ext hparts
  funext block
  by_cases hb : block ∈ P.val.partition.parts
  · obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts hb
    have heq := fiberBlock_eq_lift P hb hx
    apply Fin.ext
    calc
      ((fiberGlue (fiberRestriction P)).val.weight block : Nat) =
          ((fiberGlue (fiberRestriction P)).val.weight
            (fiberLift x.1 (block.image Prod.snd)) : Nat) :=
        congrArg (fun B => ((fiberGlue (fiberRestriction P)).val.weight B : Nat)) heq
      _ = ((fiberRestriction P x.1).val.weight (block.image Prod.snd) : Nat) :=
        fiberGlue_weight_lift _ _ _
      _ = (P.val.weight (fiberLift x.1 (block.image Prod.snd)) : Nat) :=
        fiberRestriction_weight _ _ _
      _ = (P.val.weight block : Nat) := congrArg (fun B => (P.val.weight B : Nat)) heq.symm
  · rw [P.val.weight_eq_zero _ hb,
      (fiberGlue (fiberRestriction P)).val.weight_eq_zero _ (by simpa [hparts] using hb)]

private def fiberSourceEquiv (G : SimpleGraph (Fin 3)) :
    ConnectedWeightedPartition (fiberGraph G) ≃ (Fin 3 → ConnectedWeightedPartition G) where
  toFun := fiberRestriction
  invFun := fiberGlue
  left_inv := fiberGlue_restriction
  right_inv components := funext (fiberRestriction_glue components)

@[simp] private theorem fiberLift_subset_iff
    (i : Fin 3) (A B : Finset (Fin 3)) : fiberLift i A ⊆ fiberLift i B ↔ A ⊆ B := by
  constructor
  · intro h u hu
    exact (mem_fiberLift.mp (h (show (i, u) ∈ fiberLift i A from by simpa using hu))).2
  · intro h x hx
    exact mem_fiberLift.mpr ⟨(mem_fiberLift.mp hx).1, h (mem_fiberLift.mp hx).2⟩

private def fiberRestrictionChild
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3)
    (A : (fiberRestrictionPartition P i).parts) : P.val.partition.parts :=
  ⟨fiberLift i A.val, (mem_fiberRestrictionPartition P i A.val).mp A.property⟩

private theorem fiberRestrictionChild_injective
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    Function.Injective (fiberRestrictionChild P i) := by
  intro A B h
  exact Subtype.ext (fiberLift_injective i (congrArg Subtype.val h))

private theorem fiberRestriction_children
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (upper : Finset (Fin 3)) :
    (children (fiberRestrictionPartition P i) upper).image (fiberRestrictionChild P i) =
      children P.val.partition (fiberLift i upper) := by
  ext lower
  simp only [mem_image, mem_children_iff]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (fiberLift_subset_iff i A.val upper).mpr hA
  · intro hsub
    obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts lower.property
    have hxi := (mem_fiberLift.mp (hsub hx)).1
    have heq := fiberBlock_eq_lift P lower.property hx
    rw [hxi] at heq
    let A := lower.val.image Prod.snd
    have hA : A ∈ (fiberRestrictionPartition P i).parts :=
      (mem_fiberRestrictionPartition P i A).mpr (heq ▸ lower.property)
    refine ⟨⟨A, hA⟩, ?_, ?_⟩
    · exact (fiberLift_subset_iff i A upper).mp (heq ▸ hsub)
    · exact Subtype.ext heq.symm

private theorem fiberRestriction_children_card
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (upper : Finset (Fin 3)) :
    (children (fiberRestrictionPartition P i) upper).card =
      (children P.val.partition (fiberLift i upper)).card := by
  rw [← fiberRestriction_children P i upper,
    Finset.card_image_of_injective _ (fiberRestrictionChild_injective P i)]

private theorem fiberRestriction_childWeightSum
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (upper : Finset (Fin 3)) :
    childWeightSum (fiberRestriction P i).val upper =
      childWeightSum P.val (fiberLift i upper) := by
  unfold childWeightSum
  rw [← fiberRestriction_children P i upper,
    Finset.sum_image (fiberRestrictionChild_injective P i).injOn]
  apply Finset.sum_congr rfl
  intro A _
  exact fiberRestriction_weight P i A.val

private theorem fiberRestriction_partition_le_iff
    {G : SimpleGraph (Fin 3)} (P Q : ConnectedWeightedPartition (fiberGraph G)) :
    P.val.partition ≤ Q.val.partition ↔
      ∀ i, (fiberRestrictionPartition P i) ≤ (fiberRestrictionPartition Q i) := by
  constructor
  · intro h i A hA
    have hAlift := (mem_fiberRestrictionPartition P i A).mp hA
    obtain ⟨upper, hupper, hsub⟩ := h hAlift
    obtain ⟨u, hu⟩ := (fiberRestrictionPartition P i).nonempty_of_mem_parts hA
    have heq := fiberBlock_eq_lift Q hupper
      (hsub (show (i, u) ∈ fiberLift i A from by simpa using hu))
    refine ⟨upper.image Prod.snd, (mem_fiberRestrictionPartition Q i _).mpr
      (heq ▸ hupper), ?_⟩
    exact (fiberLift_subset_iff i A _).mp (heq ▸ hsub)
  · intro h block hb
    obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts hb
    have heq := fiberBlock_eq_lift P hb hx
    have hA := (mem_fiberRestrictionPartition P x.1 _).mpr (heq ▸ hb)
    obtain ⟨upper, hu, hsub⟩ := h x.1 hA
    refine ⟨fiberLift x.1 upper, (mem_fiberRestrictionPartition Q x.1 upper).mp hu, ?_⟩
    rw [heq]
    exact (fiberLift_subset_iff x.1 _ upper).mpr hsub

private theorem fiberRestriction_le_iff
    {G : SimpleGraph (Fin 3)} (P Q : ConnectedWeightedPartition (fiberGraph G)) :
    P ≤ Q ↔ ∀ i, fiberRestriction P i ≤ fiberRestriction Q i := by
  change WeightedRefines P.val Q.val ↔
    ∀ i, WeightedRefines (fiberRestriction P i).val (fiberRestriction Q i).val
  constructor
  · intro h i
    refine ⟨(fiberRestriction_partition_le_iff P Q).mp h.1 i, ?_⟩
    intro upper
    have hu := (mem_fiberRestrictionPartition Q i upper.val).mp upper.property
    obtain ⟨d, hd, hw⟩ := h.2 ⟨fiberLift i upper.val, hu⟩
    refine ⟨d, ?_, ?_⟩
    · change d < (children (fiberRestrictionPartition P i) upper.val).card
      rwa [fiberRestriction_children_card P i upper.val]
    · change ((fiberRestrictionWeighted Q i).weight upper.val : Nat) =
        childWeightSum (fiberRestriction P i).val upper.val + d
      rw [fiberRestriction_weight, fiberRestriction_childWeightSum]
      exact hw
  · intro h
    refine ⟨(fiberRestriction_partition_le_iff P Q).mpr (fun i => (h i).1), ?_⟩
    intro upper
    obtain ⟨x, hx⟩ := Q.val.partition.nonempty_of_mem_parts upper.property
    have heq := fiberBlock_eq_lift Q upper.property hx
    have hu := (mem_fiberRestrictionPartition Q x.1 _).mpr (heq ▸ upper.property)
    obtain ⟨d, hd, hw⟩ := (h x.1).2 ⟨upper.val.image Prod.snd, hu⟩
    refine ⟨d, ?_, ?_⟩
    · change d < (children (fiberRestrictionPartition P x.1) (upper.val.image Prod.snd)).card at hd
      rw [fiberRestriction_children_card] at hd
      simpa only [← heq] using hd
    · change ((fiberRestrictionWeighted Q x.1).weight (upper.val.image Prod.snd) : Nat) =
        childWeightSum (fiberRestriction P x.1).val (upper.val.image Prod.snd) + d at hw
      rw [fiberRestriction_weight, fiberRestriction_childWeightSum] at hw
      simpa only [← heq] using hw

private def fiberSourceOrderIso (G : SimpleGraph (Fin 3)) :
    ConnectedWeightedPartition (fiberGraph G) ≃o (Fin 3 → ConnectedWeightedPartition G) where
  toEquiv := fiberSourceEquiv G
  map_rel_iff' := by
    intro P Q
    exact (fiberRestriction_le_iff P Q).symm

private theorem fiberGlue_totalBlockWeight
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    totalBlockWeight (fiberGlue components).val =
      ∑ i, totalBlockWeight (components i).val := by
  have hdisjoint : Set.PairwiseDisjoint (↑(univ : Finset (Fin 3)))
      (fun i => (components i).val.partition.parts.image (fiberLift i)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro block hi hj
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hi
    obtain ⟨B, hB, heq⟩ := mem_image.mp hj
    have hji := (fiberLift_eq_fiberLift
      ((components j).val.partition.nonempty_of_mem_parts hB) heq).1
    exact hij hji.symm
  change (∑ block ∈ fiberGlueParts components,
    ((fiberGlue components).val.weight block : Nat)) = _
  unfold fiberGlueParts
  rw [Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image (fiberLift_injective i).injOn]
  exact Finset.sum_congr rfl (fun A _ => fiberGlue_weight_lift components i A)

private theorem fiberRestriction_totalBlockWeight
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    totalBlockWeight P.val = ∑ i, totalBlockWeight (fiberRestriction P i).val := by
  simpa only [fiberGlue_restriction] using fiberGlue_totalBlockWeight (fiberRestriction P)

private theorem fiberRestriction_bottom (G : SimpleGraph (Fin 3)) :
    fiberRestriction (⊥ : ConnectedWeightedPartition (fiberGraph G)) =
      (⊥ : Fin 3 → ConnectedWeightedPartition G) :=
  (fiberSourceOrderIso G).map_bot

private theorem fiber_isMax_iff
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    IsMax P ↔ ∀ i, IsMax (fiberRestriction P i) := by
  rw [← (fiberSourceOrderIso G).isMax_apply]
  change IsMax (fiberRestriction P) ↔ _
  constructor
  · intro h i Q hiQ
    have hle : fiberRestriction P ≤ Function.update (fiberRestriction P) i Q := by
      intro j
      by_cases hji : j = i
      · subst j; simpa using hiQ
      · simp [Function.update_of_ne hji]
    have hback := h hle i
    simpa using hback
  · intro h Q hPQ i
    exact h i (hPQ i)

private theorem finite_mu_orderIso
    {α β : Type*} [Finite α] [PartialOrder α] [PartialOrder β]
    [DecidableEq α] [DecidableEq β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] (e : α ≃o β) (a b : α) :
    (IncidenceAlgebra.mu ℤ) (e a) (e b) = (IncidenceAlgebra.mu ℤ) a b := by
  classical
  induction b using (Finite.wellFounded_of_trans_of_irrefl
      ((· < ·) : α → α → Prop)).induction with
  | h b ih =>
    by_cases hab : a = b
    · subst b; simp
    · rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (e.injective.ne hab),
        IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hab]
      congr 1
      symm
      apply Finset.sum_bij (fun x _ => e x)
      · intro x hx
        simpa only [Finset.mem_Ico, e.le_iff_le, e.lt_iff_lt] using hx
      · intro x _ y _ hxy
        exact e.injective hxy
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        simpa only [Finset.mem_Ico, ← e.le_iff_le, ← e.lt_iff_lt,
          e.apply_symm_apply] using hy
      · intro x hx
        exact (ih x (Finset.mem_Ico.mp hx).2).symm

private def sourceTripleOrderIso (G : SimpleGraph (Fin 3)) :
    (Fin 3 → ConnectedWeightedPartition G) ≃o
      (ConnectedWeightedPartition G ×
        (ConnectedWeightedPartition G × ConnectedWeightedPartition G)) where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    change (f 0 ≤ g 0 ∧ f 1 ≤ g 1 ∧ f 2 ≤ g 2) ↔ ∀ i, f i ≤ g i
    constructor
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · intro h; exact ⟨h 0, h 1, h 2⟩

private def fiberSourceTripleOrderIso (G : SimpleGraph (Fin 3)) :=
  (fiberSourceOrderIso G).trans (sourceTripleOrderIso G)

private theorem fiber_mu_product
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition (fiberGraph G)) P =
      (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (fiberRestriction P 0) *
        ((IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (fiberRestriction P 1) *
          (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (fiberRestriction P 2)) := by
  classical
  rw [← finite_mu_orderIso (fiberSourceTripleOrderIso G) ⊥ P,
    (fiberSourceTripleOrderIso G).map_bot,
    ← IncidenceAlgebra.mu_prod_mu, IncidenceAlgebra.prod_apply,
    ← IncidenceAlgebra.mu_prod_mu, IncidenceAlgebra.prod_apply]
  rfl

private def sourceSummand
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (P : ConnectedWeightedPartition G) : Polynomial ℝ := by
  classical
  exact if IsMax P then
    Polynomial.C (((IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) P : ℤ) : ℝ) *
      Polynomial.X ^ totalBlockWeight P.val else 0

private theorem fiber_sourceSummand_product
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    sourceSummand P = sourceSummand (fiberRestriction P 0) *
      (sourceSummand (fiberRestriction P 1) * sourceSummand (fiberRestriction P 2)) := by
  classical
  have hmax : IsMax P ↔ IsMax (fiberRestriction P 0) ∧
      IsMax (fiberRestriction P 1) ∧ IsMax (fiberRestriction P 2) := by
    rw [fiber_isMax_iff]
    constructor
    · intro h; exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
  have hweight : totalBlockWeight P.val =
      totalBlockWeight (fiberRestriction P 0).val +
        (totalBlockWeight (fiberRestriction P 1).val +
          totalBlockWeight (fiberRestriction P 2).val) := by
    rw [fiberRestriction_totalBlockWeight]
    simp [Fin.sum_univ_succ]
  unfold sourceSummand
  by_cases h0 : IsMax (fiberRestriction P 0) <;>
    by_cases h1 : IsMax (fiberRestriction P 1) <;>
      by_cases h2 : IsMax (fiberRestriction P 2)
  all_goals simp only [hmax, h0, h1, h2, and_self, and_true, and_false,
    if_true, if_false, zero_mul, mul_zero]
  rw [fiber_mu_product, hweight, Int.cast_mul, Int.cast_mul,
    Polynomial.C_mul, Polynomial.C_mul, pow_add, pow_add]
  ring

private theorem fiberGraph_sourceMobiusPolynomial
    (G : SimpleGraph (Fin 3)) :
    sourceMobiusPolynomial (fiberGraph G) = (sourceMobiusPolynomial G) ^ 3 := by
  classical
  have hsumGlobal : sourceMobiusPolynomial (fiberGraph G) =
      ∑ P : ConnectedWeightedPartition (fiberGraph G), sourceSummand P := by
    simp only [sourceMobiusPolynomial, Finset.sum_filter, sourceSummand]
  have hsumLocal : sourceMobiusPolynomial G =
      ∑ P : ConnectedWeightedPartition G, sourceSummand P := by
    simp only [sourceMobiusPolynomial, Finset.sum_filter, sourceSummand]
  rw [hsumGlobal, hsumLocal]
  let e := fiberSourceTripleOrderIso G
  have heq : (∑ P : ConnectedWeightedPartition (fiberGraph G), sourceSummand P) =
      ∑ p : ConnectedWeightedPartition G ×
        (ConnectedWeightedPartition G × ConnectedWeightedPartition G),
          sourceSummand p.1 * (sourceSummand p.2.1 * sourceSummand p.2.2) := by
    apply Fintype.sum_equiv e.toEquiv
    intro P
    exact fiber_sourceSummand_product P
  rw [heq]
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem fiberTriangle_sourceMobiusPolynomial :
    sourceMobiusPolynomial (fiberGraph triangleThree) =
      (2 + 5 * Polynomial.X + 2 * Polynomial.X ^ 2) ^ 3 := by
  rw [fiberGraph_sourceMobiusPolynomial, triangleThree_sourceMobiusPolynomial]

private theorem fiberPath_sourceMobiusPolynomial :
    sourceMobiusPolynomial (fiberGraph pathThree) =
      (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 := by
  rw [fiberGraph_sourceMobiusPolynomial, pathThree_sourceMobiusPolynomial]

private def obstructionQuartic : Polynomial ℝ :=
  7 * Polynomial.X ^ 4 + 37 * Polynomial.X ^ 3 +
    63 * Polynomial.X ^ 2 + 37 * Polynomial.X + 7

private theorem obstructionQuartic_no_real_root (x : ℝ) :
    Polynomial.eval x obstructionQuartic ≠ 0 := by
  intro hx
  let a : ℝ := 2 + 5 * x + 2 * x ^ 2
  let b : ℝ := 1 + 3 * x + x ^ 2
  have hsum : (2 * a + b) ^ 2 + 3 * b ^ 2 = 0 := by
    have heval : Polynomial.eval x obstructionQuartic =
        7 * x ^ 4 + 37 * x ^ 3 + 63 * x ^ 2 + 37 * x + 7 := by
      simp [obstructionQuartic, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow]
    rw [heval] at hx
    dsimp [a, b]
    nlinarith [hx]
  have hb : b = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have ha : a = 0 := by nlinarith [sq_nonneg (2 * a + b)]
  have hzero : x = 0 := by dsimp [a, b] at ha hb; nlinarith
  simp [b, hzero] at hb

private theorem obstructionQuartic_not_splits : ¬ Polynomial.Splits obstructionQuartic := by
  intro hs
  have hd : Polynomial.natDegree obstructionQuartic = 4 := by
    unfold obstructionQuartic
    compute_degree!
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero
    (Polynomial.degree_ne_of_natDegree_ne (by rw [hd]; norm_num))
  exact obstructionQuartic_no_real_root x hx

private theorem fiber_source_difference_not_splits :
    ¬ Polynomial.Splits
      (sourceMobiusPolynomial (fiberGraph triangleThree) -
        sourceMobiusPolynomial (fiberGraph pathThree)) := by
  rw [fiberTriangle_sourceMobiusPolynomial, fiberPath_sourceMobiusPolynomial]
  have hfactor :
      (2 + 5 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℝ) ^ 3 -
        (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 =
        (Polynomial.X + 1) ^ 2 * obstructionQuartic := by
    unfold obstructionQuartic
    ring
  rw [hfactor]
  intro hs
  have hleft : ((Polynomial.X + 1 : Polynomial ℝ) ^ 2) ≠ 0 := by
    apply pow_ne_zero
    intro heq
    have hev := congrArg (Polynomial.eval (0 : ℝ)) heq
    norm_num at hev
  have hparts := (Polynomial.splits_mul' (f :=
    (Polynomial.X + 1 : Polynomial ℝ) ^ 2) (g := obstructionQuartic)).mp hs
  exact obstructionQuartic_not_splits (hparts.2.resolve_right hleft)

/-- The literal, all-graphs assertion of Conjecture 4.13(2) in arXiv:2608.08692v1.
    The source permits disconnected graphs with the same component count. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V),
    H ≤ G → Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent →
      Polynomial.Splits
        ((-1 : Polynomial ℝ) ^
            (Fintype.card V - Nat.card G.ConnectedComponent) *
          (sourceMobiusPolynomial G - sourceMobiusPolynomial H))

theorem result : ¬ claim := by
  intro h
  have hcomponentsG := fiberGraph_component_count triangleThree_connected
  have hcomponentsH := fiberGraph_component_count pathThree_connected
  have hs := h (Fin 3 × Fin 3) (fiberGraph triangleThree) (fiberGraph pathThree)
    fiberPath_lt_fiberTriangle.le (hcomponentsG.trans hcomponentsH.symm)
  rw [fiberGraph_vertex_count, hcomponentsG] at hs
  norm_num at hs
  exact fiber_source_difference_not_splits hs


end

end D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation

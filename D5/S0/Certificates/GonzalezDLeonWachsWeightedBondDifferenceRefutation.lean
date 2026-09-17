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


end

end D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation

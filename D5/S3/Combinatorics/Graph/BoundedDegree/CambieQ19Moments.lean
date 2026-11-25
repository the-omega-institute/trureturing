/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: The two counts and two order sums on the actual Cambie graph. -/

import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices

/-! The finite moment transports for Question 1.9 of Cambie, Jooken and Wagner
(arXiv:2508.20593v2). -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

open SimpleGraph
open scoped BigOperators

/-- An actual nonempty tree subgraph, with its vertices and edges distinguished. -/
abbrev Subtrees {V : Type} (G : SimpleGraph V) :=
  {H : G.Subgraph // H.coe.IsTree}

private def treeSupport {V : Type} {G : SimpleGraph V} (H : Subtrees G) : ConnectedSets G :=
  ⟨H.val.verts, H.property.connected.mono
    (fun _ _ h => H.val.adj_sub h)⟩

private def treeFiberAsSubgraph (s : ConnectedSets G500) :
    {H : Subtrees G500 // treeSupport H = s} ≃ TreeFiber s.val where
  toFun H := ⟨H.val.val, H.val.property,
    congrArg (fun s : ConnectedSets G500 => s.val) H.property⟩
  invFun H := ⟨⟨H.val, H.property.1⟩, Subtype.ext H.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full tree equivalence uses the actual support projection and the tree fiber over it. -/
noncomputable def allTreesEquiv : Subtrees G500 ≃ Σ c : Configuration, DeletionChoices c :=
  (Equiv.sigmaFiberEquiv treeSupport).symm.trans
    ((Equiv.sigmaCongrLeft' supportEquiv).trans
      (Equiv.sigmaCongrRight fun c => (treeFiberAsSubgraph (supportEquiv.symm c)).trans
        (treeFiberEquiv c)))

private theorem allTreesEquiv_order (c : Configuration) (e : DeletionChoices c) :
    Nat.card ((allTreesEquiv.symm ⟨c, e⟩).val.verts) = c.vertexOrder :=
  treeFiberEquiv_order c e

noncomputable instance : Fintype Configuration := by
  let : Fintype (ConnectedSets G500) := Fintype.ofFinite _
  exact Fintype.ofEquiv (ConnectedSets G500) supportEquiv

noncomputable instance (c : Configuration) : Fintype (DeletionChoices c) := Fintype.ofFinite _

/-- Connected-set count transported to interval and attachment configurations. -/
theorem connectedCount_transport : Nat.card (ConnectedSets G500) = Nat.card Configuration :=
  Nat.card_congr supportEquiv

/-- Connected-set total order transported with the pointwise order law. -/
theorem connectedOrder_transport :
    (letI : Fintype (ConnectedSets G500) := Fintype.ofFinite _
     ∑ S : ConnectedSets G500, Nat.card S.val) =
      ∑ c : Configuration, c.vertexOrder := by
  let : Fintype (ConnectedSets G500) := Fintype.ofFinite _
  exact (Fintype.sum_equiv supportEquiv.symm Configuration.vertexOrder
    (fun S : ConnectedSets G500 => Nat.card S.val)
    (fun c => (supportEquiv_order c).symm)).symm

private theorem tree_order_bounds {V : Type} [Finite V] {G : SimpleGraph V} (H : Subtrees G) :
    Nat.card H.val.verts ∈ Finset.Icc 1 (Nat.card V) := by
  let : Nonempty H.val.verts := H.property.connected.nonempty
  exact Finset.mem_Icc.mpr ⟨Nat.card_pos, Nat.card_le_card_of_injective Subtype.val Subtype.val_injective⟩

private noncomputable def treeOrderIndex {V : Type} [Finite V] {G : SimpleGraph V} (H : Subtrees G) :
    ↥(Finset.Icc 1 (Nat.card V)) :=
  ⟨Nat.card H.val.verts, tree_order_bounds H⟩

private def orderFiberAsSubgraph {V : Type} [Finite V] {G : SimpleGraph V}
    (k : ↥(Finset.Icc 1 (Nat.card V))) :
    {H : Subtrees G // treeOrderIndex H = k} ≃ SubtreesOfOrder G k.val where
  toFun H := ⟨H.val.val, H.val.property, congrArg Subtype.val H.property⟩
  invFun H := ⟨⟨H.val, H.property.1⟩, Subtype.ext H.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def treeOrderEquiv {V : Type} [Finite V] (G : SimpleGraph V) :
    Subtrees G ≃ Σ k : ↥(Finset.Icc 1 (Nat.card V)), SubtreesOfOrder G k.val :=
  (Equiv.sigmaFiberEquiv treeOrderIndex).symm.trans (Equiv.sigmaCongrRight orderFiberAsSubgraph)

private theorem stratified_tree_sum {V : Type} [Finite V] (G : SimpleGraph V)
    (weight : ℕ → ℕ) :
    (letI : Fintype (Subtrees G) := Fintype.ofFinite _
     ∑ H : Subtrees G, weight (Nat.card H.val.verts)) =
      ∑ k ∈ Finset.Icc 1 (Nat.card V), weight k * subtreeCount G k := by
  classical
  let : Fintype (Subtrees G) := Fintype.ofFinite _
  let (k : ↥(Finset.Icc 1 (Nat.card V))) :
      Fintype (SubtreesOfOrder G k.val) := Fintype.ofFinite _
  calc
    _ = ∑ x : Σ k : ↥(Finset.Icc 1 (Nat.card V)), SubtreesOfOrder G k.val, weight x.1.val :=
      Fintype.sum_equiv (treeOrderEquiv G) _ _ fun _ => rfl
    _ = ∑ k : ↥(Finset.Icc 1 (Nat.card V)), weight k.val * subtreeCount G k.val := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k _
      simp [subtreeCount, Nat.card_eq_fintype_card, mul_comm]
    _ = _ := by
      exact Finset.sum_attach (Finset.Icc 1 (Nat.card V)) (fun k => weight k * subtreeCount G k)

private theorem tree_weight_transport (weight : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 (Nat.card Vertex), weight k * subtreeCount G500 k =
      ∑ c : Configuration, weight c.vertexOrder * Nat.card (DeletionChoices c) := by
  classical
  let : Fintype (Subtrees G500) := Fintype.ofFinite _
  rw [← stratified_tree_sum G500 weight]
  calc
    _ = ∑ x : Σ c : Configuration, DeletionChoices c, weight x.1.vertexOrder :=
      (Fintype.sum_equiv allTreesEquiv.symm _ _
        (fun x => congrArg weight (allTreesEquiv_order x.1 x.2).symm)).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp [Nat.card_eq_fintype_card, mul_comm]

/-- The paper's order-stratified subtree count transported to the independent choices. -/
theorem subtreeCount_transport :
    totalSubtreeCount G500 = ∑ c : Configuration, Nat.card (DeletionChoices c) := by
  simpa [totalSubtreeCount] using tree_weight_transport (fun _ => 1)

/-- The paper's order-stratified subtree total order transported with the fiber order law. -/
theorem subtreeOrder_transport :
    totalSubtreeOrder G500 =
      ∑ c : Configuration, c.vertexOrder * Nat.card (DeletionChoices c) :=
  tree_weight_transport id

#print axioms connectedCount_transport
#print axioms connectedOrder_transport
#print axioms subtreeCount_transport
#print axioms subtreeOrder_transport

end D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

/- GID: D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.claim; result=D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.result; claim=D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.claim
   digest: A feasible four by six rectangle has an overloaded original residual component. -/

import D5.S3.Combinatorics.Graph.ActualRectangularResidualBridge
import D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption

/-! An original feasible rectangular realization disproves componentwise residual balance. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualRectangularComponentRefutation

open D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
open D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open scoped BigOperators

/-- Componentwise capacity balance for every actual feasible even rectangle.
Residual identities and capacities are the ones in the actual residual bridge. -/
def claim : Prop := by
  exact ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ (E : Type) [Fintype E] [DecidableEq E]
      (src dst : E → Fin (2 * a) × Fin (2 * b))
      (T : Finset (Fin (2 * a) × Fin (2 * b))),
    (∀ e, squareGrid.Adj
      ((src e).1.val, (src e).2.val) ((dst e).1.val, (dst e).2.val)) →
    Function.Injective (fun z : E × Bool => endpoint src dst z.1 z.2) →
    (∀ e, src e ∉ T ∧ dst e ∉ T) →
    (∀ x ∈ T,
      (((T ∪ Finset.univ.image src) ∪ Finset.univ.image dst).filter
        (fun y => squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val))).card ≤ 1) →
    let κ : Fin (2 * a) × Fin (2 * b) → Fin a × Fin b := fun x =>
      (⟨x.1.val / 2, by have := x.1.isLt; omega⟩,
       ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)
    let t : Fin a × Fin b → ℕ := fun Q => (T.filter (fun x => κ x = Q)).card
    let h : Fin a × Fin b → ℕ := fun Q =>
      (Finset.univ.filter (fun e : E => κ (src e) = Q ∧ κ (dst e) = Q)).card
    let s : Fin a × Fin b → ℕ := fun Q =>
      (Finset.univ.filter (fun e : E =>
        (κ (src e) = Q ∧ κ (dst e) ≠ Q ∧ t (κ (dst e)) = 2) ∨
        (κ (dst e) = Q ∧ κ (src e) ≠ Q ∧ t (κ (src e)) = 2))).card
    let r : Fin a × Fin b → ℕ := fun Q => 2 - (t Q + h Q + s Q)
    let ER := {e : E // κ (src e) ≠ κ (dst e) ∧
      t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2}
    let rs : ER → Fin a × Fin b := fun e => κ (src e.val)
    let rd : ER → Fin a × Fin b := fun e => κ (dst e.val)
    let G := originalGraph rs rd
    let _ : DecidableRel G.Adj := fun u v =>
      inferInstanceAs (Decidable (u ≠ v ∧ ((∃ e : ER, rs e = u ∧ rd e = v) ∨
        ∃ e : ER, rs e = v ∧ rd e = u)))
    ∀ W : G.ConnectedComponent,
      (Finset.univ.filter (fun e : ER => rs e ∈ W.supp)).card ≤
        ∑ Q ∈ Finset.univ.filter (fun Q => Q ∈ W.supp), r Q

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The original residual component on tiles 0,1,2 has two edges and capacity one. -/
theorem result : ¬ claim := by
  intro hall
  let src : Fin 5 → Fin 4 × Fin 6 := ![(0,1), (0,3), (1,1), (1,4), (1,2)]
  let dst : Fin 5 → Fin 4 × Fin 6 := ![(0,2), (0,4), (2,1), (2,4), (1,3)]
  let T : Finset (Fin 4 × Fin 6) := {(0,0), (0,5), (2,0), (2,5), (3,1), (3,4)}
  have hadj : ∀ e, squareGrid.Adj
      ((src e).1.val, (src e).2.val) ((dst e).1.val, (dst e).2.val) := by decide +kernel
  have hinj : Function.Injective (fun z : Fin 5 × Bool => endpoint src dst z.1 z.2) := by decide +kernel
  have hdisjoint : ∀ e, src e ∉ T ∧ dst e ∉ T := by decide +kernel
  have hfeas : ∀ x ∈ T,
      (((T ∪ Finset.univ.image src) ∪ Finset.univ.image dst).filter
        (fun y => squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val))).card ≤ 1 := by decide +kernel
  let κ : Fin 4 × Fin 6 → Fin 2 × Fin 3 := fun x =>
    (⟨x.1.val / 2, by have := x.1.isLt; omega⟩,
     ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)
  let t : Fin 2 × Fin 3 → ℕ := fun Q => (T.filter (fun x => κ x = Q)).card
  let h : Fin 2 × Fin 3 → ℕ := fun Q =>
    (Finset.univ.filter (fun e : Fin 5 => κ (src e) = Q ∧ κ (dst e) = Q)).card
  let s : Fin 2 × Fin 3 → ℕ := fun Q =>
    (Finset.univ.filter (fun e : Fin 5 =>
      (κ (src e) = Q ∧ κ (dst e) ≠ Q ∧ t (κ (dst e)) = 2) ∨
      (κ (dst e) = Q ∧ κ (src e) ≠ Q ∧ t (κ (src e)) = 2))).card
  let r : Fin 2 × Fin 3 → ℕ := fun Q => 2 - (t Q + h Q + s Q)
  let ER := {e : Fin 5 // κ (src e) ≠ κ (dst e) ∧
    t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2}
  have hER : ∀ e : Fin 5,
      (κ (src e) ≠ κ (dst e) ∧ t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2) ↔
        e = 0 ∨ e = 1 := by decide +kernel
  let rs : ER → Fin 2 × Fin 3 := fun e => κ (src e.val)
  let rd : ER → Fin 2 × Fin 3 := fun e => κ (dst e.val)
  let G := originalGraph rs rd
  let : DecidableRel G.Adj := by
    intro u v
    change Decidable (u ≠ v ∧ ((∃ e : ER, rs e = u ∧ rd e = v) ∨
      ∃ e : ER, rs e = v ∧ rd e = u))
    infer_instance
  let W := G.connectedComponentMk (0,0)
  have h01 : G.Adj (0,0) (0,1) := by
    refine ⟨by decide +kernel, Or.inl ?_⟩
    refine ⟨⟨0, (hER 0).2 (Or.inl rfl)⟩, ?_, ?_⟩
    · norm_num [rs, κ, src]
    · norm_num [rd, κ, dst]
  have h12 : G.Adj (0,1) (0,2) := by
    refine ⟨by decide +kernel, Or.inl ?_⟩
    refine ⟨⟨1, (hER 1).2 (Or.inr rfl)⟩, ?_, ?_⟩
    · norm_num [rs, κ, src]
    · norm_num [rd, κ, dst]
  let w : G.Walk (0,0) (0,2) := .cons h01 (.cons h12 .nil)
  have hclosedEdges : ∀ x y, G.Adj x y → s(x,y) ∈ w.edges := by
    intro x y hxy
    rcases hxy.2 with ⟨⟨e, he⟩, hs, hd⟩ | ⟨⟨e, he⟩, hs, hd⟩
    all_goals
      rcases (hER e).1 he with rfl | rfl
      all_goals
        subst x
        subst y
        norm_num [w, rs, rd, κ, src, dst, Sym2.eq_iff]
  have hclosed : ∀ x ∈ w.toSubgraph.verts, ∀ y, G.Adj x y → w.toSubgraph.Adj x y := by
    intro x _hx y hxy
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
      (hclosedEdges x y hxy)
  obtain ⟨W', hW'⟩ := w.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
  have heq : W' = W := SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (hW' ▸ w.start_mem_verts_toSubgraph) ((W.mem_supp_iff (0,0)).2 rfl)
  have hW : ∀ Q, Q ∈ W.supp ↔ Q ∈ ({(0,0), (0,1), (0,2)} : Finset (Fin 2 × Fin 3)) := by
    intro Q
    rw [← heq, ← hW', w.mem_verts_toSubgraph]
    simp [w]
  have hbalance := hall 2 3 (by decide +kernel) (by decide +kernel) (Fin 5) src dst T
    hadj hinj hdisjoint hfeas W
  change (Finset.univ.filter (fun e : ER => rs e ∈ W.supp)).card ≤
    ∑ Q ∈ Finset.univ.filter (fun Q => Q ∈ W.supp), r Q at hbalance
  simp only [hW] at hbalance
  have hC : (Finset.univ.filter (fun e : ER =>
      rs e ∈ ({(0,0), (0,1), (0,2)} : Finset (Fin 2 × Fin 3)))).card = 2 := by decide +kernel
  have hR : (∑ Q ∈ Finset.univ.filter (fun Q =>
      Q ∈ ({(0,0), (0,1), (0,2)} : Finset (Fin 2 × Fin 3))), r Q) = 1 := by decide +kernel
  rw [hC, hR] at hbalance
  exact (by decide : ¬ (2 ≤ 1)) hbalance

end D5.S3.Combinatorics.Graph.Walks.ActualRectangularComponentRefutation

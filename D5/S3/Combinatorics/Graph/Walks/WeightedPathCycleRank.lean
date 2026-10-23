/- GID: D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrarily labelled weighted paths and cycles have ranks determined by parity and the two alternating matching products. -/
import D5.S3.Combinatorics.Graph.Walks.NoEvenCycleRank
import D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
open SimpleGraph Matrix
open scoped BigOperators Classical Fin.NatCast
open D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
universe u v

private theorem matching_count {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) :
    Fintype.card M.verts = 2 * M.coe.edgeFinset.card := by
  classical
  rw [← M.coe.sum_degrees_eq_twice_card_edges]
  rw [SimpleGraph.Subgraph.isMatching_iff_forall_degree] at hM
  have hd : ∀ x : M.verts, M.degree x.val = 1 := fun x => by
    simpa only [Subgraph.degree, Fintype.card_eq_nat_card] using hM x.val x.property
  simp only [Subgraph.coe_degree, hd, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one]

private def pairedMatching {m : ℕ} (G : SimpleGraph (Fin m))
    (hp : pathGraph m ≤ G) : G.Subgraph where
  verts := {i | i.val < 2 * (m / 2)}
  Adj i j := i.val / 2 = j.val / 2 ∧ i ≠ j
  adj_sub := by
    intro i j h
    apply hp
    rw [pathGraph_adj]
    have hn : i.val ≠ j.val := fun he => h.2 (Fin.ext he)
    omega
  edge_vert := by
    intro i j h
    have hn : i.val ≠ j.val := fun he => h.2 (Fin.ext he)
    have hi := i.isLt
    have hj := j.isLt
    change i.val < 2 * (m / 2)
    omega
  symm := ⟨fun i j h => ⟨h.1.symm, h.2.symm⟩⟩

private theorem pairedMatching_isMatching {m : ℕ} (G : SimpleGraph (Fin m))
    (hp : pathGraph m ≤ G) : (pairedMatching G hp).IsMatching := by
  intro i hi
  change i.val < 2 * (m / 2) at hi
  let j : Fin m := ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have := i.isLt
    split_ifs <;> omega⟩
  refine ⟨j, ?_, ?_⟩
  · change i.val / 2 = j.val / 2 ∧ i ≠ j
    dsimp [j]
    split_ifs <;> constructor
    all_goals first | omega | (intro he; have hh := congrArg Fin.val he; dsimp at hh; omega)
  · intro k hk
    change i.val / 2 = k.val / 2 ∧ i ≠ k at hk
    apply Fin.ext
    have hn : i.val ≠ k.val := fun he => hk.2 (Fin.ext he)
    dsimp [j]
    split_ifs <;> omega

private theorem pairedMatching_card {m : ℕ} (G : SimpleGraph (Fin m))
    (hp : pathGraph m ≤ G) : (pairedMatching G hp).coe.edgeFinset.card = m / 2 := by
  let M := pairedMatching G hp
  let e : Fin (2 * (m / 2)) ≃ M.verts := {
    toFun i := ⟨⟨i.val, by have := i.isLt; omega⟩, i.isLt⟩
    invFun i := ⟨i.val.val, i.property⟩
    left_inv i := rfl
    right_inv i := rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_fin, matching_count M (pairedMatching_isMatching G hp)] at hc
  dsimp [M] at hc
  omega

private theorem rank_spanning_path_no_even {m : ℕ} {K : Type*} [Field K] [CharP K 2]
    (A : Matrix (Fin m) (Fin m) K) (hs : A.IsSymm) (hd : ∀ i, A i i = 0)
    (G : SimpleGraph (Fin m)) (he : ∀ i j, G.Adj i j ↔ A i j ≠ 0)
    (hp : pathGraph m ≤ G)
    (hno : ∀ x (p : G.Walk x x), p.IsCycle → ¬ Even p.length) :
    A.rank = 2 * (m / 2) := by
  obtain ⟨M, hm, hr, hmax⟩ := NoEvenCycleRank.rank_eq_twice_maximum_matching A hs hd G he hno
  have hlo := hmax (pairedMatching G hp) (pairedMatching_isMatching G hp)
  rw [pairedMatching_card] at hlo
  have hc := matching_count M hm
  have hle : Fintype.card M.verts ≤ m := by
    simpa using (Fintype.card_subtype_le (fun i => i ∈ M.verts))
  omega

/-- All nonzero edge weights and all finite vertex labels are retained. -/
theorem rank_path {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    {m : ℕ} (A : Matrix V V K) (hs : A.IsSymm) (hd : ∀ i, A i i = 0)
    (e : Fin m ≃ V) (he : ∀ i j, (pathGraph m).Adj i j ↔ A (e i) (e j) ≠ 0) :
    A.rank = 2 * (m / 2) := by
  have hsym : (A.submatrix e e).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hs.apply _ _
  have hr := rank_spanning_path_no_even (A.submatrix e e) hsym (fun i => hd (e i))
    (pathGraph m) he le_rfl (fun x p hc => (isAcyclic_pathGraph m p hc).elim)
  simpa using hr

private theorem cycle_spans_of_connected_isCycles {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hcyc : G.IsCycles)
    {x : V} (p : G.Walk x x) (hp : p.IsCycle) : p.length = Fintype.card V := by
  classical
  have hstep {u v : V} (hu : u ∈ p.toSubgraph.verts) (huv : G.Adj u v) :
      v ∈ p.toSubgraph.verts := by
    exact p.toSubgraph.edge_vert
      ((hp.adj_toSubgraph_iff_of_isCycles hcyc hu v).mpr huv).symm
  have hend {u v : V} (w : G.Walk u v) :
      u ∈ p.toSubgraph.verts → v ∈ p.toSubgraph.verts := by
    induction w with
    | nil => exact id
    | cons h w ih => exact fun hu => ih (hstep hu h)
  apply Walk.IsHamiltonianCycle.length_eq
  apply Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support.mpr
  refine ⟨hp, fun v => ?_⟩
  obtain ⟨w⟩ := hG.preconnected x v
  exact p.mem_verts_toSubgraph.mp
    (hend w (p.mem_verts_toSubgraph.mpr p.start_mem_support))

/-- Every odd cycle has rank one less than its number of vertices. -/
theorem rank_odd_cycle {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    {m : ℕ} (hm : 3 ≤ m) (ho : Odd m) (A : Matrix V V K)
    (hs : A.IsSymm) (hd : ∀ i, A i i = 0)
    (e : Fin m ≃ V) (he : ∀ i j, (cycleGraph m).Adj i j ↔ A (e i) (e j) ≠ 0) :
    A.rank = m - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hcyc : (cycleGraph (k + 3)).IsCycles := by
    intro i _
    rw [SimpleGraph.ncard_neighborSet]
    exact cycleGraph_degree_three_le
  have hno : ∀ x (p : (cycleGraph (k + 3)).Walk x x), p.IsCycle → ¬ Even p.length := by
    intro x p hp heven
    have hl := cycle_spans_of_connected_isCycles (cycleGraph (k + 3))
      connected_cycleGraph_add_one hcyc p hp
    rw [Fintype.card_fin] at hl
    exact (Nat.not_even_iff_odd.mpr ho) (hl ▸ heven)
  have hsym : (A.submatrix e e).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hs.apply _ _
  have hr := rank_spanning_path_no_even (A.submatrix e e) hsym (fun i => hd (e i))
    (cycleGraph (k + 3)) he pathGraph_le_cycleGraph hno
  rw [Matrix.rank_submatrix] at hr
  obtain ⟨j, hj⟩ := ho
  omega

/-- A cycle with its two alternating vertex classes and cyclic successor order. -/
def evenCycleGraph (n : ℕ) : SimpleGraph (Fin (n + 2) ⊕ Fin (n + 2)) where
  Adj
    | Sum.inl i, Sum.inr j => j = i ∨ j = finRotate (n + 2) i
    | Sum.inr j, Sum.inl i => j = i ∨ j = finRotate (n + 2) i
    | _, _ => False
  symm := ⟨by rintro (i | i) (j | j) <;> simp_all⟩
  loopless := ⟨by rintro (i | i) <;> simp⟩

private theorem rotate_ne {n : ℕ} (i : Fin (n + 2)) : finRotate (n + 2) i ≠ i := by
  simp [finRotate_apply]

/-- The products are taken from the actual entries on the two alternating matchings. -/
theorem rank_even_cycle {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    {n : ℕ} (A : Matrix V V K) (hs : A.IsSymm)
    (G : SimpleGraph V) (he : ∀ u v, G.Adj u v ↔ A u v ≠ 0)
    (e : evenCycleGraph n ≃g G) :
    A.rank = if (∏ i, A (e (Sum.inl i)) (e (Sum.inr i))) =
        ∏ i, A (e (Sum.inl i)) (e (Sum.inr (finRotate (n + 2) i)))
      then 2 * n + 2 else 2 * (n + 2) := by
  classical
  let a := fun i => A (e (Sum.inl i)) (e (Sum.inr i))
  let b := fun i => A (e (Sum.inl i)) (e (Sum.inr (finRotate (n + 2) i)))
  have hb : ∀ i, b i ≠ 0 := by
    intro i
    apply (he _ _).mp
    exact e.map_adj_iff.mpr (Or.inr rfl)
  have hcross (i j : Fin (n + 2)) :
      A (e (Sum.inl i)) (e (Sum.inr j)) = cyclicBidiagonal a b i j := by
    by_cases hj : j = i
    · subst j
      simp only [cyclicBidiagonal, if_neg (Ne.symm (rotate_ne i)), ite_true, add_zero, a]
    · by_cases hr : j = finRotate (n + 2) i
      · subst j
        simp only [cyclicBidiagonal, if_neg hj, ite_true, zero_add, b]
      · have hz : A (e (Sum.inl i)) (e (Sum.inr j)) = 0 := by
          apply not_ne_iff.mp
          intro h
          have := e.map_adj_iff.mp ((he _ _).mpr h)
          exact this.elim hj hr
        simp only [cyclicBidiagonal, if_neg hj, if_neg hr, add_zero, hz]
  have heq : A.submatrix e e = Matrix.fromBlocks 0 (cyclicBidiagonal a b)
      (cyclicBidiagonal a b)ᵀ 0 := by
    ext (i | i) (j | j)
    · apply not_ne_iff.mp
      intro h
      have := e.map_adj_iff.mp ((he _ _).mpr h)
      exact this
    · exact hcross i j
    · change A (e (Sum.inr i)) (e (Sum.inl j)) = cyclicBidiagonal a b j i
      rw [hs.apply]
      exact hcross j i
    · apply not_ne_iff.mp
      intro h
      have := e.map_adj_iff.mp ((he _ _).mpr h)
      exact this
  have hr := cyclic_bipartite_rank a b hb
  rw [← heq] at hr
  have hre : (A.submatrix e e).rank = A.rank := by
    convert Matrix.rank_submatrix A e.toEquiv e.toEquiv using 1
  rw [hre] at hr
  simpa only [a, b, Nat.mul_add, Nat.mul_one] using hr

/-- The actual binary adjacency matrix has rank two less than the even-cycle length. -/
theorem rank_even_adjacency {V : Type u} [Fintype V] {n : ℕ}
    (G : SimpleGraph V) (e : evenCycleGraph n ≃g G) :
    (G.adjMatrix (ZMod 2)).rank = 2 * n + 2 := by
  classical
  have he : ∀ u v, G.Adj u v ↔ G.adjMatrix (ZMod 2) u v ≠ 0 := by
    intro u v
    simp
  have h₁ (i : Fin (n + 2)) : G.adjMatrix (ZMod 2) (e (Sum.inl i)) (e (Sum.inr i)) = 1 := by
    have h : (evenCycleGraph n).Adj (Sum.inl i) (Sum.inr i) := Or.inl rfl
    simp only [adjMatrix_apply, e.map_adj_iff.mpr h, ite_true]
  have h₂ (i : Fin (n + 2)) :
      G.adjMatrix (ZMod 2) (e (Sum.inl i)) (e (Sum.inr (finRotate (n + 2) i))) = 1 := by
    have h : (evenCycleGraph n).Adj (Sum.inl i) (Sum.inr (finRotate (n + 2) i)) := Or.inr rfl
    simp only [adjMatrix_apply, e.map_adj_iff.mpr h, ite_true]
  have hr := rank_even_cycle (G.adjMatrix (ZMod 2)) G.isSymm_adjMatrix G he e
  simpa only [h₁, h₂, Finset.prod_const_one, ite_true] using hr

end D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank

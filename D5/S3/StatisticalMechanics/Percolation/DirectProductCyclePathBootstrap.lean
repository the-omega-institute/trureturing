/- GID: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Settles Problem 5 of Bresar, Hedzet and Herrman (arXiv:2403.10957): the 2-neighbour bootstrap percolation number of the direct product of the cycle C_n and the path P_m is n for every n >= 3 and m >= 1; the layer of one path vertex percolates, and the potential 4|A| - 2e(A) never increases, from which every percolating set has at least n vertices. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: one round of 2-neighbour
  percolation never increases `4 |A| - Σ_{v ∈ A} |N(v) ∩ A|` (`pot`, by double counting the
  edges between `A` and the newly infected vertices), and in `C_n × P_m` this potential equals
  `4 n` on the whole vertex set (`Duniv`, from `deg (a, b) = 2 deg_{P_m} b` and
  `Σ_b deg_{P_m} b = 2 (m - 1)`), so every percolating set has at least `n` vertices (`lower`);
  the layer `b = 0` infects the layers `0, …, t` in `t` rounds (`layers`)
admission_basis: open-problem-resolution (issue #10650)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap

open Finset

/-- The direct product `G × H`: `(g, h)` and `(g', h')` are adjacent when `g g'` is an edge of `G`
and `h h'` is an edge of `H`. -/
def dirProd {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

instance {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj]
    [DecidableRel H.Adj] : DecidableRel (dirProd G H).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.1 y.1 ∧ H.Adj x.2 y.2))

instance (m : ℕ) : DecidableRel (SimpleGraph.pathGraph m).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- One round of `r`-neighbour bootstrap percolation: `A` together with every vertex that has at
least `r` neighbours in `A`. -/
def step {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (A : Finset V) : Finset V :=
  A ∪ univ.filter fun v => r ≤ (G.neighborFinset v ∩ A).card

/-- `A` percolates: some number of rounds infects every vertex. -/
def Percolates {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (A : Finset V) : Prop :=
  ∃ t : ℕ, (step G r)^[t] A = univ

/-- `m(G, r)`: the least size of a nonempty percolating set. -/
noncomputable def percolationNumber {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset V, A.Nonempty ∧ A.card = k ∧ Percolates G r A}

/-- Problem 5 of Brešar, Hedžet and Herrman: `m(C_n × P_m, 2) = n` for `n ≥ 3`, `m ≥ 1`. -/
def claim : Prop :=
  ∀ n m : ℕ, 3 ≤ n → 1 ≤ m →
    percolationNumber (dirProd (SimpleGraph.cycleGraph n) (SimpleGraph.pathGraph m)) 2 = n

theorem result : claim := by
  intro n m hn hm
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  set C := SimpleGraph.cycleGraph (k + 3)
  set P := SimpleGraph.pathGraph (l + 1)
  set G := dirProd C P
  -- the potential `4 |A| - Σ_{v ∈ A} |N(v) ∩ A|` never increases
  let D : Finset (Fin (k + 3) × Fin (l + 1)) → ℤ := fun A =>
    ∑ v ∈ A, ((G.neighborFinset v ∩ A).card : ℤ)
  have pot : ∀ A, 4 * ((step G 2 A).card : ℤ) - D (step G 2 A) ≤ 4 * (A.card : ℤ) - D A := by
    intro A
    set B := (univ.filter fun v => 2 ≤ (G.neighborFinset v ∩ A).card) \ A with hB
    have hdisj : Disjoint A B := disjoint_sdiff
    have hstep : step G 2 A = A ∪ B := by
      simp only [step, hB, union_sdiff_self_eq_union]
    have hsplit : ∀ v, (G.neighborFinset v ∩ (A ∪ B)).card =
        (G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ B).card := by
      intro v
      rw [inter_union_distrib_left, card_union_of_disjoint
        (disjoint_of_subset_left inter_subset_right
          (disjoint_of_subset_right inter_subset_right hdisj))]
    have hcount : ∑ v ∈ A, (G.neighborFinset v ∩ B).card =
        ∑ w ∈ B, (G.neighborFinset w ∩ A).card := by
      have h1 : ∀ v, G.neighborFinset v ∩ B = B.bipartiteAbove (fun a b => G.Adj a b) v := by
        intro v
        ext x
        simp [bipartiteAbove, SimpleGraph.mem_neighborFinset, and_comm]
      have h2 : ∀ w, G.neighborFinset w ∩ A = A.bipartiteBelow (fun a b => G.Adj a b) w := by
        intro w
        ext x
        simp [bipartiteBelow, SimpleGraph.mem_neighborFinset, and_comm, G.adj_comm]
      simp only [h1, h2]
      exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    have hB2 : ∀ w ∈ B, 2 ≤ (G.neighborFinset w ∩ A).card := by
      intro w hw
      rw [hB, mem_sdiff, mem_filter] at hw
      exact hw.1.2
    have hsum : B.card • 2 ≤ ∑ w ∈ B, (G.neighborFinset w ∩ A).card :=
      card_nsmul_le_sum B _ 2 hB2
    have hDAB : D (A ∪ B) = D A + ∑ v ∈ A, ((G.neighborFinset v ∩ B).card : ℤ) +
        ∑ v ∈ B, ((G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ B).card : ℤ) := by
      simp only [D]
      rw [sum_union hdisj]
      simp only [hsplit, Nat.cast_add, sum_add_distrib]
    have hBB : 0 ≤ ∑ v ∈ B, ((G.neighborFinset v ∩ B).card : ℤ) :=
      sum_nonneg fun _ _ => Nat.cast_nonneg _
    rw [hstep, hDAB, card_union_of_disjoint hdisj]
    have hcount' : ∑ v ∈ A, ((G.neighborFinset v ∩ B).card : ℤ) =
        ∑ w ∈ B, ((G.neighborFinset w ∩ A).card : ℤ) := by exact_mod_cast hcount
    have hsum' : 2 * (B.card : ℤ) ≤ ∑ w ∈ B, ((G.neighborFinset w ∩ A).card : ℤ) := by
      rw [smul_eq_mul, mul_comm] at hsum
      exact_mod_cast hsum
    rw [sum_add_distrib] at *
    push_cast
    linarith
  have pot_iter : ∀ (A : Finset (Fin (k + 3) × Fin (l + 1))) (t : ℕ),
      4 * (((step G 2)^[t] A).card : ℤ) - D ((step G 2)^[t] A) ≤ 4 * (A.card : ℤ) - D A := by
    intro A t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact (pot _).trans ih
  -- the degrees
  have degC : ∀ a : Fin (k + 3), (C.neighborFinset a).card = 2 := by
    intro a
    exact SimpleGraph.cycleGraph_degree_three_le
  have nbr : ∀ v : Fin (k + 3) × Fin (l + 1),
      G.neighborFinset v = C.neighborFinset v.1 ×ˢ P.neighborFinset v.2 := by
    intro v
    ext w
    rw [mem_product, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    rfl
  have degP : ∀ b : Fin (l + 1), (P.neighborFinset b).card =
      (if b.val < l then 1 else 0) + (if 0 < b.val then 1 else 0) := by
    intro b
    have hsplitP : P.neighborFinset b =
        univ.filter (fun c : Fin (l + 1) => b.val + 1 = c.val) ∪
          univ.filter (fun c : Fin (l + 1) => c.val + 1 = b.val) := by
      ext c
      simp [SimpleGraph.mem_neighborFinset, P, SimpleGraph.pathGraph_adj]
    rw [hsplitP, card_union_of_disjoint (disjoint_filter.2 fun c _ h1 h2 => by omega)]
    congr 1
    · split_ifs with h
      · rw [card_eq_one]
        exact ⟨⟨b.val + 1, by omega⟩, by ext c; simp [Fin.ext_iff, eq_comm]⟩
      · rw [card_eq_zero, filter_eq_empty_iff]
        intro c _ hc
        omega
    · split_ifs with h
      · rw [card_eq_one]
        exact ⟨⟨b.val - 1, by omega⟩, by ext c; simp [Fin.ext_iff]; omega⟩
      · rw [card_eq_zero, filter_eq_empty_iff]
        intro c _ hc
        omega
  have sumP : ∑ b : Fin (l + 1), (P.neighborFinset b).card = 2 * l := by
    simp only [degP, sum_add_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < l then 1 else 0),
      Fin.sum_univ_eq_sum_range (fun i => if 0 < i then 1 else 0), sum_range_succ,
      sum_range_succ']
    simp only [lt_irrefl, if_false, add_zero, Nat.succ_pos, if_true]
    simp only [sum_boole, Nat.cast_id, sum_const, card_range, smul_eq_mul, mul_one, two_mul,
      Nat.add_right_cancel_iff]
    rw [filter_true_of_mem fun x hx => mem_range.1 hx, card_range]
  have Duniv : D univ = 4 * ((k + 3 : ℕ) : ℤ) * l := by
    simp only [D, inter_univ, nbr, card_product, degC]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [← univ_product_univ, sum_product]
    have hP : ∑ b : Fin (l + 1), ((P.neighborFinset b).card : ℤ) = 2 * l := by
      exact_mod_cast sumP
    simp only [← mul_sum, hP, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- lower bound: every percolating set has at least `n` vertices
  have lower : ∀ A : Finset (Fin (k + 3) × Fin (l + 1)), Percolates G 2 A → k + 3 ≤ A.card := by
    rintro A ⟨t, ht⟩
    have h := pot_iter A t
    rw [ht, Duniv, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    have hD : 0 ≤ D A := sum_nonneg fun _ _ => Nat.cast_nonneg _
    push_cast at h
    have : ((k + 3 : ℕ) : ℤ) ≤ A.card := by push_cast; nlinarith
    exact_mod_cast this
  -- upper bound: the layer `b = 0` percolates
  set L : Finset (Fin (k + 3) × Fin (l + 1)) := univ ×ˢ {0} with hL
  have sub_step : ∀ A, A ⊆ step G 2 A := fun A => subset_union_left
  have layers : ∀ t : ℕ, ∀ v : Fin (k + 3) × Fin (l + 1), v.2.val ≤ t → v ∈ (step G 2)^[t] L := by
    intro t
    induction t with
    | zero =>
      intro v hv
      simp only [Function.iterate_zero, id, hL, mem_product, mem_univ, mem_singleton, true_and]
      exact Fin.ext (by rw [Fin.val_zero]; omega)
    | succ t ih =>
      intro v hv
      rw [Function.iterate_succ_apply']
      rcases Nat.lt_or_ge v.2.val (t + 1) with h | h
      · exact sub_step _ (ih v (by omega))
      · have hb : v.2.val = t + 1 := by omega
        set b' : Fin (l + 1) := ⟨t, by omega⟩
        have hsub : C.neighborFinset v.1 ×ˢ {b'} ⊆ G.neighborFinset v ∩ (step G 2)^[t] L := by
          intro w hw
          rw [mem_product, mem_singleton, SimpleGraph.mem_neighborFinset] at hw
          rw [mem_inter, SimpleGraph.mem_neighborFinset]
          refine ⟨⟨hw.1, ?_⟩, ih w (by rw [hw.2])⟩
          rw [hw.2]
          simp [P, SimpleGraph.pathGraph_adj, b']
          omega
        have h2 := card_le_card hsub
        rw [card_product, degC, card_singleton] at h2
        exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h2⟩)
  have Lperc : Percolates G 2 L := by
    exact Exists.intro l (eq_univ_of_forall fun v => layers l v (Nat.lt_succ_iff.1 v.2.isLt))
  have Lcard : L.card = k + 3 := by
    simp [hL]
  have Lne : L.Nonempty := by
    rw [← card_pos, Lcard]
    omega
  have hmem : k + 3 ∈ {j | ∃ A : Finset (Fin (k + 3) × Fin (l + 1)),
      A.Nonempty ∧ A.card = j ∧ Percolates G 2 A} := ⟨L, Lne, Lcard, Lperc⟩
  unfold percolationNumber
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨k + 3, hmem⟩
    rintro _ ⟨A, -, rfl, hA⟩
    exact lower A hA

end D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap

/- GID: D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Answers Question 6 of Alofi and Dukes (arXiv:2411.02667) on the stochastic sandpile model: on the complete bipartite graph K_{m,n} with the sink in the first part, the stochastically recurrent states number at most half of the n^(m-1) m^n stable configurations, exactly half if and only if m = 2. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: every orientation of `K_{m,n}`
  directs exactly `mn` edges into the vertices (`sum_indeg`), so a stochastically recurrent
  configuration carries at least `n (m - 1)` grains (`sto_sum`); the involution
  `c ↦ d - 1 - c` sends `{Σ ≥ n (m - 1)}` into its complement (`ι_sum`, `AB`, `hAB`); for
  `m = 2` an explicit orientation makes every configuration with `n` grains recurrent (`A_sto`),
  and for `m ≥ 3` a configuration with `n (m - 1) - 1` grains lies outside both halves (`hnot`)
admission_basis: open-problem-resolution (issue #10704)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.Sandpiles.StochasticSandpileBipartiteHalf

open Finset

instance {V W : Type} : DecidableRel (completeBipartiteGraph V W).Adj :=
  fun v w => inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

/-- An orientation of `G`: every edge `uv` gets one direction, `O u v = true` meaning `u → v`. -/
def IsOrientation {V : Type} (G : SimpleGraph V) (O : V → V → Bool) : Prop :=
  ∀ u v, G.Adj u v → (O u v = true ↔ O v u = false)

/-- The number of edges directed into `v`. -/
def indeg {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (O : V → V → Bool)
    (v : V) : ℕ :=
  (univ.filter fun u => G.Adj u v ∧ O u v = true).card

/-- Stable configurations: `0 ≤ c(v) < d(v)` on the non-sink vertices. -/
abbrev Stable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : V) : Type :=
  (v : {v // v ≠ s}) → Fin (G.degree v)

/-- `Sto(G)`: the stable configurations compatible with some orientation, that is with
`in_O(v) ≥ d(v) - c(v)` at every non-sink vertex. -/
noncomputable def Sto {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : V) : Finset (Stable G s) := by
  classical
  exact univ.filter fun c => ∃ O : V → V → Bool, IsOrientation G O ∧
    ∀ v : {v // v ≠ s}, G.degree v ≤ indeg G O v + c v

/-- Question 6 of Alofi and Dukes, answered: on `K_{m,n}` with the sink in the first part,
`2 |Sto(K_{m,n})| ≤ n^(m-1) m^n`, with equality exactly when `m = 2`. -/
def claim : Prop :=
  ∀ m n : ℕ, (hm : 2 ≤ m) → 1 ≤ n →
    2 * (Sto (completeBipartiteGraph (Fin m) (Fin n)) (Sum.inl ⟨0, by omega⟩)).card ≤
        n ^ (m - 1) * m ^ n ∧
      (2 * (Sto (completeBipartiteGraph (Fin m) (Fin n)) (Sum.inl ⟨0, by omega⟩)).card =
        n ^ (m - 1) * m ^ n ↔ m = 2)

theorem result : claim := by
  intro m n hm hn
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := ⟨n - 1, by omega⟩
  set G := completeBipartiteGraph (Fin (k + 2)) (Fin (l + 1)) with hG
  set s : Fin (k + 2) ⊕ Fin (l + 1) := Sum.inl ⟨0, by omega⟩ with hs
  -- degrees
  have deg_inl : ∀ a, G.degree (Sum.inl a) = l + 1 := by
    intro a
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : G.neighborFinset (Sum.inl a) = univ.map Function.Embedding.inr := by
      ext w
      cases w <;> simp [G, SimpleGraph.mem_neighborFinset]
    rw [this, card_map, card_univ, Fintype.card_fin]
  have deg_inr : ∀ b, G.degree (Sum.inr b) = k + 2 := by
    intro b
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : G.neighborFinset (Sum.inr b) = univ.map Function.Embedding.inl := by
      ext w
      cases w <;> simp [G, SimpleGraph.mem_neighborFinset]
    rw [this, card_map, card_univ, Fintype.card_fin]
  -- sums over the non-sink vertices, through the total extension by `0` at the sink
  have sub_sum : ∀ f : {v // v ≠ s} → ℕ, ∑ v, f v =
      ∑ v : Fin (k + 2) ⊕ Fin (l + 1), if h : v ≠ s then f ⟨v, h⟩ else 0 := by
    intro f
    rw [Fintype.sum_eq_add_sum_subtype_ne _ s, dif_neg (not_not.2 rfl), zero_add]
    exact sum_congr rfl fun v _ => by rw [dif_pos v.2]
  -- the number of stable configurations
  have card_stable : Fintype.card (Stable G s) = (l + 1) ^ (k + 1) * (k + 2) ^ (l + 1) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    have h := Fintype.prod_eq_mul_prod_subtype_ne (fun v => G.degree v) s
    rw [Fintype.prod_sum_type] at h
    have deg_s : G.degree s = l + 1 := deg_inl _
    simp only [deg_inl, deg_inr, prod_const, card_univ, Fintype.card_fin, deg_s] at h
    have h2 : (l + 1) ^ (k + 2) = (l + 1) * (l + 1) ^ (k + 1) := by ring
    rw [h2, mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos l) h).symm
  -- every orientation directs exactly `mn` edges: `Σ_v in(v) = mn`
  have deg_sum : ∀ v, G.degree v = ∑ u, if G.Adj u v then 1 else 0 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
      card_filter]
    exact sum_congr rfl fun u _ => if_congr (G.adj_comm v u) rfl rfl
  have sum_deg : ∑ v, G.degree v = 2 * ((k + 2) * (l + 1)) := by
    rw [Fintype.sum_sum_type]
    simp only [deg_inl, deg_inr, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have sum_indeg : ∀ O : Fin (k + 2) ⊕ Fin (l + 1) → Fin (k + 2) ⊕ Fin (l + 1) → Bool,
      IsOrientation G O → ∑ v, indeg G O v = (k + 2) * (l + 1) := by
    intro O hO
    have hpair : ∀ u v, ((if G.Adj u v ∧ O u v = true then 1 else 0) +
        (if G.Adj v u ∧ O v u = true then 1 else 0) : ℕ) = if G.Adj u v then 1 else 0 := by
      intro u v
      by_cases h : G.Adj u v
      · have h' : G.Adj v u := h.symm
        have hx := hO u v h
        cases hu : O u v <;> cases hv : O v u <;> simp_all
      · have h' : ¬ G.Adj v u := fun h'' => h h''.symm
        simp [h, h']
    have hin : ∀ v, indeg G O v = ∑ u, if G.Adj u v ∧ O u v = true then 1 else 0 := by
      intro v
      unfold indeg
      rw [card_filter]
    have hS : (∑ v, ∑ u, (if G.Adj u v ∧ O u v = true then 1 else 0 : ℕ)) =
        ∑ v, ∑ u, (if G.Adj v u ∧ O v u = true then 1 else 0 : ℕ) := sum_comm
    have h2 : 2 * ∑ v, indeg G O v = ∑ v, G.degree v := by
      simp only [hin, deg_sum]
      rw [two_mul]
      conv_lhs => arg 2; rw [hS]
      rw [← sum_add_distrib]
      refine sum_congr rfl fun v _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun u _ => hpair u v
    omega
  -- a stochastically recurrent configuration carries at least `n (m - 1)` grains
  have deg_s : G.degree s = l + 1 := deg_inl _
  have sto_sum : ∀ c ∈ Sto G s, (l + 1) * (k + 1) ≤ ∑ v, (c v : ℕ) := by
    intro c hc
    unfold Sto at hc
    obtain ⟨O, hO, hle⟩ := (mem_filter.1 hc).2
    have h1 : ∑ v : {v // v ≠ s}, G.degree v ≤
        ∑ v : {v // v ≠ s}, indeg G O v + ∑ v, (c v : ℕ) := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun v _ => hle v
    have h2 := Fintype.sum_eq_add_sum_subtype_ne (fun v => G.degree v) s
    have h3 := Fintype.sum_eq_add_sum_subtype_ne (fun v => indeg G O v) s
    rw [sum_deg, deg_s] at h2
    rw [sum_indeg O hO] at h3
    nlinarith
  -- the involution `c ↦ d - 1 - c`
  let ι : Stable G s → Stable G s := fun c v => Fin.rev (c v)
  have ι_inv : ∀ c, ι (ι c) = c := fun c => funext fun v => Fin.rev_rev _
  have ι_sum : ∀ c : Stable G s,
      ∑ v, ((ι c) v : ℕ) + ∑ v, (c v : ℕ) = (k + 1) * (2 * l + 1) := by
    intro c
    rw [← sum_add_distrib]
    have hv : ∀ v : {v // v ≠ s}, ((ι c) v : ℕ) + (c v : ℕ) = G.degree v - 1 := by
      intro v
      have := (c v).isLt
      simp only [ι, Fin.val_rev]
      omega
    rw [sum_congr rfl fun v _ => hv v]
    have h := Fintype.sum_eq_add_sum_subtype_ne (fun v => G.degree v - 1) s
    rw [Fintype.sum_sum_type] at h
    simp only [deg_inl, deg_inr, deg_s, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
    have : (k + 2) * (l + 1 - 1) + (l + 1) * (k + 2 - 1) = l + 1 - 1 + (k + 1) * (2 * l + 1) := by
      rw [show k + 2 - 1 = k + 1 by omega, show l + 1 - 1 = l by omega]
      ring
    omega
  -- the sets `{Σ ≥ n (m - 1)}` and `{Σ + n (m - 1) ≤ D}` exchanged by the involution
  set A := univ.filter fun c : Stable G s => (l + 1) * (k + 1) ≤ ∑ v, (c v : ℕ) with hA
  set B := univ.filter fun c : Stable G s => ∑ v, (c v : ℕ) + (l + 1) * (k + 1) ≤
    (k + 1) * (2 * l + 1) with hB
  have hAB : Disjoint A B := by
    rw [hA, hB, disjoint_filter]
    intro c _ h1 h2
    nlinarith
  have AB : A.card ≤ B.card := by
    refine card_le_card_of_injOn ι ?_ ?_
    · intro c hc
      have h1 := (mem_filter.1 hc).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      have := ι_sum c
      omega
    · intro c _ c' _ h
      rw [← ι_inv c, ← ι_inv c']
      exact congrArg ι h
  have hsum_AB : A.card + B.card ≤ (l + 1) ^ (k + 1) * (k + 2) ^ (l + 1) := by
    rw [← card_union_of_disjoint hAB, ← card_stable]
    exact card_le_univ _
  have StoA : Sto G s ⊆ A := fun c hc => mem_filter.2 ⟨mem_univ _, sto_sum c hc⟩
  have le_half : 2 * (Sto G s).card ≤ (l + 1) ^ (k + 1) * (k + 2) ^ (l + 1) := by
    have := card_le_card StoA
    omega
  refine ⟨le_half, ?_⟩
  have BA : B.card ≤ A.card := by
    refine card_le_card_of_injOn ι ?_ ?_
    · intro c hc
      have h1 := (mem_filter.1 hc).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      have := ι_sum c
      omega
    · intro c _ c' _ h
      rw [← ι_inv c, ← ι_inv c']
      exact congrArg ι h
  rcases k with _ | k
  · -- `m = 2`: every configuration with at least `n` grains is recurrent, and the involution
    -- exchanges `{Σ ≥ n}` and `{Σ ≤ n - 1}`
    simp only [iff_true]
    have hne1 : (Sum.inl 1 : Fin (0 + 2) ⊕ Fin (l + 1)) ≠ s := by
      simp [hs]
    have hneb : ∀ b : Fin (l + 1), (Sum.inr b : Fin (0 + 2) ⊕ Fin (l + 1)) ≠ s := by
      simp [hs]
    have A_sto : A ⊆ Sto G s := by
      intro c hc
      have hsum := (mem_filter.1 hc).2
      set ca : ℕ := (c ⟨Sum.inl 1, hne1⟩ : ℕ) with hca
      set cb : Fin (l + 1) → ℕ := fun b => (c ⟨Sum.inr b, hneb b⟩ : ℕ) with hcb
      have cb_le : ∀ b, cb b ≤ 1 := by
        intro b
        have h := (c ⟨Sum.inr b, hneb b⟩).isLt
        have h' : G.degree (Sum.inr b) = 0 + 2 := deg_inr b
        simp only [hcb]
        change _ < G.degree (Sum.inr b) at h
        omega
      have sum_eq : ∑ v, (c v : ℕ) = ca + ∑ b, cb b := by
        rw [sub_sum (fun v => (c v : ℕ)), Fintype.sum_sum_type, Fin.sum_univ_two]
        have h0 : ¬ ((Sum.inl 0 : Fin (0 + 2) ⊕ Fin (l + 1)) ≠ s) := by simp [hs]
        rw [dif_neg h0, dif_pos hne1, zero_add]
        exact congrArg (ca + ·) (sum_congr rfl fun b _ => dif_pos (hneb b))
      let O : Fin (0 + 2) ⊕ Fin (l + 1) → Fin (0 + 2) ⊕ Fin (l + 1) → Bool := fun u v =>
        match u, v with
        | Sum.inl i, Sum.inr b => if i = 0 then true else decide (cb b = 0)
        | Sum.inr b, Sum.inl i => if i = 0 then false else decide (cb b ≠ 0)
        | _, _ => false
      unfold Sto
      refine mem_filter.2 ⟨mem_univ _, O, ?_, ?_⟩
      · intro u v huv
        rcases u with i | b <;> rcases v with j | b'
        · simp [G] at huv
        · by_cases hi : i = 0 <;> simp [O, hi]
        · by_cases hj : j = 0 <;> simp [O, hj]
        · simp [G] at huv
      · rintro ⟨v, hv⟩
        rcases v with i | b
        · have hi : i = 1 := by
            fin_cases i
            · simp [hs] at hv
            · rfl
          subst hi
          have hin : indeg G O (Sum.inl 1) = ∑ b, cb b := by
            unfold indeg
            rw [card_filter, Fintype.sum_sum_type]
            simp only [G, completeBipartiteGraph_adj, Sum.isLeft_inl, Sum.isRight_inl,
              Sum.isLeft_inr, Sum.isRight_inr, Bool.false_eq_true, and_false, or_false,
              and_true, if_false, sum_const_zero, zero_add, O]
            refine sum_congr rfl fun b _ => ?_
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (cb_le b) with h0 | h0 <;> simp [h0]
          change G.degree (Sum.inl 1) ≤ indeg G O (Sum.inl 1) + ca
          rw [deg_inl, hin]
          omega
        · have hin : indeg G O (Sum.inr b) = 1 + if cb b = 0 then 1 else 0 := by
            unfold indeg
            rw [card_filter, Fintype.sum_sum_type, Fin.sum_univ_two]
            simp only [G, completeBipartiteGraph_adj, Sum.isLeft_inl, Sum.isRight_inl,
              Sum.isLeft_inr, Sum.isRight_inr, Bool.false_eq_true, and_false, or_false,
              and_true, true_and, if_false, sum_const_zero, add_zero, O]
            by_cases h0 : cb b = 0 <;> simp [h0]
          change G.degree (Sum.inr b) ≤ indeg G O (Sum.inr b) + cb b
          rw [deg_inr, hin]
          have := cb_le b
          split_ifs <;> omega
    have hStoA : Sto G s = A := Subset.antisymm StoA A_sto
    have hunion : A ∪ B = univ := by
      apply eq_univ_of_forall
      intro c
      rw [mem_union, hA, hB, mem_filter, mem_filter]
      simp only [mem_univ, true_and]
      omega
    have := card_union_of_disjoint hAB
    rw [hunion, card_univ, card_stable] at this
    rw [hStoA, show (l + 1) ^ (0 + 2 - 1) = (l + 1) ^ (0 + 1) from rfl]
    omega
  · -- `m ≥ 3`: a configuration with `n (m - 1) - 1` grains lies in neither set
    simp only [show ¬ (k + 1 + 2 = 2) by omega, iff_false]
    let c0 : Stable G s := fun v =>
      match v with
      | ⟨Sum.inl a, _⟩ => ⟨0, by change 0 < G.degree (Sum.inl a); rw [deg_inl]; omega⟩
      | ⟨Sum.inr b, _⟩ => ⟨if b.val = 0 then k + 1 else k + 2, by
          change _ < G.degree (Sum.inr b)
          rw [deg_inr]
          split_ifs <;> omega⟩
    have hc0 : ∑ v, (c0 v : ℕ) = (k + 1) + l * (k + 2) := by
      rw [sub_sum (fun v => (c0 v : ℕ)), Fintype.sum_sum_type]
      have h1 : ∑ a : Fin (k + 1 + 2), (if h : (Sum.inl a : Fin (k + 1 + 2) ⊕ Fin (l + 1)) ≠ s
          then (c0 ⟨Sum.inl a, h⟩ : ℕ) else 0) = 0 :=
        sum_eq_zero fun a _ => by split_ifs <;> rfl
      have h2 : ∑ b : Fin (l + 1), (if h : (Sum.inr b : Fin (k + 1 + 2) ⊕ Fin (l + 1)) ≠ s
          then (c0 ⟨Sum.inr b, h⟩ : ℕ) else 0) =
          ∑ b : Fin (l + 1), if b.val = 0 then k + 1 else k + 2 :=
        sum_congr rfl fun b _ => by rw [dif_pos (by simp [hs])]
      rw [h1, h2, zero_add, Fin.sum_univ_succ]
      simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false, sum_const,
        card_univ, Fintype.card_fin, smul_eq_mul]
    have hnot : c0 ∉ A ∪ B := by
      rw [mem_union, hA, hB, mem_filter, mem_filter, hc0]
      push Not
      constructor <;> intro _ <;> nlinarith
    have hlt := card_lt_univ_of_notMem hnot
    rw [card_union_of_disjoint hAB, card_stable] at hlt
    have hSA := card_le_card StoA
    have h2 : 2 * (Sto G s).card < (l + 1) ^ (k + 1 + 1) * (k + 1 + 2) ^ (l + 1) :=
      calc 2 * (Sto G s).card ≤ A.card + B.card := by omega
        _ < _ := hlt
    rw [show (l + 1) ^ (k + 1 + 2 - 1) = (l + 1) ^ (k + 1 + 1) from rfl]
    exact h2.ne

end D5.S3.StatisticalMechanics.Sandpiles.StochasticSandpileBipartiteHalf

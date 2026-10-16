/- GID: D5/S3/Combinatorics/Graph/Walks/WeightedVertexProducts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/WeightedVertexProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: On connected graphs over commutative groups with surjective squaring, vertex products are solvable exactly when every even closed walk balances. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.Walks.WeightedVertexProducts
open SimpleGraph

variable {V A : Type*} [CommGroup A] {G : SimpleGraph V}

/-- Alternating edge product, retaining every traversal with its multiplicity. -/
def alpha (w : Sym2 V → A) {u v : V} (p : G.Walk u v) : A :=
  (p.edges.map w).alternatingProd

private theorem alpha_append (w : Sym2 V → A) {u v z : V}
    (p : G.Walk u v) (q : G.Walk v z) :
    alpha w (p.append q) = alpha w p * alpha w q ^ (-1 : ℤ) ^ p.length := by
  simp [alpha, Walk.edges_append, List.map_append, List.alternatingProd_append]

private theorem alpha_reverse (w : Sym2 V → A) {u v : V} (p : G.Walk u v) :
    alpha w p.reverse = alpha w p ^ (-1 : ℤ) ^ (p.length + 1) := by
  simp [alpha, Walk.edges_reverse, List.map_reverse, List.alternatingProd_reverse]

private theorem alpha_of_vertex_products (w : Sym2 V → A) (b : V → A)
    (hb : ∀ u v, G.Adj u v → b u * b v = w s(u, v))
    {u v : V} (p : G.Walk u v) :
    alpha w p = b u * b v ^ (-((-1 : ℤ) ^ p.length)) := by
  induction p with
  | nil => simp [alpha]
  | @cons u v z h p ih =>
    simp only [alpha, Walk.edges_cons, List.map_cons, List.alternatingProd_cons] at *
    rw [← hb u v h, ih]
    simp only [Walk.length_cons, pow_succ, mul_neg, mul_one, neg_neg]
    rcases neg_one_pow_eq_or (R := ℤ) p.length with hp | hp <;>
      simp [hp, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private theorem path_value_eq (w : Sym2 V → A) (r : V) (a : A)
    (hc : ∀ p : G.Walk r r,
      alpha w p = a * a ^ (-((-1 : ℤ) ^ p.length)))
    {v : V} (p q : G.Walk r v) :
    (a / alpha w p) ^ (-1 : ℤ) ^ p.length =
      (a / alpha w q) ^ (-1 : ℤ) ^ q.length := by
  have h := hc (p.append q.reverse)
  rw [alpha_append, alpha_reverse] at h
  simp only [Walk.length_append, Walk.length_reverse, pow_add, pow_succ] at h
  rcases neg_one_pow_eq_or (R := ℤ) p.length with hp | hp <;>
    rcases neg_one_pow_eq_or (R := ℤ) q.length with hq | hq <;>
    simp [hp, hq, ← div_eq_mul_inv] at h ⊢
  · exact div_eq_one.mp h
  · apply div_eq_div_iff_mul_eq_mul.mpr
    simpa [mul_comm] using h.symm
  · apply div_eq_div_iff_mul_eq_mul.mpr
    simpa [mul_comm] using h
  · exact div_eq_one.mp h

/-- Over a group admitting square roots, even closed walks are the complete obstruction
    to factoring symmetric edge weights into products of vertex weights. -/
theorem vertex_products_iff_even_closed_walks (w : Sym2 V → A)
    (hsquare : Function.Surjective (fun a : A => a * a)) (hG : G.Connected) :
    (∃ b : V → A, ∀ u v, G.Adj u v → b u * b v = w s(u, v)) ↔
      ∀ (u : V) (p : G.Walk u u), Even p.length → alpha w p = 1 := by
  classical
  constructor
  · rintro ⟨b, hb⟩ u p hp
    simpa [hp.neg_one_pow] using alpha_of_vertex_products w b hb p
  · intro heven
    let r : V := Classical.choice hG.nonempty
    have ha : ∃ a : A, ∀ p : G.Walk r r,
        alpha w p = a * a ^ (-((-1 : ℤ) ^ p.length)) := by
      by_cases hall : ∀ p : G.Walk r r, Even p.length
      · refine ⟨1, fun p => ?_⟩
        simp [heven r p (hall p)]
      · push Not at hall
        obtain ⟨q, hq⟩ := hall
        have hqo : Odd q.length := Nat.not_even_iff_odd.mp hq
        obtain ⟨a, ha⟩ := hsquare (alpha w q)
        refine ⟨a, fun p => ?_⟩
        by_cases hp : Even p.length
        · simp [hp.neg_one_pow, heven r p hp]
        · have hpo : Odd p.length := Nat.not_even_iff_odd.mp hp
          have hlen : Even (q.append p.reverse).length := by
            simpa only [Walk.length_append, Walk.length_reverse] using hqo.add_odd hpo
          have h := heven r (q.append p.reverse) hlen
          rw [alpha_append, alpha_reverse] at h
          have hsign : (-1 : ℤ) ^ (p.length + 1) = 1 :=
            (hpo.add_odd (by decide : Odd 1)).neg_one_pow
          simp only [hqo.neg_one_pow, hsign, zpow_one, zpow_neg_one] at h
          have hi : alpha w p = alpha w q := (eq_of_mul_inv_eq_one h).symm
          simp [hpo.neg_one_pow, hi, ← ha]
    obtain ⟨a, ha⟩ := ha
    let P : ∀ v : V, G.Walk r v := fun v => (hG.preconnected r v).some
    let b : V → A := fun v => (a / alpha w (P v)) ^ (-1 : ℤ) ^ (P v).length
    refine ⟨b, fun u v huv => ?_⟩
    let e : G.Walk u v := huv.toWalk
    have hv := path_value_eq w r a ha ((P u).append e) (P v)
    change b u * b v = _
    dsimp [b]
    rw [← hv, alpha_append]
    simp only [e, Adj.toWalk, alpha, Walk.edges_cons, Walk.edges_nil,
      List.map_cons, List.map_nil, List.alternatingProd_singleton, Walk.length_append,
      Walk.length_cons, Walk.length_nil, zero_add, pow_add, pow_one]
    rcases neg_one_pow_eq_or (R := ℤ) (P u).length with hp | hp <;>
      simp [hp]

private theorem tree_vertex_products (w : Sym2 V → A) (hT : G.IsTree) :
    ∃ b : V → A, ∀ u v, G.Adj u v → b u * b v = w s(u, v) := by
  classical
  let r : V := Classical.choice hT.connected.nonempty
  choose P hP huniq using hT.existsUnique_path r
  let b : V → A := fun v => (alpha w (P v)) ^ (-((-1 : ℤ) ^ (P v).length))
  have step {u v : V} (h : G.Adj u v) (he : P v = (P u).concat h) :
      b u * b v = w s(u, v) := by
    dsimp [b]
    rw [he, Walk.concat_eq_append, alpha_append]
    simp only [alpha, Walk.edges_cons, Walk.edges_nil, List.map_cons, List.map_nil,
      List.alternatingProd_singleton, Walk.length_append, Walk.length_cons,
      Walk.length_nil, zero_add, pow_add, pow_one, mul_neg, mul_one, neg_neg]
    rcases neg_one_pow_eq_or (R := ℤ) (P u).length with hp | hp <;>
      simp [hp, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  refine ⟨b, fun u v h => ?_⟩
  by_cases hu : u ∈ (P v).support
  · exact step h (hT.isAcyclic.path_concat (hP u) (hP v) h hu)
  · have hv := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (hP u) (hP v) h hu
    simpa [mul_comm, Sym2.eq_swap] using
      step h.symm (hT.isAcyclic.path_concat (hP v) (hP u) h.symm hv)

/-- In a bipartite graph, balancing all simple cycles and balancing the fundamental
    cycles of any specified spanning tree are each equivalent to vertex factorization. -/
theorem bipartite_cycle_tree_criteria (w : Sym2 V → A) (hG : G.Colorable 2)
    (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree) :
    let Sol := ∃ b : V → A, ∀ u v, G.Adj u v → b u * b v = w s(u, v)
    let Cycles := ∀ (u : V) (p : G.Walk u u), p.IsCycle → alpha w p = 1
    let Fundamental := ∀ (u v : V) (h : G.Adj u v), ¬ T.Adj u v →
      ∀ p : T.Walk v u, p.IsPath → alpha w (Walk.cons h (p.mapLe hTG)) = 1
    (Sol ↔ Cycles) ∧ (Sol ↔ Fundamental) := by
  classical
  dsimp only
  have even := SimpleGraph.two_colorable_iff_forall_loop_even.mp hG
  have necessity (b : V → A)
      (hb : ∀ u v, G.Adj u v → b u * b v = w s(u, v))
      (u : V) (p : G.Walk u u) : alpha w p = 1 := by
    simpa [(even u p).neg_one_pow] using alpha_of_vertex_products w b hb p
  have sufficiency
      (hf : ∀ (u v : V) (h : G.Adj u v), ¬ T.Adj u v →
        ∀ p : T.Walk v u, p.IsPath → alpha w (Walk.cons h (p.mapLe hTG)) = 1) :
      ∃ b : V → A, ∀ u v, G.Adj u v → b u * b v = w s(u, v) := by
    obtain ⟨b, hb⟩ := tree_vertex_products w hT
    refine ⟨b, fun u v h => ?_⟩
    by_cases ht : T.Adj u v
    · exact hb u v ht
    · obtain ⟨p, hp, _⟩ := hT.existsUnique_path v u
      have hbal := hf u v h ht p hp
      have he := even u (Walk.cons h (p.mapLe hTG))
      have ho : Odd p.length := by
        simpa only [Walk.length_cons, Walk.length_mapLe, Nat.even_add_one,
          Nat.not_even_iff_odd] using he
      have hval := alpha_of_vertex_products w b hb p
      simp only [ho.neg_one_pow, neg_neg, zpow_one] at hval
      simp only [alpha, Walk.edges_cons, Walk.edges_mapLe_eq_edges, List.map_cons,
        List.alternatingProd_cons] at hbal
      change w s(u, v) / alpha w p = 1 at hbal
      have hw := div_eq_one.mp hbal
      simpa [mul_comm] using hval.symm.trans hw.symm
  have cyc_to_fund
      (hc : ∀ (u : V) (p : G.Walk u u), p.IsCycle → alpha w p = 1) :
      ∀ (u v : V) (h : G.Adj u v), ¬ T.Adj u v →
        ∀ p : T.Walk v u, p.IsPath → alpha w (Walk.cons h (p.mapLe hTG)) = 1 := by
    intro u v h hn p hp
    apply hc
    apply (Walk.cons_isCycle_iff _ _).mpr
    refine ⟨hp.mapLe hTG, ?_⟩
    rw [Walk.edges_mapLe_eq_edges]
    intro he
    exact hn (T.mem_edgeSet.mp (p.edges_subset_edgeSet he))
  constructor
  · constructor
    · rintro ⟨b, hb⟩ u p _
      exact necessity b hb u p
    · exact fun hc => sufficiency (cyc_to_fund hc)
  · constructor
    · rintro ⟨b, hb⟩ u v h _ p _
      exact necessity b hb u _
    · exact sufficiency

end D5.S3.Combinatorics.Graph.Walks.WeightedVertexProducts

/- GID: D5/S3/Combinatorics/Graph/LinearForests/BipartiteCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/BipartiteCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Color-preserving saturation of the smaller part of finite bipartite linear forests. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Preorder.Finite

/-! Same-carrier bipartite linear-forest completion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset SimpleGraph
namespace D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion

private lemma partition_bipartite {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (A B : Finset α)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hd : Disjoint A B) (hc : A ∪ B = univ) :
    G.IsBipartiteWith (A : Set α) (B : Set α) := by
  classical
  refine ⟨by simpa using hd, ?_⟩
  intro x y hxy
  have hx : x ∈ A ∨ x ∈ B := by simpa [← hc] using (mem_univ x)
  have hy : y ∈ A ∨ y ∈ B := by simpa [← hc] using (mem_univ y)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact False.elim (((G.isIndepSet_iff).mp hA hx hy hxy.ne) hxy)
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact False.elim (((G.isIndepSet_iff).mp hB hx hy hxy.ne) hxy)

private lemma induced_partition {α : Type*}
    (G : SimpleGraph α) (A B : Finset α) (s : Set α)
    (hp : G.IsBipartiteWith (A : Set α) (B : Set α)) :
    (G.induce s).IsBipartiteWith (A.subtype (· ∈ s) : Set s)
      (B.subtype (· ∈ s) : Set s) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hp.disjoint (by simpa using hx) (by simpa using hy)
  · intro x y hxy
    rcases hp.mem_of_adj hxy with h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
    · exact Or.inr ⟨by simpa using h.1, by simpa using h.2⟩

private lemma closed_degree_sums {α : Type*} [Fintype α]
    (G : SimpleGraph α) (A B : Finset α) (s : Set α)
    (hp : G.IsBipartiteWith (A : Set α) (B : Set α))
    (hs : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s) :
    (∑ x ∈ A.filter (· ∈ s), G.degree x) =
      ∑ x ∈ B.filter (· ∈ s), G.degree x := by
  classical
  have he := isBipartiteWith_sum_degrees_eq (induced_partition G A B s hp)
  have hd (x : s) : (G.induce s).degree x = G.degree x :=
    degree_induce_of_neighborSet_subset (fun y hy => hs x x.property y hy)
  calc
    _ = ∑ x ∈ A.subtype (· ∈ s), G.degree x.val :=
      (sum_subtype_eq_sum_filter (fun x : α => G.degree x)).symm
    _ = ∑ x ∈ B.subtype (· ∈ s), G.degree x.val := by simpa only [hd] using he
    _ = _ := sum_subtype_eq_sum_filter (fun x : α => G.degree x)

private lemma deficient_component_balance {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (A B : Finset α)
    (hp : G.IsBipartiteWith (A : Set α) (B : Set α)) (hc : A ∪ B = univ)
    (ha : G.IsAcyclic) (hd : ∀ x, G.degree x ≤ 2)
    {u : α} (hu : u ∈ A) (hdu : G.degree u < 2) :
    (B.filter (· ∈ (G.connectedComponentMk u).supp)).card ≤
      (A.filter (· ∈ (G.connectedComponentMk u).supp)).card := by
  classical
  let c := G.connectedComponentMk u
  let s := c.supp
  let J := G.induce s
  have hclosed : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s := by
    intro x hx y hxy
    exact (c.mem_supp_congr_adj hxy).mp hx
  have hdeg (x : s) : J.degree x = G.degree x :=
    degree_induce_of_neighborSet_subset (fun y hy => hclosed x x.property y hy)
  have he := isBipartiteWith_sum_degrees_eq_card_edges (induced_partition G A B s hp)
  have he' : (∑ x ∈ A.filter (· ∈ s), G.degree x) = J.edgeFinset.card := by
    change (∑ x ∈ A.subtype (· ∈ s), J.degree x) = J.edgeFinset.card at he
    calc
      _ = ∑ x ∈ A.subtype (· ∈ s), G.degree x.val :=
        (sum_subtype_eq_sum_filter (fun x : α => G.degree x)).symm
      _ = _ := by simpa only [hdeg] using he
  have htree : J.IsTree := ha.isTree_connectedComponent c
  have hcard := htree.card_edgeFinset
  have hparts : (A.subtype (· ∈ s)) ∪ (B.subtype (· ∈ s)) = (univ : Finset s) := by
    ext x
    have hx : x.val ∈ A ∨ x.val ∈ B := by simpa [← hc] using (mem_univ x.val)
    simpa using hx
  have hdis : Disjoint (A.subtype (· ∈ s)) (B.subtype (· ∈ s)) := by
    exact disjoint_coe.mp (induced_partition G A B s hp).disjoint
  have hv : (A.filter (· ∈ s)).card + (B.filter (· ∈ s)).card = Fintype.card s := by
    simpa only [card_union_of_disjoint hdis, card_subtype, card_univ] using congrArg card hparts
  have hlt : (∑ x ∈ A.filter (· ∈ s), G.degree x) < 2 * (A.filter (· ∈ s)).card := by
    calc
      _ < ∑ _x ∈ A.filter (· ∈ s), 2 := by
        apply sum_lt_sum
        · intro x hx; exact hd x
        · exact ⟨u, by simp [s, c, hu], hdu⟩
      _ = _ := by simp [Nat.mul_comm]
  change (B.filter (· ∈ s)).card ≤ (A.filter (· ∈ s)).card
  omega

private lemma opposite_deficient_vertex {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (A B : Finset α)
    (hp : G.IsBipartiteWith (A : Set α) (B : Set α)) (hc : A ∪ B = univ)
    (ha : G.IsAcyclic) (hd : ∀ x, G.degree x ≤ 2) (hab : A.card < B.card)
    {u : α} (hu : u ∈ A) (hdu : G.degree u < 2) :
    ∃ v ∈ B, G.degree v < 2 ∧ ¬G.Reachable u v := by
  classical
  let c := G.connectedComponentMk u
  let s := c.supp
  have hclosed : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s := by
    intro x hx y hxy
    exact (c.mem_supp_congr_adj hxy).mp hx
  have hin := deficient_component_balance G A B hp hc ha hd hu hdu
  change (B.filter (· ∈ s)).card ≤ (A.filter (· ∈ s)).card at hin
  have hca := A.card_filter_add_card_filter_not (· ∈ s)
  have hcb := B.card_filter_add_card_filter_not (· ∈ s)
  have hout : (A.filter (· ∉ s)).card < (B.filter (· ∉ s)).card := by omega
  have hsum := closed_degree_sums G A B s hp hclosed
  have htotal := isBipartiteWith_sum_degrees_eq hp
  have hsa := sum_filter_add_sum_filter_not A (· ∈ s) (fun x => G.degree x)
  have hsb := sum_filter_add_sum_filter_not B (· ∈ s) (fun x => G.degree x)
  have heq : (∑ x ∈ A.filter (· ∉ s), G.degree x) =
      ∑ x ∈ B.filter (· ∉ s), G.degree x := by omega
  have hlt : (∑ x ∈ B.filter (· ∉ s), G.degree x) <
      ∑ _x ∈ B.filter (· ∉ s), 2 := by
    calc
      _ = ∑ x ∈ A.filter (· ∉ s), G.degree x := heq.symm
      _ ≤ ∑ _x ∈ A.filter (· ∉ s), 2 := sum_le_sum (fun x _ => hd x)
      _ = 2 * (A.filter (· ∉ s)).card := by simp [Nat.mul_comm]
      _ < 2 * (B.filter (· ∉ s)).card := by omega
      _ = _ := by simp [Nat.mul_comm]
  obtain ⟨v, hv, hdv⟩ := exists_lt_of_sum_lt hlt
  refine ⟨v, (mem_filter.mp hv).1, hdv, ?_⟩
  intro huv
  apply (mem_filter.mp hv).2
  change G.connectedComponentMk v = G.connectedComponentMk u
  exact ConnectedComponent.sound huv.symm

private lemma added_edge_degree {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {u v : α} (hne : u ≠ v) (hn : ¬G.Adj u v) (x : α) :
    (G ⊔ edge u v).degree x = G.degree x + if x = u ∨ x = v then 1 else 0 := by
  classical
  have hn' : Disjoint G (edge u v) := (G.disjoint_edge).mpr hn
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_sup_of_disjoint x hn', card_disjUnion,
    card_neighborFinset_eq_degree]
  have he : (edge u v).neighborFinset x =
      if x = u then {v} else if x = v then {u} else ∅ := by
    ext y
    by_cases hx : x = u <;> by_cases hy : x = v <;>
      simp_all [mem_neighborFinset, edge_adj]
  rw [he]
  by_cases hx : x = u <;> by_cases hy : x = v <;> simp_all

/-- Every finite bipartite linear forest with a strict surplus in B has a
same-carrier, color-preserving extension saturating all vertices in A. -/
theorem exists_saturating_extension {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (A B : Finset α)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hp : Disjoint A B) (hc : A ∪ B = univ)
    (ha : G.IsAcyclic) (hd : ∀ x, G.degree x ≤ 2) (hab : A.card < B.card) :
    ∃ H : SimpleGraph α, G ≤ H ∧ H.IsAcyclic ∧ (∀ x, H.degree x ≤ 2) ∧
      H.IsIndepSet (A : Set α) ∧ H.IsIndepSet (B : Set α) ∧
      ∀ u ∈ A, H.degree u = 2 := by
  classical
  let P := fun H : SimpleGraph α => H.IsAcyclic ∧ (∀ x, H.degree x ≤ 2) ∧
    H.IsBipartiteWith (A : Set α) (B : Set α)
  have hP : P G := ⟨ha, hd, partition_bipartite G A B hA hB hp hc⟩
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal hP
  have hH := hmax.prop
  refine ⟨H, hGH, hH.1, hH.2.1, ?_, ?_, ?_⟩
  · intro x hx y hy _hne hxy
    exact Set.disjoint_left.mp hH.2.2.disjoint hy
      (hH.2.2.mem_of_mem_adj hx hxy)
  · intro x hx y hy _hne hxy
    exact Set.disjoint_left.mp hH.2.2.disjoint
      (hH.2.2.symm.mem_of_mem_adj hx hxy) hy
  · intro u hu
    by_contra hdu
    have hdu' : H.degree u < 2 := by have := hH.2.1 u; omega
    obtain ⟨v, hv, hdv, hnr⟩ :=
      opposite_deficient_vertex H A B hH.2.2 hc hH.1 hH.2.1 hab hu hdu'
    have hne : u ≠ v := by
      intro he; subst v
      exact disjoint_left.mp hp hu hv
    have hn : ¬H.Adj u v := fun huv => hnr huv.reachable
    have hK : P (H ⊔ edge u v) := by
      refine ⟨hH.1.sup_edge_of_not_reachable hnr, ?_, ?_⟩
      · intro x
        have hdx : (H ⊔ edge u v).degree x =
            H.degree x + if x = u ∨ x = v then 1 else 0 := by
          simpa only [← ncard_neighborSet] using added_edge_degree H hne hn x
        simp only [← ncard_neighborSet] at hdx hdu' hdv ⊢
        rw [hdx]
        by_cases hxu : x = u
        · subst x; simp only [true_or, if_true]; omega
        by_cases hxv : x = v
        · subst x; simp only [or_true, if_true]; omega
        · simp only [hxu, hxv, or_self, if_false, Nat.add_zero]
          simpa only [← ncard_neighborSet] using hH.2.1 x
      · refine ⟨hH.2.2.disjoint, ?_⟩
        intro x y hxy
        rcases hxy with hxy | hxy
        · exact hH.2.2.mem_of_adj hxy
        · rcases (edge_adj u v x y).mp hxy with ⟨hxy | hxy, _⟩
          · exact Or.inl ⟨hxy.1.symm ▸ hu, hxy.2.symm ▸ hv⟩
          · exact Or.inr ⟨hxy.1.symm ▸ hv, hxy.2.symm ▸ hu⟩
    exact (lt_sup_edge H u v hne hn).not_ge (hmax.le_of_ge hK le_sup_left)

end D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion

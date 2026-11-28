import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-! Cubic triangles and the common-neighbor condition constrain incidence
with the high-degree block of a contact graph. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicContactHighBlock

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A cubic edge with a common neighbor has two common neighbors of degree
strictly greater than three, provided all degrees are at least three. -/
theorem cubic_edge_two_high_neighbors
    (hmin : ∀ v, 3 ≤ G.degree v)
    (hSecond : ∀ ⦃a b c : V⦄, G.Adj a b → G.degree a = 3 → G.degree b = 3 →
      G.Adj a c → G.Adj b c → ∃ d, d ≠ c ∧ G.Adj a d ∧ G.Adj b d)
    (hTriangle : ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a →
      G.degree a = 3 → G.degree b = 3 → G.degree c = 3 → False)
    {a b c : V} (hab : G.Adj a b) (ha : G.degree a = 3) (hb : G.degree b = 3)
    (hac : G.Adj a c) (hbc : G.Adj b c) :
    3 < G.degree c ∧ ∃ d, d ≠ c ∧ 3 < G.degree d ∧ G.Adj a d ∧ G.Adj b d := by
  have hc : 3 < G.degree c := by
    by_contra! hn
    have he : G.degree c = 3 := Nat.le_antisymm hn (hmin c)
    exact hTriangle a b c hab hbc hac.symm ha hb he
  obtain ⟨d, hdc, had, hbd⟩ := hSecond hab ha hb hac hbc
  have hd : 3 < G.degree d := by
    by_contra! hn
    have he : G.degree d = 3 := Nat.le_antisymm hn (hmin d)
    exact hTriangle a b d hab hbd had.symm ha hb he
  exact ⟨hc,d,hdc,hd,had,hbd⟩

/-- If a single vertex has degree above three, its cubic neighbors form an
independent set. Counting edges from those neighbors to the remaining
vertices gives the sharp degree-budget inequality for that partition. -/
theorem unique_high_degree_bound {v : V}
    (hv : 3 < G.degree v) (hcubic : ∀ x, x ≠ v → G.degree x = 3)
    (hSecond : ∀ ⦃a b c : V⦄, G.Adj a b → G.degree a = 3 → G.degree b = 3 →
      G.Adj a c → G.Adj b c → ∃ d, d ≠ c ∧ G.Adj a d ∧ G.Adj b d)
    (hTriangle : ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a →
      G.degree a = 3 → G.degree b = 3 → G.degree c = 3 → False) :
    5 * G.degree v ≤ 3 * (Fintype.card V - 1) := by
  classical
  let A := G.neighborFinset v
  let B : Finset V := univ \ insert v A
  let N (S : Finset V) (x : V) := S.filter (G.Adj x)
  have hmin (x : V) : 3 ≤ G.degree x := by
    by_cases h : x = v
    · subst x; omega
    · rw [hcubic x h]
  have memA {x : V} : x ∈ A ↔ G.Adj v x := G.mem_neighborFinset v x
  have memB {x : V} : x ∈ B ↔ x ≠ v ∧ x ∉ A := by
    simp only [B, mem_sdiff, mem_univ, true_and, mem_insert, not_or]
  have vNotA : v ∉ A := fun h => G.irrefl (memA.mp h)
  have cardA : A.card = G.degree v := G.card_neighborFinset_eq_degree v
  have cardB : B.card = Fintype.card V - (1 + G.degree v) := by
    change (univ \ insert v A).card = _
    rw [ card_sdiff_of_subset (subset_univ _), card_univ,
      card_insert_of_notMem vNotA, cardA, Nat.add_comm]
  have hAB : 1 + G.degree v ≤ Fintype.card V := by
    have h := card_le_card (subset_univ (insert v A))
    rw [card_insert_of_notMem vNotA, cardA, card_univ] at h
    omega
  have independent {a c : V} (ha : a ∈ A) (hc : c ∈ A) : ¬ G.Adj a c := by
    intro hac
    obtain ⟨_,d,hdv,hd,_,_⟩ := cubic_edge_two_high_neighbors hmin hSecond hTriangle
      hac (hcubic a (memA.mp ha).ne') (hcubic c (memA.mp hc).ne')
      (memA.mp ha).symm (memA.mp hc).symm
    have he := hcubic d hdv
    omega
  have hrow (a : V) (ha : a ∈ A) : (N B a).card = 2 := by
    have he : N B a = (G.neighborFinset a).erase v := by
      ext x
      simp only [N, mem_filter, memB, mem_erase, G.mem_neighborFinset]
      exact ⟨fun ⟨⟨hx,_⟩,hax⟩ => ⟨hx,hax⟩,
        fun ⟨hx,hax⟩ => ⟨⟨hx,fun hxA => independent ha hxA hax⟩,hax⟩⟩
    rw [he, card_erase_of_mem ((G.mem_neighborFinset a v).mpr (memA.mp ha).symm),
      G.card_neighborFinset_eq_degree, hcubic a (memA.mp ha).ne']
  have hcol (b : V) (hb : b ∈ B) : (N A b).card ≤ 3 := by
    have hsub : N A b ⊆ G.neighborFinset b := fun x hx =>
      (G.mem_neighborFinset b x).mpr (mem_filter.mp hx).2
    have h := card_le_card hsub
    rwa [G.card_neighborFinset_eq_degree, hcubic b (memB.mp hb).1] at h
  have hcross : (∑ a ∈ A, (N B a).card) = ∑ b ∈ B, (N A b).card := by
    calc
      _ = ∑ b ∈ B, (A.bipartiteBelow G.Adj b).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := A) (t := B) G.Adj
      _ = _ := by
        refine sum_congr rfl fun b _ => congrArg Finset.card ?_
        ext a
        rw [mem_bipartiteBelow, show a ∈ N A b ↔ a ∈ A ∧ G.Adj b a from mem_filter,
          G.adj_comm a b]
  have hcount : 2 * G.degree v ≤ 3 * B.card := by
    have hl : (∑ a ∈ A, (N B a).card) = 2 * G.degree v := by
      rw [sum_congr rfl hrow, sum_const, cardA, nsmul_eq_mul, Nat.mul_comm]
      rfl
    have hr : (∑ b ∈ B, (N A b).card) ≤ 3 * B.card := by
      calc
        _ ≤ ∑ _ ∈ B, (3 : ℕ) := sum_le_sum hcol
        _ = _ := by rw [sum_const, nsmul_eq_mul, Nat.mul_comm]; rfl
    omega
  rw [cardB] at hcount
  omega

#print axioms cubic_edge_two_high_neighbors
#print axioms unique_high_degree_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicContactHighBlock

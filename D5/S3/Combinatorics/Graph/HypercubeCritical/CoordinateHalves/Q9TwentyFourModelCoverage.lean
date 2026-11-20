import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances

/-! Recover the vertices suppressed by compression and match the resulting
induced graph to the vertex order used by the embedding search. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelCoverage

open Finset SimpleGraph
open private suppress from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
open private paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private High vertex side vertex_degree vertex_injective neighbor_pair source_of_middle
  expandEdge_cases from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion
open private Graph adjacent decode from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
open private crosses from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors
open private mem_graphEdges graphEdges_nodup cross_of_side colored_model_of_half from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage
open private modelAt colorAt subdivisionPairs subdivisionPairsOfOrder expandedAdjacent expandedAdjacentOfOrder
  distance reorder valid_model
  walk_of_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)

attribute [local instance] Classical.propDecidable

private theorem high_adj {V : Type*} [Fintype V] {G : SimpleGraph V} {L R : Finset V}
    (hbip : G.IsBipartiteWith (L : Set V) (R : Set V)) (x y : High G L R) :
    G.Adj (vertex x) (vertex y) ↔ (suppress G L R).Adj x y ∧ side x ≠ side y := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [side, Sum.elim_inl, ne_eq, not_true_eq_false, and_false, iff_false]
      intro he
      exact Finset.disjoint_left.mp (Finset.disjoint_coe.mp hbip.disjoint)
        (mem_filter.mp y.property).1
        (hbip.mem_of_mem_adj (mem_filter.mp x.property).1 he)
    | inr y => simp [suppress, vertex, side]
  | inr x =>
    cases y with
    | inl y => simp [suppress, vertex, side]
    | inr y =>
      simp only [side, Sum.elim_inr, ne_eq, not_true_eq_false, and_false, iff_false]
      intro he
      exact Finset.disjoint_left.mp (Finset.disjoint_coe.mp hbip.disjoint)
        (hbip.mem_of_mem_adj' (mem_filter.mp x.property).1 he.symm)
        (mem_filter.mp y.property).1

private theorem expanded_graph {order lowCount : Nat} [NeZero order]
    {V : Type*} [Fintype V] {G : SimpleGraph V} {L R : Finset V}
    (hbip : G.IsBipartiteWith (L : Set V) (R : Set V)) (hV : Fintype.card V = order + lowCount)
    (hlow : ∀ x y, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (graph : Graph) (color : Nat) (label : Fin order ≃ High G L R) (reverse : Bool)
    (hlabel : ∀ i j : Fin order, adjacent graph i.val j.val = true ↔
      (suppress G L R).Adj (label i) (label j))
    (hcolor : ∀ i : Fin order, color.testBit i.val = (side (label i) ^^ reverse))
    (hlen : (subdivisionPairsOfOrder order graph color).length = lowCount) :
    ∃ point : Fin (order + lowCount) ≃ V, ∀ i j : Fin (order + lowCount),
      expandedAdjacentOfOrder order graph color i.val j.val = true ↔
        G.Adj (point i) (point j) := by
  classical
  let pairs := subdivisionPairsOfOrder order graph color
  have hdisj : Disjoint L R := Finset.disjoint_coe.mp hbip.disjoint
  let h (i : Fin order) := vertex (label i)
  have hi : Function.Injective h := (vertex_injective (G := G) hdisj).comp label.injective
  have hd (i : Fin order) : G.degree (h i) = 3 := vertex_degree _
  let edge (i : Fin lowCount) := pairs[i.val]'(hlen.symm ▸ i.isLt)
  have hedge (i : Fin lowCount) : (edge i).1 < order ∧ (edge i).2 < order ∧ (edge i).1 < (edge i).2 ∧
      (suppress G L R).Adj (label (Fin.ofNat order (edge i).1)) (label (Fin.ofNat order (edge i).2)) ∧
      side (label (Fin.ofNat order (edge i).1)) = side (label (Fin.ofNat order (edge i).2)) := by
    have hm : edge i ∈ pairs := List.getElem_mem _
    obtain ⟨hm, hc⟩ := List.mem_filter.mp hm
    obtain ⟨ha, hb, hlt, hadj⟩ := (mem_graphEdges order graph _ _).mp hm
    let a := Fin.ofNat order (edge i).1
    let b := Fin.ofNat order (edge i).2
    have hva : a.val = (edge i).1 := Nat.mod_eq_of_lt ha
    have hvb : b.val = (edge i).2 := Nat.mod_eq_of_lt hb
    refine ⟨ha, hb, hlt, (hlabel a b).mp (by rw [hva, hvb]; exact hadj), ?_⟩
    by_contra hne
    have he := (cross_of_side label color reverse hcolor a b).mpr hne
    rw [hva, hvb] at he
    rw [he] at hc
    cases hc
  let a (i : Fin lowCount) := (⟨(edge i).1, (hedge i).1⟩ : Fin order)
  let b (i : Fin lowCount) := (⟨(edge i).2, (hedge i).2.1⟩ : Fin order)
  have hab (i : Fin lowCount) : a i ≠ b i :=
    fun he => (Nat.ne_of_lt (hedge i).2.2.1) (congrArg Fin.val he)
  have hlowExists (i : Fin lowCount) :
      ∃ m, G.degree m = 2 ∧ G.Adj m (h (a i)) ∧ G.Adj m (h (b i)) := by
    have ha : Fin.ofNat order (edge i).1 = a i := Fin.ext (Nat.mod_eq_of_lt (hedge i).1)
    have hb : Fin.ofNat order (edge i).2 = b i := Fin.ext (Nat.mod_eq_of_lt (hedge i).2.1)
    have he := (hedge i).2.2.2
    rw [ha, hb] at he
    rcases expandEdge_cases he.1 with ⟨hc, _⟩ | ⟨_, m, hd, hx, hy, _⟩
    · exact (hc he.2).elim
    · exact ⟨m, hd, hx.symm, hy⟩
  let low (i : Fin lowCount) := (hlowExists i).choose
  have dlow (i : Fin lowCount) : G.degree (low i) = 2 := (hlowExists i).choose_spec.1
  have endLow (i : Fin lowCount) : G.Adj (low i) (h (a i)) ∧ G.Adj (low i) (h (b i)) :=
    (hlowExists i).choose_spec.2
  have lowAdj (i : Fin lowCount) (j : Fin order) : G.Adj (low i) (h j) ↔ j = a i ∨ j = b i := by
    rw [← SimpleGraph.mem_neighborFinset, neighbor_pair (dlow i) (endLow i).1 (endLow i).2
      (fun he => hab i (hi he)), mem_insert, mem_singleton]
    exact or_congr hi.eq_iff hi.eq_iff
  have lowInj : Function.Injective low := by
    intro i j he
    have e1 := (lowAdj i (a j)).mp (he.symm ▸ (endLow j).1)
    have e2 := (lowAdj i (b j)).mp (he.symm ▸ (endLow j).2)
    have hs1 : (a i).val < (b i).val := (hedge i).2.2.1
    have hs2 : (a j).val < (b j).val := (hedge j).2.2.1
    have hs : edge i = edge j := by
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact (hab j (e1.trans e2.symm)).elim
      · exact Prod.ext (congrArg Fin.val e1.symm) (congrArg Fin.val e2.symm)
      · rw [e1, e2] at hs2
        omega
      · exact (hab j (e1.trans e2.symm)).elim
    have hn : pairs.Nodup := (graphEdges_nodup order graph).filter _
    exact Fin.ext (hn.eq_of_getElem_eq _ _ hs)
  let f (i : Fin (order + lowCount)) :=
    if e : i.val < order then h ⟨i.val, e⟩ else low ⟨i.val - order, by omega⟩
  have hf : Function.Injective f := by
    intro i j he
    unfold f at he
    split at he <;> split at he
    · apply Fin.ext
      exact congrArg (fun i : Fin order => i.val) (hi he)
    · have := congrArg (fun v => G.degree v) he
      rw [hd, dlow] at this
      omega
    · have := congrArg (fun v => G.degree v) he
      rw [dlow, hd] at this
      omega
    · have hh := congrArg Fin.val (lowInj he)
      apply Fin.ext
      change i.val - order = j.val - order at hh
      omega
  let graphPoint : Fin (order + lowCount) ≃ V := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp [hV]⟩)
  have hAdj (i j : Fin (order + lowCount)) :
      expandedAdjacentOfOrder order graph color i.val j.val = true ↔ G.Adj (graphPoint i) (graphPoint j) := by
    change expandedAdjacentOfOrder order graph color i.val j.val = true ↔ G.Adj (f i) (f j)
    by_cases hI : i.val < order <;> by_cases hJ : j.val < order
    · simp only [expandedAdjacentOfOrder, hI, hJ, ite_true, f, dite_true, Bool.and_eq_true_iff]
      exact (and_congr (hlabel ⟨i.val, hI⟩ ⟨j.val, hJ⟩)
        (cross_of_side label color reverse hcolor ⟨i.val, hI⟩ ⟨j.val, hJ⟩)).trans
        (high_adj hbip _ _).symm
    · let j' : Fin lowCount := ⟨j.val - order, by omega⟩
      have he : pairs[j.val - order]! = edge j' := getElem!_pos pairs _ (hlen.symm ▸ j'.isLt)
      simp only [expandedAdjacentOfOrder, hI, hJ, ite_true, ite_false, f, dite_true, dite_false]
      change (i.val == pairs[j.val - order]!.1 || i.val == pairs[j.val - order]!.2) = true ↔
        G.Adj (h ⟨i.val, hI⟩) (low j')
      rw [he, G.adj_comm, lowAdj]
      simp only [Bool.or_eq_true_iff, beq_iff_eq, a, b, Fin.ext_iff]
    · let i' : Fin lowCount := ⟨i.val - order, by omega⟩
      have he : pairs[i.val - order]! = edge i' := getElem!_pos pairs _ (hlen.symm ▸ i'.isLt)
      simp only [expandedAdjacentOfOrder, hI, hJ, ite_true, ite_false, f, dite_true, dite_false]
      change (j.val == pairs[i.val - order]!.1 || j.val == pairs[i.val - order]!.2) = true ↔
        G.Adj (low i') (h ⟨j.val, hJ⟩)
      rw [he, lowAdj]
      simp only [Bool.or_eq_true_iff, beq_iff_eq, a, b, Fin.ext_iff]
    · simp only [expandedAdjacentOfOrder, hI, hJ, ite_false, f, dite_false, Bool.false_eq_true, false_iff]
      exact fun he => hlow _ _ he (dlow _) (dlow _)
  exact ⟨graphPoint, hAdj⟩

private theorem expanded_model {V : Type*} [Fintype V] {G : SimpleGraph V} {L R : Finset V}
    (hbip : G.IsBipartiteWith (L : Set V) (R : Set V)) (hV : Fintype.card V = 24)
    (hlow : ∀ x y, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (index : Fin 53) (label : Fin 12 ≃ High G L R) (reverse : Bool)
    (hlabel : ∀ i j : Fin 12, adjacent (decode (colorAt index).1) i.val j.val = true ↔
      (suppress G L R).Adj (label i) (label j))
    (hcolor : ∀ i : Fin 12, (colorAt index).2.testBit i.val = (side (label i) ^^ reverse)) :
    ∃ point : Fin 24 ≃ V, ∀ i j : Fin 24,
      distance (modelAt index) i.val j.val = 1 ↔ G.Adj (point i) (point j) := by
  classical
  let code := (colorAt index).1
  let color := (colorAt index).2
  let pairs := subdivisionPairs code color
  obtain ⟨_, hlen, hbound, hinjective, hmatrix, _, _⟩ := valid_model index
  change pairs.length = 12 at hlen
  obtain ⟨graphPoint, hAdj⟩ := expanded_graph (order := 12) (lowCount := 12)
    hbip hV hlow (decode code) color label reverse hlabel hcolor hlen
  let perm (i : Fin 24) : Fin 24 := ⟨reorder index i, hbound i⟩
  have hp : Function.Injective perm := fun i j h => hinjective i j (congrArg Fin.val h)
  let e := Equiv.ofBijective perm ⟨hp, Finite.surjective_of_injective hp⟩
  exact ⟨e.trans graphPoint, fun i j => (hmatrix i j).trans (hAdj (perm i) (perm j))⟩

private theorem model_of_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 24) :
    ∃ (index : Fin 53) (point : Fin 24 ≃ (coordinateSlice C b : Set (Q 9))),
      ∀ i j : Fin 24, distance (modelAt index) i.val j.val = 1 ↔
        (hypercube 9).Adj (point i).val (point j).val := by
  obtain ⟨index, label, reverse, he, hc⟩ := colored_model_of_half hC hr hb b hs
  obtain ⟨_, hlow, _, _, _⟩ := Q9TwentyFourCompression.half_degree_split hC hr hb b hs
  obtain ⟨point, hp⟩ := expanded_model (parity_bipartite (coordinateSlice C b))
    ((Fintype.card_coe _).trans hs) hlow index label reverse he hc
  exact ⟨index, point, hp⟩

#print axioms expanded_model
#print axioms model_of_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelCoverage

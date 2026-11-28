/- GID: D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex, mathlib/module/Mathlib.Data.Fintype.Fin, mathlib/module/Mathlib.Data.Fintype.Perm, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Algebra.BigOperators.Field, mathlib/module/Mathlib.Tactic.Positivity]
   utility: none
   digest: An induced colorable subgraph from reciprocal degrees. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import OmegaBuild.Commands

compile_only_with_mathlib

/-! # An induced colorable subgraph from reciprocal degrees -/

open scoped BigOperators

namespace ColorableInducedSubgraph

noncomputable section

/-- A vertex ordering assigns each vertex a distinct position. -/
abbrev VertexOrder (V : Type*) [Fintype V] := V ≃ Fin (Fintype.card V)

private theorem card_filter_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) [DecidablePred p] [DecidablePred (fun a => p (e a))] :
    (Finset.univ.filter fun a => p (e a)).card = (Finset.univ.filter p).card := by
  calc
    _ = (Finset.map e.toEmbedding (Finset.univ.filter fun a => p (e a))).card :=
      (Finset.card_map e.toEmbedding).symm
    _ = _ := by
      congr 1
      ext b
      simp [Finset.mem_map_equiv]

private theorem sum_card_filter_comm {A B : Type*} (U : Finset A) (W : Finset B)
    (p : A → B → Prop) [DecidableRel p] :
    (∑ a ∈ U, (W.filter (p a)).card) = ∑ b ∈ W, (U.filter fun a => p a b).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

/-- Rank, starting at zero, in the order induced on a finite set. -/
def localRank {V : Type*} [Fintype V] (B : Finset V) (e : VertexOrder V) :
    B ≃ Fin B.card :=
  let positions := B.map e.toEmbedding
  let restrict : B ≃ positions := e.subtypeEquiv fun v => by
    change v ∈ B ↔ e v ∈ B.map e.toEmbedding
    rw [Finset.mem_map_equiv, e.symm_apply_apply]
  restrict.trans (positions.orderIsoOfFin (Finset.card_map e.toEmbedding)).symm.toEquiv

private theorem localRank_lt_iff {V : Type*} [Fintype V]
    (B : Finset V) (e : VertexOrder V) (x y : B) :
    localRank B e x < localRank B e y ↔ e x.val < e y.val := by
  let positions := B.map e.toEmbedding
  let sorted := positions.orderIsoOfFin (Finset.card_map e.toEmbedding)
  have mem (z : B) : e z.val ∈ positions := Finset.mem_map.mpr ⟨z.val, z.property, rfl⟩
  exact sorted.symm.lt_iff_lt (x := ⟨e x.val, mem x⟩) (y := ⟨e y.val, mem y⟩)

private theorem localRank_val {V : Type*} [Fintype V]
    (B : Finset V) (e : VertexOrder V) (x : B) :
    (localRank B e x).val = (Finset.univ.filter fun y : B => e y.val < e x.val).card := by
  calc
    (localRank B e x).val = (Finset.Iio (localRank B e x)).card := (Fin.card_Iio _).symm
    _ = (Finset.univ.filter fun i => i < localRank B e x).card := by
      congr 1
      ext i
      simp
    _ = (Finset.univ.filter fun y : B => localRank B e y < localRank B e x).card :=
      (card_filter_equiv (localRank B e) _).symm
    _ = (Finset.univ.filter fun y : B => e y.val < e x.val).card := by
      congr 1
      ext y
      simpa only [Finset.mem_filter_univ] using localRank_lt_iff B e y x

private theorem swap_mem_iff {V : Type*} [DecidableEq V] (B : Finset V) (x y : B) (a : V) :
    Equiv.swap x.val y.val a ∈ B ↔ a ∈ B := by
  by_cases hxa : a = x.val
  · subst a
    simp [x.property, y.property]
  by_cases hya : a = y.val
  · subst a
    simp [x.property, y.property]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hya]

/-- Swapping two names in the set carries one vertex's rank to the other. -/
private theorem localRank_swap {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (e : VertexOrder V) (x y : B) :
    localRank B ((Equiv.swap x.val y.val).trans e) y = localRank B e x := by
  let swap := Equiv.swap x.val y.val
  let restrict : B ≃ B := swap.subtypeEquiv fun a => (swap_mem_iff B x y a).symm
  apply Fin.ext
  rw [localRank_val, localRank_val]
  simp only [Equiv.trans_apply, Equiv.swap_apply_right]
  exact card_filter_equiv restrict (fun a => e a.val < e x.val)

/-- Orders in which a specified vertex has rank in a specified set of ranks. -/
def ordersAtRanks {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (x : B) (T : Finset (Fin B.card)) : Finset (VertexOrder V) :=
  Finset.univ.filter fun e => localRank B e x ∈ T

/-- For a fixed vertex, the count of orders attaining any specified set of ranks
times the local set size is the rank set size times the total number of orders. -/
private theorem card_ordersAtRanks_mul {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (x : B) (T : Finset (Fin B.card)) :
    (ordersAtRanks B x T).card * B.card = T.card * Fintype.card (VertexOrder V) := by
  have sameCount (y : B) : (ordersAtRanks B y T).card = (ordersAtRanks B x T).card := by
    let rename : VertexOrder V ≃ VertexOrder V :=
      (Equiv.swap x.val y.val).equivCongr (Equiv.refl _)
    have transport (e : VertexOrder V) : localRank B (rename e) y = localRank B e x :=
      localRank_swap B e x y
    have equalFilters :
        (Finset.univ.filter fun e => localRank B (rename e) y ∈ T) = ordersAtRanks B x T := by
      ext e
      simp [ordersAtRanks, transport]
    rw [ordersAtRanks, ← card_filter_equiv rename (fun e => localRank B e y ∈ T),
      equalFilters]
  calc
    (ordersAtRanks B x T).card * B.card =
        ∑ y : B, (Finset.univ.filter fun e => localRank B e y ∈ T).card := by
      change _ = ∑ y : B, (ordersAtRanks B y T).card
      simp only [sameCount, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        Nat.cast_id, Nat.mul_comm]
    _ = ∑ e : VertexOrder V, (Finset.univ.filter fun y => localRank B e y ∈ T).card :=
      sum_card_filter_comm _ _ _
    _ = T.card * Fintype.card (VertexOrder V) := by
      simp_rw [card_filter_equiv (localRank B _)]
      simp [Nat.mul_comm]

/-- Every two ranks are attained by equally many orders for a fixed vertex. -/
private theorem card_ordersAtRank_eq {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (x : B) (i j : Fin B.card) :
    (ordersAtRanks B x {i}).card = (ordersAtRanks B x {j}).card := by
  have hpos : 0 < B.card := Finset.card_pos.mpr ⟨x.val, x.property⟩
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [card_ordersAtRanks_mul, card_ordersAtRanks_mul, Finset.card_singleton,
    Finset.card_singleton]

private theorem exists_card_ge_of_counts {V Ω : Type*} [Fintype V] [Fintype Ω]
    [Nonempty Ω] [DecidableEq V] (X : Ω → Finset V) (weight : V → ℚ)
    (hcount : ∀ v : V, ((Finset.univ.filter fun e => v ∈ X e).card : ℚ) =
      weight v * (Fintype.card Ω : ℚ)) :
    ∃ e : Ω, (∑ v : V, weight v) ≤ ((X e).card : ℚ) := by
  obtain ⟨e, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun a : Ω => (X a).card) Finset.univ_nonempty
  refine ⟨e, ?_⟩
  have hsum : (∑ a : Ω, (X a).card) = ∑ v : V, (Finset.univ.filter fun a => v ∈ X a).card := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      sum_card_filter_comm (Finset.univ : Finset Ω) (Finset.univ : Finset V)
        (fun a v => v ∈ X a)
  have hupper :
      (∑ a : Ω, ((X a).card : ℚ)) ≤ ((X e).card : ℚ) * (Fintype.card Ω : ℚ) := by
    calc
      _ ≤ ∑ _a : Ω, ((X e).card : ℚ) :=
        Finset.sum_le_sum fun a ha => Nat.cast_le.mpr (hmax a ha)
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  rw [← Nat.cast_sum, hsum, Nat.cast_sum, Finset.sum_congr rfl (fun v _ => hcount v),
    ← Finset.sum_mul] at hupper
  exact le_of_mul_le_mul_right hupper (Nat.cast_pos.mpr Fintype.card_pos)

section Graph

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors that precede the vertex, using a natural-number position function. -/
def earlierNeighbors (position : V → ℕ) (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => position w < position v

/-- Any set of vertices with fewer than `s` earlier neighbors per vertex can be
colored greedily with `s` colors. -/
private theorem colorable_induce_of_earlierNeighbors_lt
    (position : V → ℕ) (hposition : Function.Injective position)
    (X : Finset V) {s : ℕ} (hs : 0 < s)
    (hX : ∀ v ∈ X, (earlierNeighbors G position v).card < s) :
    (G.induce (X : Set V)).Colorable s := by
  classical
  have prefixColorable (n : ℕ) : ∃ c : V → Fin s, ∀ v ∈ X, ∀ w ∈ X,
      position v < n → position w < n →
      G.Adj v w → c v ≠ c w := by
    induction n with
    | zero =>
        exact ⟨fun _ => ⟨0, hs⟩, by simp⟩
    | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        by_cases hex : ∃ a ∈ X, position a = n
        · obtain ⟨a, ha, han⟩ := hex
          let forbidden := (earlierNeighbors G position a).image c
          obtain ⟨color, _, hcolor⟩ := Finset.exists_mem_notMem_of_card_lt_card
            (s := forbidden) (t := Finset.univ)
            (by simpa using Finset.card_image_le.trans_lt (hX a ha))
          have step (b d : V) (hb : b ∈ X) (hd : d ∈ X)
              (hbn : position b < n + 1) (hdn : position d < n + 1)
              (hbd : G.Adj b d) (hlt : position b < position d) :
              Function.update c a color b ≠ Function.update c a color d := by
            have hba : b ≠ a := by
              intro h
              subst b
              omega
            rw [Function.update_of_ne hba]
            by_cases hda : d = a
            · subst d
              rw [Function.update_self]
              exact fun heq => hcolor (heq ▸ Finset.mem_image_of_mem c
                (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hbd.symm, hlt⟩))
            · rw [Function.update_of_ne hda]
              have hne : position d ≠ n := fun h => hda (hposition (h.trans han.symm))
              exact hc b hb d hd (by omega) (by omega) hbd
          refine ⟨Function.update c a color, ?_⟩
          intro v hv w hw hvn hwn hadj
          have hne : position v ≠ position w := fun h => hadj.ne (hposition h)
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact step v w hv hw hvn hwn hadj hlt
          · exact (step w v hw hv hwn hvn hadj.symm hgt).symm
        · refine ⟨c, ?_⟩
          intro v hv w hw hvn hwn hadj
          have hvne : position v ≠ n := fun h => hex ⟨v, hv, h⟩
          have hwne : position w ≠ n := fun h => hex ⟨w, hw, h⟩
          exact hc v hv w hw (by omega) (by omega) hadj
  obtain ⟨c, hc⟩ := prefixColorable (X.sup position + 1)
  refine ⟨Coloring.mk (fun v => c v.val) ?_⟩
  intro v w hadj
  exact hc v.val v.property w.val w.property
    (Nat.lt_succ_of_le (Finset.le_sup v.property))
    (Nat.lt_succ_of_le (Finset.le_sup w.property)) hadj

variable [DecidableEq V]

/-- The closed neighborhood, including the vertex itself. -/
def closedNeighborhood (v : V) : Finset V := insert v (G.neighborFinset v)

private theorem card_closedNeighborhood (v : V) :
    (closedNeighborhood G v).card = G.degree v + 1 := by
  rw [closedNeighborhood, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
    G.card_neighborFinset_eq_degree]

/-- The rank of a vertex in its closed neighborhood counts its earlier neighbors. -/
private theorem localRank_closedNeighborhood (e : VertexOrder V) (v : V) :
    (localRank (closedNeighborhood G v) e ⟨v, Finset.mem_insert_self _ _⟩).val =
      (earlierNeighbors G (fun w => (e w).val) v).card := by
  rw [localRank_val]
  let coe : closedNeighborhood G v ↪ V := Function.Embedding.subtype _
  rw [← Finset.card_map coe]
  congr 1
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hw
    have hlt := (Finset.mem_filter_univ a).mp ha
    have hne : a.val ≠ v := by
      intro h
      change e a.val < e v at hlt
      rw [h] at hlt
      exact (lt_irrefl _) hlt
    have hmem := (Finset.mem_insert.mp a.property).resolve_left hne
    exact Finset.mem_filter.mpr ⟨hmem, hlt⟩
  · intro hw
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hw
    let a : closedNeighborhood G v := ⟨w, Finset.mem_insert_of_mem hmem⟩
    exact Finset.mem_map.mpr ⟨a, (Finset.mem_filter_univ a).mpr hlt, rfl⟩

/-- The selected vertices for a particular order. -/
def selected (s : ℕ) (e : VertexOrder V) : Finset V :=
  Finset.univ.filter fun v => (earlierNeighbors G (fun w => (e w).val) v).card < s

/-- The exact finite count of orders in which a vertex is selected. -/
private theorem card_orders_selecting_mul (s : ℕ) (v : V) (h : s ≤ G.degree v + 1) :
    (Finset.univ.filter fun e : VertexOrder V => v ∈ selected G s e).card *
      (G.degree v + 1) = s * Fintype.card (VertexOrder V) := by
  let B := closedNeighborhood G v
  let T : Finset (Fin B.card) := Finset.univ.filter fun i => i.val < s
  have hT : T.card = s := by
    rw [show T.card = min B.card s from Fin.card_filter_val_lt]
    exact min_eq_right ((card_closedNeighborhood G v).symm ▸ h)
  have hfilter :
      (Finset.univ.filter fun e : VertexOrder V => v ∈ selected G s e) =
        ordersAtRanks B ⟨v, Finset.mem_insert_self _ _⟩ T := by
    ext e
    simp only [Finset.mem_filter_univ, ordersAtRanks, selected, T]
    rw [localRank_closedNeighborhood G e v]
  rw [hfilter, ← card_closedNeighborhood G v, card_ordersAtRanks_mul, hT]

omit [DecidableEq V] in
/-- The ordering bound under the degree hypothesis at each vertex. -/
private theorem ordering_of_degree (s : ℕ) (hs : 0 < s) (hdegree : ∀ v, s ≤ G.degree v + 1) :
    ∃ X : Finset V, (G.induce (X : Set V)).Colorable s ∧
      (s : ℚ) * (∑ v : V, 1 / ((G.degree v : ℚ) + 1)) ≤ (X.card : ℚ) := by
  classical
  let _ : Nonempty (VertexOrder V) := ⟨Fintype.equivFin V⟩
  have hcounts (v : V) :
      ((Finset.univ.filter fun e : VertexOrder V => v ∈ selected G s e).card : ℚ) =
        ((s : ℚ) / ((G.degree v : ℚ) + 1)) * (Fintype.card (VertexOrder V) : ℚ) := by
    have hd : (G.degree v : ℚ) + 1 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div₀]
    refine (eq_div_iff_mul_eq hd).mpr ?_
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ℚ)) (card_orders_selecting_mul G s v (hdegree v))
  obtain ⟨order, horder⟩ := exists_card_ge_of_counts (selected G s)
    (fun v => (s : ℚ) / ((G.degree v : ℚ) + 1)) hcounts
  refine ⟨selected G s order, colorable_induce_of_earlierNeighbors_lt G
    (fun w => (order w).val) (fun _ _ heq => order.injective (Fin.ext heq)) _ hs
    (fun v hv => (Finset.mem_filter_univ v).mp hv), ?_⟩
  simpa only [Finset.mul_sum, mul_one_div] using horder

omit [DecidableEq V] in
/-- Ordering Lemma 3.2 of arXiv:2611.34386v1. -/
theorem exists_colorable_induce_of_minDegree (s : ℕ) (hs : 0 < s) (hmin : s - 1 ≤ G.minDegree) :
    ∃ X : Finset V, (G.induce (X : Set V)).Colorable s ∧
      (s : ℚ) * (∑ v : V, 1 / ((G.degree v : ℚ) + 1)) ≤ (X.card : ℚ) := by
  apply ordering_of_degree G s hs
  intro v
  have h := hmin.trans (G.minDegree_le_degree v)
  omega

end Graph

end

end ColorableInducedSubgraph

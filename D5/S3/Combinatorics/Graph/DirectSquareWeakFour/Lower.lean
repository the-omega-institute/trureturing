/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal incidence lower bounds for weak-four resolving sets in direct squares. -/

import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Core
import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.LowDegreeCount

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset

variable {n : ℕ}

private theorem avoiding {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (a a' : α)
    (h : (S.filter (fun w => w.1 = a)).card +
      (S.filter (fun w => w.1 = a')).card < Fintype.card β) :
    ∃ b : β, (a,b) ∉ S ∧ (a',b) ∉ S := by
  let A := (S.filter (fun w => w.1 = a)).image Prod.snd
  let B := (S.filter (fun w => w.1 = a')).image Prod.snd
  have hc : (A ∪ B).card < (univ : Finset β).card := by
    have hA := card_image_le (s := S.filter (fun w => w.1 = a)) (f := Prod.snd)
    have hB := card_image_le (s := S.filter (fun w => w.1 = a')) (f := Prod.snd)
    change A.card ≤ _ at hA
    change B.card ≤ _ at hB
    have hU := card_union_le A B
    simpa only [card_univ] using (show (A ∪ B).card < Fintype.card β by omega)
  obtain ⟨b, _, hb⟩ := exists_mem_notMem_of_card_lt_card hc
  refine ⟨b, ?_, ?_⟩
  · intro hs
    exact hb (mem_union_left B (mem_image.mpr ⟨(a,b), mem_filter.mpr ⟨hs,rfl⟩, rfl⟩))
  · intro hs
    exact hb (mem_union_right A (mem_image.mpr ⟨(a',b), mem_filter.mpr ⟨hs,rfl⟩, rfl⟩))

/-- Two distinct rows have total landmark degree at least four. -/
theorem row_pair_min (hn : 4 ≤ n) (S : Finset (Fin n × Fin n)) (hS : IsWeakFour S)
    (i i' : Fin n) (hi : i ≠ i') : 4 ≤ rowDegree S i + rowDegree S i' := by
  by_contra h
  obtain ⟨j, hj, hj'⟩ := avoiding S i i' (by
    simpa only [rowDegree, HammingWeakTwoMetricDimension.rowDegree, Fintype.card_fin] using
      (show rowDegree S i + rowDegree S i' < n by omega))
  have hw := hS (i,j) (i',j) (by simpa using hi)
  rw [delta_same_col (by omega) S i i' j hi] at hw
  simp only [if_neg hj, if_neg hj', add_zero] at hw
  omega

/-- The transposed necessary pair-degree bound. -/
theorem col_pair_min (hn : 4 ≤ n) (S : Finset (Fin n × Fin n)) (hS : IsWeakFour S)
    (j j' : Fin n) (hj : j ≠ j') : 4 ≤ colDegree S j + colDegree S j' := by
  by_contra h
  let T := S.map (Equiv.prodComm (Fin n) (Fin n)).toEmbedding
  have hdeg (j : Fin n) : (T.filter (fun w => w.1 = j)).card = colDegree S j := by
    simp only [T, filter_map, card_map, Function.comp_def, Equiv.toEmbedding_apply,
      Equiv.prodComm_apply, Prod.fst_swap, HammingWeakTwoMetricDimension.colDegree]
    rfl
  obtain ⟨i, hi, hi'⟩ := avoiding T j j' (by rw [hdeg,hdeg]; simp only [Fintype.card_fin]; omega)
  have hi : (i,j) ∉ S := by simpa [T] using hi
  have hi' : (i,j') ∉ S := by simpa [T] using hi'
  have hw := hS (i,j) (i,j') (by simpa using hj)
  rw [delta_same_row (by omega) S i j j' hj] at hw
  simp only [if_neg hi, if_neg hi', add_zero] at hw
  omega

private theorem min_two_of_small_sum (hn : 2 ≤ n) (f : Fin n → ℕ)
    (hpair : ∀ i i', i ≠ i' → 4 ≤ f i + f i')
    (hsmall : (∑ i, f i) < 3*n-2) : ∀ i, 2 ≤ f i := by
  intro i
  by_contra h
  have hi : f i ≤ 1 := by omega
  have heach (i' : Fin n) (hi' : i' ∈ univ.erase i) : 4 - f i ≤ f i' := by
    have := hpair i i' (mem_erase.mp hi').1.symm
    omega
  have hs := sum_le_sum heach
  have ht := add_sum_erase univ f (mem_univ i)
  simp only [sum_const, smul_eq_mul, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin] at hs
  interval_cases hv : f i <;> omega

/-- Sets smaller than the elementary three-per-row bound have minimum degree two. -/
theorem minimum_degrees (hn : 4 ≤ n) (S : Finset (Fin n × Fin n)) (hS : IsWeakFour S)
    (hsmall : S.card < 3*n-2) :
    (∀ i, 2 ≤ rowDegree S i) ∧ (∀ j, 2 ≤ colDegree S j) := by
  constructor
  · apply min_two_of_small_sum (by omega) (rowDegree S) (row_pair_min hn S hS)
    simpa only [HammingWeakTwoMetricDimension.sum_rowDegree] using hsmall
  · apply min_two_of_small_sum (by omega) (colDegree S) (col_pair_min hn S hS)
    simpa only [HammingWeakTwoMetricDimension.sum_colDegree] using hsmall

/-- A landmark set as a bipartite incidence graph, distinct from the product graph. -/
def incidence (S : Finset (Fin n × Fin n)) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj a b := match a,b with
    | .inl i, .inr j => (i,j) ∈ S
    | .inr j, .inl i => (i,j) ∈ S
    | _, _ => False
  symm := ⟨by rintro (i|j) (i'|j') <;> simp⟩
  loopless := ⟨by rintro (i|j) <;> simp⟩

instance (S : Finset (Fin n × Fin n)) : DecidableRel (incidence S).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [incidence] <;> infer_instance

private theorem row_support (S : Finset (Fin n × Fin n)) (i : Fin n) :
    (univ.filter (fun j => (i,j) ∈ S)).card = rowDegree S i := by
  apply card_bij (fun j _ => (i,j))
  · intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).2, rfl⟩
  · intro a _ b _ h
    exact congrArg Prod.snd h
  · intro w hw
    obtain ⟨hw, hi⟩ := mem_filter.mp hw
    exact ⟨w.2, by simp [← hi, hw], by exact Prod.ext hi.symm rfl⟩

private theorem col_support (S : Finset (Fin n × Fin n)) (j : Fin n) :
    (univ.filter (fun i => (i,j) ∈ S)).card = colDegree S j := by
  apply card_bij (fun i _ => (i,j))
  · intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).2, rfl⟩
  · intro a _ b _ h
    exact congrArg Prod.fst h
  · intro w hw
    obtain ⟨hw, hj⟩ := mem_filter.mp hw
    exact ⟨w.1, by simp [← hj, hw], by exact Prod.ext rfl hj.symm⟩

/-- The incidence graph degrees are the original row and column cardinalities. -/
theorem incidence_degrees (S : Finset (Fin n × Fin n)) :
    (∀ i, (incidence S).degree (.inl i) = rowDegree S i) ∧
    (∀ j, (incidence S).degree (.inr j) = colDegree S j) := by
  constructor
  · intro i
    have he : (incidence S).neighborFinset (.inl i) =
        (univ.filter (fun j => (i,j) ∈ S)).map Function.Embedding.inr := by
      ext v
      cases v <;> simp only [SimpleGraph.mem_neighborFinset] <;> simp [incidence]
    rw [SimpleGraph.degree, he, card_map]
    exact row_support S i
  · intro j
    have he : (incidence S).neighborFinset (.inr j) =
        (univ.filter (fun i => (i,j) ∈ S)).map Function.Embedding.inl := by
      ext v
      cases v <;> simp only [SimpleGraph.mem_neighborFinset] <;> simp [incidence]
    rw [SimpleGraph.degree, he, card_map]
    exact col_support S j

/-- The degree-two subgraph cannot contain a path through four distinct vertices. -/
theorem no_low_rectangle_path (hn : 4 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : IsWeakFour S) (i i' j j' : Fin n) (hi : i ≠ i') (hj : j ≠ j')
    (ha : (i,j) ∈ S) (hb : (i',j) ∈ S) (hc : (i',j') ∈ S)
    (hdi : rowDegree S i = 2) (hdi' : rowDegree S i' = 2)
    (hdj : colDegree S j = 2) (hdj' : colDegree S j' = 2) : False := by
  have hd := delta_rectangle (by omega) S i i' j' j hi hj.symm
  have hw := hS (i,j') (i',j) (by intro h; exact hi (congrArg Prod.fst h))
  simp only [if_pos ha, if_pos hb, if_pos hc, hdi, hdi', hdj, hdj'] at hd
  split_ifs at hd <;> omega

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour

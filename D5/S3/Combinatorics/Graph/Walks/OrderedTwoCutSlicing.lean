/- GID: D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two ordered actual path edges determine three endpoint-typed paths with the literal full support and exactly the retained edges. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing

universe u

private theorem list_split_at_two_indices {α : Type u} (l : List α)
    {i j : Nat} (hij : i < j) (hj : j < l.length) :
    l.take i ++ [l[i]'(lt_trans hij hj)] ++
        (l.drop (i + 1)).take (j - (i + 1)) ++
        [l[j]'hj] ++ l.drop (j + 1) = l := by
  have hmiddle := List.drop_take_append_drop l (i + 1) (j - (i + 1))
  have hs : i + 1 + (j - (i + 1)) = j := by omega
  rw [hs] at hmiddle
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  rw [← List.drop_eq_getElem_cons hj, hmiddle,
    ← List.drop_eq_getElem_cons (lt_trans hij hj), List.take_append_drop]

private theorem filter_out_two_of_nodup {α : Type u} [DecidableEq α]
    (l₀ l₁ l₂ : List α) (e₀ e₁ : α)
    (hn : (l₀ ++ [e₀] ++ l₁ ++ [e₁] ++ l₂).Nodup) :
    (l₀ ++ [e₀] ++ l₁ ++ [e₁] ++ l₂).filter
        (fun e => decide (e ≠ e₀ ∧ e ≠ e₁)) = l₀ ++ l₁ ++ l₂ := by
  have hn' : (l₀ ++ e₀ :: (l₁ ++ e₁ :: l₂)).Nodup := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hn
  have hs₀ := List.nodup_append'.mp hn'
  have ht₀ := List.nodup_cons.mp hs₀.2.1
  have hs₁ := List.nodup_append'.mp ht₀.2
  have ht₁ := List.nodup_cons.mp hs₁.2.1
  have he₀₀ : e₀ ∉ l₀ := by
    intro he
    exact List.disjoint_left.mp hs₀.2.2 he (by simp)
  have he₁₀ : e₁ ∉ l₀ := by
    intro he
    exact List.disjoint_left.mp hs₀.2.2 he (by simp)
  have he₀₁ : e₀ ∉ l₁ := by
    intro he
    exact ht₀.1 (List.mem_append.mpr (Or.inl he))
  have he₁₁ : e₁ ∉ l₁ := by
    intro he
    exact List.disjoint_left.mp hs₁.2.2 he (by simp)
  have he₀₂ : e₀ ∉ l₂ := by
    intro he
    exact ht₀.1 (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ he)))
  have he₁₂ : e₁ ∉ l₂ := ht₁.1
  have hf₀ : l₀.filter (fun e => decide (e ≠ e₀ ∧ e ≠ e₁)) = l₀ := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq]
    exact ⟨fun h => he₀₀ (h ▸ he), fun h => he₁₀ (h ▸ he)⟩
  have hf₁ : l₁.filter (fun e => decide (e ≠ e₀ ∧ e ≠ e₁)) = l₁ := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq]
    exact ⟨fun h => he₀₁ (h ▸ he), fun h => he₁₁ (h ▸ he)⟩
  have hf₂ : l₂.filter (fun e => decide (e ≠ e₀ ∧ e ≠ e₁)) = l₂ := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq]
    exact ⟨fun h => he₀₂ (h ▸ he), fun h => he₁₂ (h ▸ he)⟩
  simp only [List.filter_append, hf₀, hf₁, hf₂]
  simp

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Cut an actual path at two specified, ordered edge positions. The endpoint
identities record the orientation in which the original path traverses each
cut. All three pieces are actual paths in the original graph; their supports
concatenate literally to the original support, and their edge lists are the
original edge list with exactly the two cuts removed. Adjacent cuts are allowed:
the middle actual nil path still retains its single vertex. -/
theorem exists_path_slicing_at_two_ordered_edges
    {a b ℓ₀ r₀ ℓ₁ r₁ : V} (p : G.Walk a b) (hp : p.IsPath)
    {i j : Nat} (hij : i < j) (hj : j < p.length)
    (hℓ₀ : p.getVert i = ℓ₀) (hr₀ : p.getVert (i + 1) = r₀)
    (hℓ₁ : p.getVert j = ℓ₁) (hr₁ : p.getVert (j + 1) = r₁) :
    ∃ q₀ : G.Walk a ℓ₀, ∃ q₁ : G.Walk r₀ ℓ₁, ∃ q₂ : G.Walk r₁ b,
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = p.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
        p.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges =
        p.edges.filter (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) ∧
      q₀.length = i ∧ q₁.length = j - i - 1 ∧
      q₂.length = p.length - j - 1 := by
  have hi : i < p.length := lt_trans hij hj
  have hi₁ : i + 1 ≤ p.length := by omega
  have hj₁ : j + 1 ≤ p.length := by omega
  have hs : i + 1 + (j - (i + 1)) = j := by omega
  have hm : (p.drop (i + 1)).getVert (j - (i + 1)) = ℓ₁ := by
    rw [SimpleGraph.Walk.drop_getVert, hs]
    exact hℓ₁
  let q₀ : G.Walk a ℓ₀ := (p.take i).copy rfl hℓ₀
  let q₁ : G.Walk r₀ ℓ₁ :=
    ((p.drop (i + 1)).take (j - (i + 1))).copy hr₀ hm
  let q₂ : G.Walk r₁ b := (p.drop (j + 1)).copy hr₁ rfl
  have hq₀ : q₀.IsPath := by
    simpa only [q₀, SimpleGraph.Walk.isPath_copy] using hp.take i
  have hq₁ : q₁.IsPath := by
    simpa only [q₁, SimpleGraph.Walk.isPath_copy] using
      (hp.drop (i + 1)).take (j - (i + 1))
  have hq₂ : q₂.IsPath := by
    simpa only [q₂, SimpleGraph.Walk.isPath_copy] using hp.drop (j + 1)
  have hsupport : q₀.support ++ q₁.support ++ q₂.support = p.support := by
    simp only [q₀, q₁, q₂, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_take, SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hi₁, Nat.min_eq_left hj₁]
    have hmiddle :=
      List.drop_take_append_drop p.support (i + 1) (j - (i + 1) + 1)
    have hs' : i + 1 + (j - (i + 1) + 1) = j + 1 := by omega
    rw [hs'] at hmiddle
    rw [List.append_assoc, hmiddle, List.take_append_drop]
  have hiE : i < p.edges.length := by
    simpa only [SimpleGraph.Walk.length_edges] using hi
  have hjE : j < p.edges.length := by
    simpa only [SimpleGraph.Walk.length_edges] using hj
  have hcut₀ : p.edges[i]'hiE = s(ℓ₀, r₀) := by
    rw [SimpleGraph.Walk.getElem_edges hiE, hℓ₀, hr₀]
  have hcut₁ : p.edges[j]'hjE = s(ℓ₁, r₁) := by
    rw [SimpleGraph.Walk.getElem_edges hjE, hℓ₁, hr₁]
  have hedges :
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
        p.edges := by
    have hsplit := list_split_at_two_indices p.edges hij hjE
    rw [hcut₀, hcut₁] at hsplit
    simpa only [q₀, q₁, q₂, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_take, SimpleGraph.Walk.edges_drop] using hsplit
  have hfiltered :
      q₀.edges ++ q₁.edges ++ q₂.edges =
        p.edges.filter (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
    have hn := hp.isTrail.edges_nodup
    rw [← hedges] at hn
    have hf := filter_out_two_of_nodup q₀.edges q₁.edges q₂.edges
      s(ℓ₀, r₀) s(ℓ₁, r₁) hn
    rw [hedges] at hf
    exact hf.symm
  refine ⟨q₀, q₁, q₂, hq₀, hq₁, hq₂, hsupport, hedges, hfiltered, ?_, ?_, ?_⟩
  · simp only [q₀, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length]
    exact Nat.min_eq_left (Nat.le_of_lt hi)
  · simp only [q₁, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.drop_length]
    rw [Nat.min_eq_left (show j - (i + 1) ≤ p.length - (i + 1) by omega)]
    omega
  · simp only [q₂, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length]
    omega

#print axioms exists_path_slicing_at_two_ordered_edges

end D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing

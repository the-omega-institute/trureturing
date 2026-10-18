/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Design
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse incidence designs assemble to weak-four landmark sets. -/

import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Core
import D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension

set_option autoImplicit false
set_option maxRecDepth 2000

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset HammingWeakTwoMetricDimension

/-- Minimum degree two, no four-cycle, and a high vertex on every three-edge path. -/
def Good {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset (α × β)) : Prop :=
  (∀ a, 2 ≤ leftCount S a) ∧ (∀ b, 2 ≤ rightCount S b) ∧
  (∀ a a' b b', a ≠ a' → b ≠ b' →
    (a,b) ∈ S → (a',b) ∈ S → (a',b') ∈ S →
    9 ≤ leftCount S a + leftCount S a' + rightCount S b + rightCount S b') ∧
  (∀ a a' b b', a ≠ a' → b ≠ b' →
    (a,b) ∈ S → (a',b) ∈ S → (a',b') ∈ S → (a,b') ∉ S)

/-- The incidence criterion controls every actual distinct product-graph pair. -/
theorem good_resolves {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n × Fin n))
    (h : Good S) : IsWeakFour S := by
  have hr : ∀ i, 2 ≤ rowDegree S i := h.1
  have hc : ∀ j, 2 ≤ colDegree S j := h.2.1
  intro x y hxy
  rcases x with ⟨i,j⟩
  rcases y with ⟨i',j'⟩
  by_cases hi : i = i'
  · subst i'
    have hj : j ≠ j' := by simpa using hxy
    rw [delta_same_row hn S i j j' hj]
    have := hc j
    have := hc j'
    omega
  by_cases hj : j = j'
  · subst j'
    rw [delta_same_col hn S i i' j hi]
    have := hr i
    have := hr i'
    omega
  have he := delta_rectangle hn S i i' j j' hi hj
  have hri := hr i
  have hri' := hr i'
  have hcj := hc j
  have hcj' := hc j'
  have hp₁ := h.2.2.1 i i' j j' hi hj
  have hp₂ := h.2.2.1 i i' j' j hi (Ne.symm hj)
  have hp₃ := h.2.2.1 i' i j j' (Ne.symm hi) hj
  have hp₄ := h.2.2.1 i' i j' j (Ne.symm hi) (Ne.symm hj)
  have hcycle := h.2.2.2 i i' j j' hi hj
  change ((i,j) ∈ S → (i',j) ∈ S → (i',j') ∈ S →
    9 ≤ rowDegree S i + rowDegree S i' + colDegree S j + colDegree S j') at hp₁
  change ((i,j') ∈ S → (i',j') ∈ S → (i',j) ∈ S →
    9 ≤ rowDegree S i + rowDegree S i' + colDegree S j' + colDegree S j) at hp₂
  change ((i',j) ∈ S → (i,j) ∈ S → (i,j') ∈ S →
    9 ≤ rowDegree S i' + rowDegree S i + colDegree S j + colDegree S j') at hp₃
  change ((i',j') ∈ S → (i,j') ∈ S → (i,j) ∈ S →
    9 ≤ rowDegree S i' + rowDegree S i + colDegree S j' + colDegree S j) at hp₄
  by_cases ha : (i,j) ∈ S <;> by_cases hb : (i',j') ∈ S <;>
    by_cases hc : (i,j') ∈ S <;> by_cases hd : (i',j) ∈ S <;>
    simp only [ha, hb, hc, hd, ite_true, ite_false] at he
  all_goals first
    | exact False.elim (hcycle ha hd hb hc)
    | have hp := hp₁ ha hd hb; omega
    | have hp := hp₂ hc hb hd; omega
    | have hp := hp₃ hd ha hc; omega
    | have hp := hp₄ hb hc ha; omega
    | omega

private theorem join_mem_ll {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ))
    (a : α) (b : β) : (Sum.inl a, Sum.inl b) ∈ join S T ↔ (a,b) ∈ S := by
  simp [join]

private theorem join_mem_rr {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ))
    (a : γ) (b : δ) : (Sum.inr a, Sum.inr b) ∈ join S T ↔ (a,b) ∈ T := by
  simp [join]

private theorem join_mem_lr {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ))
    (a : α) (b : δ) : (Sum.inl a, Sum.inr b) ∉ join S T := by
  simp [join]

private theorem join_mem_rl {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ))
    (a : γ) (b : β) : (Sum.inr a, Sum.inl b) ∉ join S T := by
  simp [join]

/-- Incidence disjoint union preserves the criterion, including cross-block pairs. -/
theorem good_join {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] {S : Finset (α × β)} {T : Finset (γ × δ)}
    (hS : Good S) (hT : Good T) : Good (join S T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (a|a) <;> simp only [join_left_inl, join_left_inr]
    · exact hS.1 a
    · exact hT.1 a
  · rintro (b|b) <;> simp only [join_right_inl, join_right_inr]
    · exact hS.2.1 b
    · exact hT.2.1 b
  · rintro (a|a) (a'|a') (b|b) (b'|b') <;>
      simp only [join_mem_ll, join_mem_rr, join_mem_lr, join_mem_rl,
        ne_eq, Sum.inl.injEq, Sum.inr.injEq, join_left_inl, join_left_inr,
        join_right_inl, join_right_inr, false_implies, implies_true]
    · exact hS.2.2.1 a a' b b'
    · exact hT.2.2.1 a a' b b'
  · rintro (a|a) (a'|a') (b|b) (b'|b') <;>
      simp only [join_mem_ll, join_mem_rr, join_mem_lr, join_mem_rl,
        ne_eq, Sum.inl.injEq, Sum.inr.injEq, false_implies, implies_true, not_false_eq_true]
    · exact hS.2.2.2 a a' b b'
    · exact hT.2.2.2 a a' b b'

/-- Relabeling the two incidence parts preserves every condition. -/
theorem good_map {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (f : α ≃ γ) (g : β ≃ δ)
    {S : Finset (α × β)} (hS : Good S) :
    Good (S.map (f.toEmbedding.prodMap g.toEmbedding)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨a,rfl⟩ := f.surjective a
    simpa [leftCount_map] using hS.1 a
  · intro b
    obtain ⟨b,rfl⟩ := g.surjective b
    simpa [rightCount_map] using hS.2.1 b
  · intro a a' b b'
    obtain ⟨a,rfl⟩ := f.surjective a
    obtain ⟨a',rfl⟩ := f.surjective a'
    obtain ⟨b,rfl⟩ := g.surjective b
    obtain ⟨b',rfl⟩ := g.surjective b'
    simpa [leftCount_map, rightCount_map] using hS.2.2.1 a a' b b'
  · intro a a' b b'
    obtain ⟨a,rfl⟩ := f.surjective a
    obtain ⟨a',rfl⟩ := f.surjective a'
    obtain ⟨b,rfl⟩ := g.surjective b
    obtain ⟨b',rfl⟩ := g.surjective b'
    simpa using hS.2.2.2 a a' b b'

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour

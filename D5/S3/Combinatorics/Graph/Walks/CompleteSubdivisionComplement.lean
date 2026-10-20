/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Complementing the full landmark set preserves all actual edge-profile collisions. -/
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionComplement

open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection

variable {n : ℕ}

theorem full_selectedDegree (u : Fin n) :
    selectedDegree (Finset.univ : Finset (Vertex n)) u = (n : ℤ) - 1 := by
  classical
  cases n with
  | zero => exact u.elim0
  | succ m =>
    rw [selectedDegree_eq_sum_pairBit, Fin.sum_univ_succAbove _ u]
    simp [pairBit, midpointBit, Fin.succAbove_ne, Ne.symm]

theorem full_bins_equal (e f : Sym2 (Vertex n))
    (he : e ∈ (graph n).edgeSet) (hf : f ∈ (graph n).edgeSet) (k : Fin 4) :
    bin Finset.univ e k.val = bin Finset.univ f k.val := by
  classical
  obtain ⟨u, v, h, rfl⟩ := (edge_iff_incidence e).mp he
  obtain ⟨x, y, j, rfl⟩ := (edge_iff_incidence f).mp hf
  have H := histogram (Finset.univ : Finset (Vertex n)) u v h
  have K := histogram (Finset.univ : Finset (Vertex n)) x y j
  dsimp only at H K
  simp only [originalBit, midpointBit, Finset.mem_univ, if_true,
    full_selectedDegree] at H K
  fin_cases k <;> dsimp <;> omega

theorem bin_add_compl (S : Finset (Vertex n)) (e : Sym2 (Vertex n)) (k : ℕ) :
    bin S e k + bin Sᶜ e k = bin Finset.univ e k := by
  classical
  exact Finset.sum_add_sum_compl S (fun s => if edgeDistance s e = k then (1 : ℤ) else 0)

theorem profile_compl_iff (S : Finset (Vertex n)) (e f : Sym2 (Vertex n))
    (he : e ∈ (graph n).edgeSet) (hf : f ∈ (graph n).edgeSet) :
    profile Sᶜ e = profile Sᶜ f ↔ profile S e = profile S f := by
  classical
  have bins (U : Finset (Vertex n)) :
      profile U e = profile U f ↔ ∀ k : Fin 4, bin U e k.val = bin U f k.val := by
    rw [profile_eq_iff_four_counts U U e f he hf]
    simp only [bin_eq_count, Int.natCast_inj]
  rw [bins, bins]
  constructor <;> intro h k
  · have hc := h k
    have h₁ := bin_add_compl S e k.val
    have h₂ := bin_add_compl S f k.val
    have ht := full_bins_equal e f he hf k
    omega
  · have hc := h k
    have h₁ := bin_add_compl S e k.val
    have h₂ := bin_add_compl S f k.val
    have ht := full_bins_equal e f he hf k
    omega

theorem resolves_compl_iff (S : Finset (Vertex n)) : Resolves Sᶜ ↔ Resolves S := by
  classical
  constructor <;> intro h e he f hf hp
  · exact h he hf ((profile_compl_iff S e f he hf).mpr hp)
  · exact h he hf ((profile_compl_iff S e f he hf).mp hp)

theorem selection_compl (S : Finset (Vertex n)) (u v : Fin n) :
    selection Sᶜ u v = 1 - selection S u v := by
  classical
  unfold selection pairBit originalBit midpointBit
  split_ifs <;> simp_all

theorem selection_row_compl (S : Finset (Vertex n)) (u : Fin n) :
    (∑ v, selection Sᶜ u v) + (∑ v, selection S u v) = n := by
  classical
  rw [← Finset.sum_add_distrib]
  have hi (v : Fin n) : selection Sᶜ u v + selection S u v = 1 := by
    rw [selection_compl]
    have := selection_binary S u v
    omega
  simp_rw [hi]
  simp

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionComplement

/- GID: D5/S3/Combinatorics/Graph/Walks/HamiltonConnected
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/HamiltonConnected
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Fixed-endpoint path surgery for the Chvatal-Erdos Hamilton-connectedness criterion. -/
import D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
import D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.HamiltonConnected

open SimpleGraph OrderedTwoCutSlicing
open scoped Classical
universe u
variable {V : Type u} {G : SimpleGraph V}

private lemma append_path {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z ∈ p.support, z ∈ q.support → z = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
  intro z hz w hw heq
  subst heq
  have hz' := hmeet z hz (List.mem_of_mem_tail hw)
  subst hz'
  have hn := hq.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1 hw

/-- The two cuts retain their literal prescribed endpoints, including adjacent cuts. -/
private lemma two_cut_extension [DecidableEq V]
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hij : i < j) (hj : j < p.length)
    (d : G.Walk (p.getVert i) (p.getVert j)) (hd : d.IsPath)
    (hclean : ∀ z ∈ d.support, z ∈ p.support →
      z = p.getVert i ∨ z = p.getVert j)
    (he : G.Adj (p.getVert (i+1)) (p.getVert (j+1))) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + d.length - 1 := by
  obtain ⟨q₀,q₁,q₂,h₀,h₁,h₂,hs,_,_,hl₀,hl₁,hl₂⟩ :=
    exists_path_slicing_at_two_ordered_edges p hp hij hj rfl rfl rfl rfl
  have hn : (q₀.support ++ q₁.support ++ q₂.support).Nodup := hs.symm ▸ hp.support_nodup
  have h01 : q₀.support.Disjoint q₁.support := by
    exact (List.nodup_append.mp (List.nodup_append.mp hn).1).2.2
  have h02 : q₀.support.Disjoint q₂.support := by
    intro z hz w hw heq
    exact (List.nodup_append.mp hn).2.2
      (List.mem_append.mpr (Or.inl hz)) hw heq
  have h12 : q₁.support.Disjoint q₂.support := by
    intro z hz w hw heq
    exact (List.nodup_append.mp hn).2.2
      (List.mem_append.mpr (Or.inr hz)) hw heq
  have hmem₀ : ∀ z ∈ q₀.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hz)))
  have hmem₁ : ∀ z ∈ q₁.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hz)))
  have hmem₂ : ∀ z ∈ q₂.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inr hz)
  have hr : (q₁.reverse.append (Walk.cons he q₂)).IsPath := by
    apply append_path _ _ h₁.reverse
    · rw [Walk.cons_isPath_iff]
      exact ⟨h₂, fun hz => h12 q₁.start_mem_support hz rfl⟩
    · intro z hz hz'
      rw [Walk.support_reverse, List.mem_reverse] at hz
      rw [Walk.support_cons, List.mem_cons] at hz'
      exact hz'.resolve_right (fun hm => h12 hz hm rfl)
  have hdr : (d.append (q₁.reverse.append (Walk.cons he q₂))).IsPath := by
    apply append_path _ _ hd hr
    intro z hz hz'
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse,
      Walk.support_cons, List.mem_cons] at hz'
    have hzp : z ∈ p.support := by
      rcases hz' with hm | rfl | hm
      · exact hmem₁ z hm
      · exact hmem₁ _ q₁.start_mem_support
      · exact hmem₂ z hm
    rcases hclean z hz hzp with heq | heq
    · subst heq
      rcases hz' with hm | heq | hm
      · exact (h01 q₀.end_mem_support hm rfl).elim
      · exact (h01 q₀.end_mem_support q₁.start_mem_support heq).elim
      · exact (h02 q₀.end_mem_support hm rfl).elim
    · exact heq
  let q := q₀.append (d.append (q₁.reverse.append (Walk.cons he q₂)))
  have hq : q.IsPath := by
    apply append_path _ _ h₀ hdr
    intro z hz hz'
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse, Walk.support_cons, List.mem_cons] at hz'
    rcases hz' with hm | hm | heq | hm
    · rcases hclean z hm (hmem₀ z hz) with heq | heq
      · exact heq
      · subst heq; exact (h01 hz q₁.end_mem_support rfl).elim
    · exact (h01 hz hm rfl).elim
    · subst heq; exact (h01 hz q₁.start_mem_support rfl).elim
    · exact (h02 hz hm rfl).elim
  refine ⟨q,hq,?_⟩
  simp only [q, Walk.length_append, Walk.length_reverse, Walk.length_cons]
  omega

end D5.S3.Combinatorics.Graph.Walks.HamiltonConnected

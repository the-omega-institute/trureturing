/- GID: D5/S3/Combinatorics/Graph/StarForming/Comparison
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Comparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Maximal dissociation selections are minimal two-star-forming. -/

import D5.S3.Combinatorics.Graph.StarForming.Semantics
import D5.S3.Combinatorics.Graph.StarForming.DisjointUnion

namespace D5.S3.Combinatorics.Graph.StarForming
open StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A selected vertex of a dissociation set fails its own deletion test. -/
theorem independent_self_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hi : IsKIndependent G 2 S) (v : V) (hv : v ∈ S) :
    ¬ Amplification.TwoAt G (↑(S.erase v)) v := by
  have h := (SubQuorum.DoubleStarGrafting.independent_iff G S).mp hi
  rintro (⟨a,ha,b,hb,hab,hva,hvb⟩ | ⟨c,hc,hvc,l,hl,hcl⟩)
  · exact hab (h v hv a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hva hvb)
  · have hcv : G.Adj c v := G.adj_symm hvc
    have he := h c (Finset.mem_erase.mp hc).2 v hv l (Finset.mem_erase.mp hl).2 hcv hcl
    exact (Finset.mem_erase.mp hl).1 he.symm

/-- If an outside vertex is not covered, adjoining it preserves dissociation. -/
theorem independent_insert_of_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hi : IsKIndependent G 2 S) (x : V) (hx : x ∉ S)
    (hfail : ¬ Amplification.TwoAt G (↑S) x) :
    IsKIndependent G 2 (insert x S) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff G _).mpr
  have h := (SubQuorum.DoubleStarGrafting.independent_iff G S).mp hi
  intro c hc a ha b hb hca hcb
  rcases Finset.mem_insert.mp hc with rfl | hcS
  · have haS := (Finset.mem_insert.mp ha).resolve_left (by
      intro heq; subst a; exact G.irrefl hca)
    have hbS := (Finset.mem_insert.mp hb).resolve_left (by
      intro heq; subst b; exact G.irrefl hcb)
    by_contra hne
    exact hfail (Or.inl ⟨a,haS,b,hbS,hne,hca,hcb⟩)
  · rcases Finset.mem_insert.mp ha with rfl | haS
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · rfl
      · exact False.elim (hfail (Or.inr ⟨c,hcS,G.adj_symm hca,b,hbS,hcb⟩))
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact False.elim (hfail (Or.inr ⟨c,hcS,G.adj_symm hcb,a,haS,hca⟩))
      · exact h c hcS a haS b hbS hca hcb

/-- Every inclusion-maximal dissociation set is minimal star-forming. -/
theorem maximal_independent_minimal (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hi : IsKIndependent G 2 S)
    (hmax : ∀ x, x ∉ S → ¬ IsKIndependent G 2 (insert x S)) :
    IsMinimalStarForming G 2 S := by
  apply (minimal_iff G S).mp
  apply Amplification.minimal_of_deletion_failures
  · intro x hx
    by_contra hn
    exact hmax x hx (independent_insert_of_failure G S hi x hx hn)
  · intro v hv
    refine ⟨v,?_,?_⟩
    · simp
    · simpa using independent_self_failure G S hi v hv

/-- The classical dissociation lower comparison, with actual finite maxima. -/
theorem beta_le_sf (G : SimpleGraph V) [DecidableRel G.Adj] : beta G 2 ≤ SF G 2 := by
  classical
  obtain ⟨S,hi,hcard⟩ := beta_attained G 2
  have hm : IsMinimalStarForming G 2 S := by
    apply maximal_independent_minimal G S hi
    intro x hx hins
    have hh : (insert x S).card ≤ beta G 2 := Finset.le_sup
      (Finset.mem_filter.mpr ⟨by simp,hins⟩)
    rw [Finset.card_insert_of_notMem hx,hcard] at hh
    omega
  rw [← hcard]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hm⟩)

end D5.S3.Combinatorics.Graph.StarForming

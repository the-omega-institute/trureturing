/- GID: D5/S3/Combinatorics/Graph/StarForming/FiniteCover
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/FiniteCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact finite fiber counts and canonical maxima under local graph covers. -/

import D5.S3.Combinatorics.Graph.StarForming.Semantics
import D5.S3.Combinatorics.Graph.StarForming.CoverStability
import D5.S3.Combinatorics.Graph.StarForming.DissociationCover
import Mathlib.Algebra.Order.Ring.Finset

namespace D5.S3.Combinatorics.Graph.StarForming

open StarFormingDissociationRefutation

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The relational presentation uses exactly the canonical non-induced stars. -/
theorem regular_forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Regular.Forms G.Adj (· ∈ S) ↔ IsStarForming G 2 S := by
  rw [← forms_iff]
  constructor
  · intro h x hx
    rcases h x hx with ⟨a,b,ha,hb,hab,hxa,hxb⟩ | ⟨c,l,hc,hl,hxc,hcl⟩
    · exact Or.inl ⟨a,ha,b,hb,hab,hxa,hxb⟩
    · exact Or.inr ⟨c,hc,hxc,l,hl,hcl⟩
  · intro h x hx
    rcases h x hx with ⟨a,ha,b,hb,hab,hxa,hxb⟩ | ⟨c,hc,hxc,l,hl,hcl⟩
    · exact Or.inl ⟨a,b,ha,hb,hab,hxa,hxb⟩
    · exact Or.inr ⟨c,l,hc,hl,hxc,hcl⟩

/-- No finiteness or minimality hypothesis is lost in the predicate bridge. -/
theorem regular_minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Regular.Minimal G.Adj (· ∈ S) ↔ IsMinimalStarForming G 2 S := by
  classical
  constructor
  · rintro ⟨hf,hm⟩
    refine ⟨(regular_forms_iff _ _).mp hf, ?_⟩
    intro T hT hforms
    have hex : ∃ x, x ∈ S ∧ x ∉ T := by
      by_contra h
      have hback : S ⊆ T := by
        intro x hx
        by_contra hn
        exact h ⟨x,hx,hn⟩
      exact hT.2 hback
    exact hm (· ∈ T) (fun _ h => hT.1 h) hex ((regular_forms_iff _ _).mpr hforms)
  · rintro ⟨hf,hm⟩
    refine ⟨(regular_forms_iff _ _).mpr hf, ?_⟩
    intro T hsub ⟨x,hx,hnot⟩ hforms
    let U := Finset.univ.filter T
    have hU (v : V) : v ∈ U ↔ T v := by simp [U]
    have hproper : U ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨fun v hv => hsub v ((hU v).mp hv), ?_⟩
      intro heq
      exact hnot ((hU x).mp (heq ▸ hx))
    apply hm U hproper
    apply (regular_forms_iff _ _).mp
    simpa only [hU] using hforms

/-- Count the whole inverse image from its actual constant finite fibers.
This does not impose global surjectivity when the fiber size is zero. -/
theorem card_preimage_uniform (p : W → V) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (S : Finset V) :
    (Finset.univ.filter (fun w => p w ∈ S)).card = k * S.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := p) (t := S)
    (by intro w hw; exact (Finset.mem_filter.mp hw).2)]
  calc
    ∑ v ∈ S, ((Finset.univ.filter (fun w => p w ∈ S)).filter (fun w => p w = v)).card =
        ∑ _v ∈ S, k := by
      apply Finset.sum_congr rfl
      intro v hv
      have he : (Finset.univ.filter (fun w => p w ∈ S)).filter (fun w => p w = v) =
          Finset.univ.filter (fun w => p w = v) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun h => ⟨h ▸ hv,h⟩⟩
      rw [he, hk]
    _ = k * S.card := by simp [Nat.mul_comm]

/-- Minimality pulls back from safe deletion certificates under a local cover.
NeighborhoodCover contains no global projection-surjectivity field. -/
theorem minimal_preimage_of_safe (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (S : Finset V)
    (hS : IsMinimalStarForming G 2 S)
    (hsafe : CoverPullback.HasSafeCertificates G.Adj (· ∈ S)) :
    IsMinimalStarForming H 2 (Finset.univ.filter (fun w => p w ∈ S)) := by
  classical
  apply (regular_minimal_iff _ _).mp
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    CoverPullback.minimal_pullback_of_safe_certificates cover (fun _ => G.irrefl)
      (fun _ _ h => G.adj_symm h) (fun _ _ h => H.adj_symm h)
      ((regular_minimal_iff _ _).mpr hS).1 hsafe

/-- Uniform local covers multiply any safely certified attained selection. -/
theorem sf_mul_le_of_safe (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k)
    (hsafe : ∀ S : Finset V, IsMinimalStarForming G 2 S →
      CoverPullback.HasSafeCertificates G.Adj (· ∈ S)) :
    k * SF G 2 ≤ SF H 2 := by
  classical
  change k * (Finset.univ.powerset.filter (IsMinimalStarForming G 2)).sup Finset.card ≤ _
  rw [Finset.mul_sup₀]
  apply Finset.sup_le
  intro S hS
  have hm := (Finset.mem_filter.mp hS).2
  have hlift := minimal_preimage_of_safe G H p cover S hm (hsafe S hm)
  rw [← card_preimage_uniform p k hk S]
  exact Finset.le_sup (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hlift⟩)

/-- Local injectivity suffices for the dissociation lower bound, even with
zero fibers; the converse pullback theorem separately needs surjectivity. -/
theorem beta_mul_le (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    k * beta G 2 ≤ beta H 2 := by
  classical
  change k * (Finset.univ.powerset.filter (IsKIndependent G 2)).sup Finset.card ≤ _
  rw [Finset.mul_sup₀]
  apply Finset.sup_le
  intro S hS
  have hm := (SubQuorum.DoubleStarGrafting.independent_iff G S).mp
    (Finset.mem_filter.mp hS).2
  let T := Finset.univ.filter (fun w => p w ∈ S)
  have hi : IsKIndependent H 2 T := by
    apply (SubQuorum.DoubleStarGrafting.independent_iff H T).mpr
    intro c hc a ha b hb hca hcb
    apply cover.neighbor_injective c a b hca hcb
    exact hm (p c) (Finset.mem_filter.mp hc).2
      (p a) (Finset.mem_filter.mp ha).2 (p b) (Finset.mem_filter.mp hb).2
      (cover.map_edge _ _ hca) (cover.map_edge _ _ hcb)
  rw [← card_preimage_uniform p k hk S]
  exact Finset.le_sup (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ T),hi⟩)

end D5.S3.Combinatorics.Graph.StarForming

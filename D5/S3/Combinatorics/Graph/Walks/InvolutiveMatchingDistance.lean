/- GID: D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Walk.Maps, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: A finite walk with involutive matching edges reduces to a base walk and at most one matching step. -/
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InvolutiveMatchingDistance
open SimpleGraph
noncomputable section
variable {V : Type} {G : SimpleGraph V}

/-- The extension retains the original vertices and adds the actual automorphism matching. -/
def extension (e : G ≃g G) : SimpleGraph V := G ⊔ SimpleGraph.fromRel (fun u v => e u=v)

private theorem base_le (e : G ≃g G) : G ≤ extension e := le_sup_left

/-- Every finite extension walk has a base-graph representative with at most one matching edge. -/
theorem walk_normal_form (e : G ≃g G) (he : ∀ u : V, e (e u)=u)
    {u v : V} (p : (extension e).Walk u v) :
    (∃ q : G.Walk u v, q.length ≤ p.length) ∨
      (∃ q : G.Walk (e u) v, q.length+1 ≤ p.length) := by
  induction p with
  | nil => exact Or.inl ⟨.nil,le_rfl⟩
  | @cons u v w huv p ih =>
    change G.Adj u v ∨ (u≠v ∧ (e u=v ∨ e v=u)) at huv
    rcases huv with huv | ⟨_,huv⟩
    · rcases ih with ⟨q,hq⟩ | ⟨q,hq⟩
      · exact Or.inl ⟨q.cons huv,by change q.length+1 ≤ p.length+1; omega⟩
      · exact Or.inr ⟨q.cons (e.toHom.map_adj huv),by change (q.length+1)+1 ≤ p.length+1; omega⟩
    · have huv' : e u=v := by
        rcases huv with h | h
        · exact h
        · simpa only [he] using congrArg e h.symm
      rcases ih with ⟨q,hq⟩ | ⟨q,hq⟩
      · exact Or.inr ⟨q.copy huv'.symm rfl,by simp only [Walk.length_copy]; change q.length+1 ≤ p.length+1; omega⟩
      · have hev : e v=u := by rw [← huv',he]
        exact Or.inl ⟨q.copy hev rfl,by simp only [Walk.length_copy]; change q.length ≤ p.length+1; omega⟩

/-- The finite-walk normal form gives the exact distance in every connected involutive extension. -/
theorem distance (hc : G.Connected) (e : G ≃g G) (he : ∀ u : V, e (e u)=u)
    (u v : V) :
    (extension e).dist u v = min (G.dist u v) (1+G.dist (e u) v) := by
  have hconn : (extension e).Connected := hc.mono (base_le e)
  apply le_antisymm
  · apply le_min
    · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
      have hh := SimpleGraph.dist_le (p.map (Hom.ofLE (base_le e)))
      change (extension e).dist u v ≤ _ at hh
      simpa only [Walk.length_map,hp] using hh
    · by_cases hfix : u=e u
      · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
        have hh := SimpleGraph.dist_le (p.map (Hom.ofLE (base_le e)))
        change (extension e).dist u v ≤ _ at hh
        simp only [Walk.length_map,hp] at hh
        rw [← hfix]
        omega
      · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (e u) v
        have hstep : (extension e).Adj u (e u) := Or.inr ⟨hfix,Or.inl rfl⟩
        have hh := SimpleGraph.dist_le ((p.map (Hom.ofLE (base_le e))).cons hstep)
        change (extension e).dist u v ≤ _ at hh
        simp only [Walk.length_cons,Walk.length_map,hp] at hh
        omega
  · obtain ⟨p,hp⟩ := hconn.exists_walk_length_eq_dist u v
    rcases walk_normal_form e he p with ⟨q,hq⟩ | ⟨q,hq⟩
    · exact (min_le_left _ _).trans ((SimpleGraph.dist_le q).trans (hq.trans_eq hp))
    · exact (min_le_right _ _).trans (by have hh := (SimpleGraph.dist_le q); omega)

end
end InvolutiveMatchingDistance

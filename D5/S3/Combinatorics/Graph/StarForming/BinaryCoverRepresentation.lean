/- GID: D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Every actual two-element-fiber neighborhood cover is a binary voltage lift. -/

import D5.S3.Combinatorics.Graph.StarForming.BinaryLift
import Mathlib.Data.Fintype.EquivFin

/-! The passage from an arbitrary two-sheeted neighborhood cover to signings
in HEAWOOD_DOUBLE_COVER_GAIN, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69. Global surjectivity is supplied
by the explicit two-element fiber hypothesis; it is not built into the local
cover predicate. No connectedness hypothesis is needed for representation. -/
namespace D5.S3.Combinatorics.Graph.StarForming.BinaryCoverRepresentation
open BinaryLift Classical

variable {V : Type} (G : SimpleGraph V) (H : SimpleGraph (V × F2))

noncomputable def sign (v w : V) : F2 := if H.Adj (v,0) (w,0) then 0 else 1

noncomputable def voltage : Voltage G where
  sign := sign H
  symmetric v w _ := by
    unfold sign
    rw [show H.Adj (v,0) (w,0) ↔ H.Adj (w,0) (v,0) from
      ⟨H.adj_symm,H.adj_symm⟩]

private theorem fiber_neighbor (c : CoverPullback.NeighborhoodCover G.Adj H.Adj Prod.fst)
    (v w : V) (a : F2) (h : G.Adj v w) :
    H.Adj (v,a) (w,0) ∨ H.Adj (v,a) (w,1) := by
  obtain ⟨⟨u,b⟩,hu,he⟩ := c.neighbor_surjective (v,a) w h
  change u=w at he
  subst u
  have hc : ∀ b : F2, b=0 ∨ b=1 := by decide +kernel
  rcases hc b with rfl | rfl
  · exact Or.inl hu
  · exact Or.inr hu

/-- Local bijectivity forces each edge's two-sheet incidence matrix to be
one of the two permutation matrices, so its adjacency is an actual XOR law. -/
theorem adjacency (c : CoverPullback.NeighborhoodCover G.Adj H.Adj Prod.fst)
    (v w : V) (a b : F2) :
    H.Adj (v,a) (w,b) ↔ G.Adj v w ∧ a+b=sign H v w := by
  classical
  by_cases hg : G.Adj v w
  · have h0 := fiber_neighbor G H c v w 0 hg
    have h1 := fiber_neighbor G H c v w 1 hg
    have hc0 := fiber_neighbor G H c w v 0 (G.adj_symm hg)
    have hc1 := fiber_neighbor G H c w v 1 (G.adj_symm hg)
    have hne : (0 : F2)≠1 := by decide +kernel
    have excl (x : V × F2) (u : V) :
        ¬ (H.Adj x (u,0) ∧ H.Adj x (u,1)) := by
      rintro ⟨h,h'⟩
      exact hne (congrArg Prod.snd (c.neighbor_injective x (u,0) (u,1) h h' rfl))
    have he0 := excl (v,0) w
    have he1 := excl (v,1) w
    have he2 := excl (w,0) v
    have he3 := excl (w,1) v
    simp only [H.adj_comm (w,0) (v,0),H.adj_comm (w,0) (v,1)] at hc0 he2
    simp only [H.adj_comm (w,1) (v,0),H.adj_comm (w,1) (v,1)] at hc1 he3
    have h00 : H.Adj (v,0) (w,0) ↔ H.Adj (v,1) (w,1) := by tauto
    have h01 : H.Adj (v,0) (w,1) ↔ H.Adj (v,1) (w,0) := by tauto
    have hab : ∀ a : F2, a=0 ∨ a=1 := by decide +kernel
    have htwo : (1 : F2)+1=0 := by decide +kernel
    rcases hab a with rfl | rfl <;> rcases hab b with rfl | rfl <;>
      by_cases hz : H.Adj (v,0) (w,0) <;>
      simp_all [sign,htwo]
  · constructor
    · intro h
      exact (hg (c.map_edge _ _ h)).elim
    · exact fun h => (hg h.1).elim

/-- The labeled cover is actually isomorphic to its binary voltage graph. -/
noncomputable def labeledIso (c : CoverPullback.NeighborhoodCover G.Adj H.Adj Prod.fst) :
    H ≃g BinaryLift.graph G (voltage G H) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    rintro ⟨v,a⟩ ⟨w,b⟩
    exact (adjacency G H c v w a b).symm

variable {U : Type} [Fintype U] (p : U → V)

noncomputable def label (h : ∀ v, Fintype.card {u // p u=v}=2) : U ≃ (V × F2) :=
  (Equiv.sigmaFiberEquiv p).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fun v => Fintype.equivOfCardEq
      (show Fintype.card {u // p u=v}=Fintype.card F2 by simpa [ZMod.card] using h v)))

private theorem label_first (h : ∀ v, Fintype.card {u // p u=v}=2) (u : U) :
    (label p h u).1=p u := rfl

private theorem label_symm_first (h : ∀ v, Fintype.card {u // p u=v}=2) (x : V × F2) :
    p ((label p h).symm x)=x.1 := by
  have he := label_first p h ((label p h).symm x)
  simpa using he.symm

/-- Uniform two-element fibers produce a true binary-lift representation of
an arbitrary neighborhood cover, with no original labeling assumption. -/
theorem representation (K : SimpleGraph U)
    (c : CoverPullback.NeighborhoodCover G.Adj K.Adj p)
    (h : ∀ v, Fintype.card {u // p u=v}=2) :
    ∃ s : Voltage G, Nonempty (K ≃g BinaryLift.graph G s) := by
  classical
  let e := label p h
  let L := K.comap e.symm
  have hep : ∀ x : V × F2, p (e.symm x)=x.1 := label_symm_first p h
  have hc : CoverPullback.NeighborhoodCover G.Adj L.Adj Prod.fst := by
    constructor
    · intro x y hxy
      have hh := c.map_edge _ _ hxy
      rw [hep x,hep y] at hh
      exact hh
    · intro x v hxv
      obtain ⟨y,hy,he⟩ := c.neighbor_surjective (e.symm x) v
        ((hep x).symm ▸ hxv)
      refine ⟨e y,?_,?_⟩
      · change K.Adj (e.symm x) (e.symm (e y))
        simpa using hy
      · exact (label_first p h y).trans he
    · intro x y z hxy hxz he
      apply e.symm.injective
      apply c.neighbor_injective (e.symm x) _ _ hxy hxz
      exact (hep y).trans (he.trans (hep z).symm)
  let f : K ≃g L := {
    toEquiv := e
    map_rel_iff' := by intro x y; change K.Adj (e.symm (e x)) (e.symm (e y)) ↔ _; simp }
  exact ⟨voltage G L,⟨f.trans (labeledIso G L hc)⟩⟩

end D5.S3.Combinatorics.Graph.StarForming.BinaryCoverRepresentation

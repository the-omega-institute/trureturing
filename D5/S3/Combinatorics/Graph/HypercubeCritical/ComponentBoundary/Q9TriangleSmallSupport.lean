/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TriangleSmallSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TriangleSmallSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A nonempty triangle support of at most five faces is carried by four vertices. -/

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Interval.Finset.Nat

/-! Small real triangle supports can be ruled out using just the absence of
singleton edge incidences. Complementation on five vertices gives a graph
with no induced triple containing exactly one edge. Its nonadjacency classes
are the parts of a complete multipartite graph. A five-vertex partition yields
0, 4, 6, 7, 8, 9, or 10 edges. In the four-edge case all triangles lie on the
four-vertex part of the partition. -/

set_option autoImplicit false

namespace Q9TriangleSmallSupport

open Finset

private abbrev Face := Finset (Fin 5)

private def edges : Finset Face := (univ : Face).powersetCard 2

private def triangles : Finset Face := (univ : Face).powersetCard 3

private theorem smallFamilies :
    ∀ k ∈ Icc (1 : ℕ) 5, ∀ C ∈ triangles.powersetCard k,
      (∀ e ∈ edges, (C.filter (e ⊆ ·)).card ≠ 1) →
      k = 4 ∧ ∃ T ∈ (univ : Face).powersetCard 4, C = T.powersetCard 3 := by
  decide +kernel

/-- In a nonempty family of at most five triangles on five vertices,
the absence of singleton edge incidences forces a tetrahedron boundary. -/
theorem tetrahedron_boundary (C : Finset (Finset (Fin 5)))
    (hsize : ∀ t ∈ C, t.card = 3) (hpositive : 1 ≤ C.card) (hsmall : C.card ≤ 5)
    (hclosed : ∀ e : Finset (Fin 5), e.card = 2 → (C.filter (e ⊆ ·)).card ≠ 1) :
    C.card = 4 ∧ ∃ T : Finset (Fin 5), T.card = 4 ∧ C = T.powersetCard 3 := by
  have hC : C ∈ triangles.powersetCard C.card :=
    mem_powersetCard.mpr
      ⟨fun t ht => mem_powersetCard.mpr ⟨subset_univ t, hsize t ht⟩, rfl⟩
  obtain ⟨hcard, T, hT, rfl⟩ :=
    smallFamilies C.card (mem_Icc.mpr ⟨hpositive, hsmall⟩) C hC
      (fun e he => hclosed e (mem_powersetCard.mp he).2)
  exact ⟨hcard, T, (mem_powersetCard.mp hT).2, rfl⟩

/-- Relabel a family on at most five vertices. A pair with one incident
triangle in the image would come from a pair with one incident triangle in
the original family. -/
theorem carried_by_four {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V ≤ 5) (C : Finset (Finset V))
    (hsize : ∀ t ∈ C, t.card = 3) (hpositive : 1 ≤ C.card) (hsmall : C.card ≤ 5)
    (hclosed : ∀ e : Finset V, e.card = 2 → (C.filter (e ⊆ ·)).card ≠ 1) :
    C.card = 4 ∧ ∃ W : Finset V, W.card ≤ 4 ∧ ∀ t ∈ C, t ⊆ W := by
  obtain ⟨f⟩ : Nonempty (V ↪ Fin 5) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  let g := (mapEmbedding f).toEmbedding
  let D := C.map g
  have hcard : D.card = C.card := by simp [D]
  have hdsize : ∀ t ∈ D, t.card = 3 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_map.mp ht
    change (s.map f).card = 3
    simpa using hsize s hs
  have hdclosed : ∀ e : Face, e.card = 2 → (D.filter (e ⊆ ·)).card ≠ 1 := by
    intro e he hone
    obtain ⟨t, ht⟩ := card_eq_one.mp hone
    have htd : t ∈ D.filter (e ⊆ ·) := by simp [ht]
    obtain ⟨htD, hsub⟩ := mem_filter.mp htd
    obtain ⟨s, hs, rfl⟩ := mem_map.mp htD
    let a : Finset V := s.filter fun x => f x ∈ e
    have hmap : a.map f = e := by
      ext x
      constructor
      · rintro hx
        obtain ⟨v, hv, rfl⟩ := mem_map.mp hx
        exact (mem_filter.mp hv).2
      · intro hx
        have hxs : x ∈ s.map f := hsub hx
        obtain ⟨v, hv, rfl⟩ := mem_map.mp hxs
        exact mem_map.mpr ⟨v, mem_filter.mpr ⟨hv, hx⟩, rfl⟩
    have ha : a.card = 2 := by rw [← card_map f, hmap, he]
    have hfilter : D.filter (e ⊆ ·) = (C.filter (a ⊆ ·)).map g := by
      change (C.map g).filter (e ⊆ ·) = (C.filter (a ⊆ ·)).map g
      rw [filter_map]
      congr 1
      ext s
      simp [Function.comp_def, g, ← hmap]
    apply hclosed a ha
    rwa [hfilter, card_map] at hone
  obtain ⟨hfour, W, hW, hfamily⟩ :=
    tetrahedron_boundary D hdsize (by omega) (by omega) hdclosed
  let X : Finset V := univ.filter fun x => f x ∈ W
  have hmap : X.map f ⊆ W := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact (mem_filter.mp hx).2
  refine ⟨hcard.symm.trans hfour, X, ?_, ?_⟩
  · have h := card_le_card hmap
    rwa [card_map, hW] at h
  · intro t ht x hx
    have htD : t.map f ∈ D := mem_map.mpr ⟨t, ht, rfl⟩
    have hsub : t.map f ⊆ W := (mem_powersetCard.mp (hfamily ▸ htD)).1
    exact mem_filter.mpr ⟨mem_univ x, hsub (mem_map.mpr ⟨x, hx, rfl⟩)⟩

/-- On at most five vertices the possible nonzero support of at most five
triangles has order four. -/
theorem no_five_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V ≤ 5) (C : Finset (Finset V))
    (hsize : ∀ t ∈ C, t.card = 3)
    (hclosed : ∀ e : Finset V, e.card = 2 → (C.filter (e ⊆ ·)).card ≠ 1) :
    C.card ≠ 5 := by
  intro h
  have hfour := (carried_by_four hV C hsize (by omega) (by omega) hclosed).1
  omega

end Q9TriangleSmallSupport

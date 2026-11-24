/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CappedTriangleLinkFive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CappedTriangleLinkFive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A nonempty capped triangle link on five vertices is the bipyramid over a triangle. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-! Complementing a three-set on five vertices gives an edge. The no-singleton
condition says no triple contains exactly one complementary edge, so
nonadjacency is an equivalence relation. The four-set cap gives maximum
degree three, so the only nonempty complete multipartite graph has parts
of size two and three. -/

set_option autoImplicit false

namespace Q9CappedTriangleLinkFive

open Finset

private abbrev Face := Finset (Fin 5)
private abbrev Family := Finset Face

private def faces (rank : ℕ) : Family := (univ : Face).powersetCard rank

set_option maxRecDepth 16384 in
set_option maxHeartbeats 15000000 in
-- Evaluate just the 1024 subfamilies of ten triangles in the kernel.
private theorem classify :
    ∀ C ∈ (faces 3).powerset,
      C.Nonempty →
      (∀ e ∈ faces 2, (C.filter (e ⊆ ·)).card ≠ 1) →
      (∀ W ∈ faces 4, (C.filter (· ⊆ W)).card ≤ 3) →
      C.card = 6 ∧ ∃ part ∈ faces 2,
        C = (faces 3).filter (fun t => (t ∩ part).card = 1) := by
  decide +kernel

/-- On five vertices, a nonempty family of triangles with no singleton
edge and at most three triangles in any four-set is a triangular
bipyramid. Each face has one vertex from the two-element part. -/
theorem triangular_bipyramid (C : Finset (Finset (Fin 5)))
    (hRank : ∀ t ∈ C, t.card = 3) (hNonempty : C.Nonempty)
    (hNo : ∀ e : Face, e.card = 2 → (C.filter (e ⊆ ·)).card ≠ 1)
    (hCap : ∀ W : Face, W.card = 4 → (C.filter (· ⊆ W)).card ≤ 3) :
    C.card = 6 ∧ ∃ part : Face, part.card = 2 ∧
      (∀ t : Face, t ∈ C ↔ t.card = 3 ∧ (t ∩ part).card = 1) := by
  have hC : C ∈ (faces 3).powerset :=
    mem_powerset.mpr (fun t ht => mem_powersetCard.mpr ⟨subset_univ t, hRank t ht⟩)
  obtain ⟨hc, part, hp, hEq⟩ := classify C hC hNonempty
    (fun e he => hNo e (mem_powersetCard.mp he).2)
    (fun W hw => hCap W (mem_powersetCard.mp hw).2)
  refine ⟨hc, part, (mem_powersetCard.mp hp).2, ?_⟩
  intro t
  simp [hEq, faces]

end Q9CappedTriangleLinkFive

/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyFibres
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyFibres
   mirror-E: none(waiver:shared-label-fibres)
   anchors: [mathlib/module/Mathlib.Combinatorics.Pigeonhole]
   utility: none
   digest: Equal forward-edge labels form complementary cliques. -/

import Mathlib.Combinatorics.Pigeonhole
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyColoring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open Finset

/-- A forward-edge increasing label separates every edge inside one fibre. -/
theorem label_fiber_clique {n d : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin d)
    (hr : ∀ u v, u < v → G.Adj u v → r u < r v) :
    ∀ c, Gᶜ.IsClique ((univ.filter fun v => r v = c) : Set (Fin n)) := by
  classical
  intro c u hu v hv hne
  have hur := (mem_filter.mp hu).2
  have hvr := (mem_filter.mp hv).2
  apply (SimpleGraph.compl_adj _ _ _).mpr
  refine ⟨hne, ?_⟩
  intro hG
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := hr u v h hG
    rw [hur, hvr] at hlt
    exact (lt_irrefl _ hlt)
  · have hlt := hr v u h hG.symm
    rw [hur, hvr] at hlt
    exact (lt_irrefl _ hlt)

end D5.S3.Combinatorics.DihedralRamsey

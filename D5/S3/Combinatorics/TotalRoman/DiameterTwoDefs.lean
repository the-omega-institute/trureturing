/- GID: D5/S3/Combinatorics/TotalRoman/DiameterTwoDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/DiameterTwoDefs
   mirror-E: none(waiver:mynhardt-ogden-question-one-statement)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Diam]
   utility: none
   digest: Mynhardt and Ogden's Question 1 on connected 6-γ_tR-edge-supercritical graphs of diameter 2, in a form for every order n ≥ 10. -/

import Mathlib.Combinatorics.SimpleGraph.Diam
import D5.S3.Combinatorics.TotalRoman.SupercriticalDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.DiameterTwoDefs

open SupercriticalDefs

/-! Fixed public statement: C. M. Mynhardt and S. E. A. Ogden, *Total Roman Domination
    Edge-Supercritical and Edge-Removal-Supercritical Graphs*, Australas. J. Combin. 78(3) (2020),
    arXiv:2002.01347v1, Section 10: "Question 1. Do there exist connected 6-γ_tR-edge-supercritical
    graphs with diameter 2?" A k-γ_tR-edge-supercritical graph is a γ_tR-edge-supercritical graph
    with γ_tR(G) = k (definitions in `SupercriticalDefs`). The affirmative answer is recorded in the
    stronger form `claim`: such graphs exist on n vertices for every n ≥ 10. -/

/-- Question 1, affirmative answer for every order `n ≥ 10`. -/
def claim : Prop :=
  ∀ n : ℕ, 10 ≤ n → ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ G.diam = 2 ∧ Supercritical G ∧ gammaTR G = 6

end D5.S3.Combinatorics.TotalRoman.DiameterTwoDefs

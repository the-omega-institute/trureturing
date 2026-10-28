/- GID: D5/S3/Combinatorics/MinimalForts/OctahedronBlock
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/OctahedronBlock
   mirror-E: none(waiver:finite-block-ingredient)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite]
   utility: none
   digest: Exact full minimal-fort and rooted minimal-fort counts of the six-vertex octahedral block. -/

import D5.S3.Combinatorics.MinimalForts.UniversalRoot
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-! The octahedral graph is the complete equipartite graph with three parts of size two. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.OctahedronBlock

open D5.S3.Combinatorics.MinimalForts.UniversalRoot

/-- The actual six-vertex complete tripartite graph. -/
def octahedron : SimpleGraph (Fin 3 × Fin 2) := SimpleGraph.completeEquipartiteGraph 3 2

instance : DecidableRel octahedron.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.completeEquipartiteGraph 3 2).Adj)

set_option maxRecDepth 10000 in
/-- Exact counts enumerate all actual subsets and all their possible fort subsets. -/
theorem octahedron_block :
    Fintype.card (Fin 3 × Fin 2) = 6 ∧
    (minimalForts octahedron).card = 11 ∧
    (rootedChoices octahedron).card = 12 ∧
    ∀ v, ∃ w, octahedron.Adj v w := by
  decide +kernel

end D5.S3.Combinatorics.MinimalForts.OctahedronBlock

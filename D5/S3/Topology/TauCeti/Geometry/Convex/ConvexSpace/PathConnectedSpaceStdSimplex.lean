/- GID: D5/S3/Topology/TauCeti/Geometry/Convex/ConvexSpace/PathConnectedSpaceStdSimplex
   generality: G
   mirror-B: none(waiver:upstream-support-documented-in-module)
   mirror-E: none(waiver:abstract-support-without-experimental-evidence)
   anchors: []
   utility: none
   digest: TauCeti port: The interval parametrization of the one-simplex; sphere support. -/

import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/Geometry/Convex/ConvexSpace/PathConnectedSpaceStdSimplex.lean`. Changes: import paths are namespaced under
`D5.S3.Topology.TauCeti` for this repository's pinned Mathlib. The original
Tau Ceti copyright and Apache-2.0 terms are retained in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`. Retire this port only
when this repository's own pinned Mathlib provides an equivalent declaration
at the full telescope and all live consumers compile with direct replacement.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The parametrization of the standard `1`-simplex by the unit interval

Values of Mathlib's homeomorphism `Convexity.StdSimplex.homeomorphI` between the standard
`1`-simplex and the unit interval: it is the last weight (`homeomorphI_apply_eq_mk`), and it sends
the two faces of the standard `1`-simplex, its vertices, to `1` and `0`
(`homeomorphI_map_succAbove_zero`, `homeomorphI_map_succAbove_one`).
-/

public section

namespace Convexity.StdSimplex

/-- The parameter of a point of the standard `1`-simplex is its last weight. -/
lemma homeomorphI_apply_eq_mk (w : StdSimplex ℝ (Fin 2)) :
    homeomorphI w = ⟨w.weights 1, w.weights_nonneg 1, w.weights_apply_le_one 1⟩ :=
  Subtype.ext (homeomorphI_apply_coe w)

/-- The `0`-th face of the standard `1`-simplex is its last vertex, of parameter `1`. -/
-- Not a simp lemma: `Fin.succAbove_zero` rewrites the face map first.
lemma homeomorphI_map_succAbove_zero (w : StdSimplex ℝ (Fin 1)) :
    homeomorphI (map (Fin.succAbove (0 : Fin 2)) w) = 1 := by
  rw [Subsingleton.elim w (single 0), map_single]
  exact homeomorphI_single_one

/-- The `1`-st face of the standard `1`-simplex is its first vertex, of parameter `0`. -/
@[simp]
lemma homeomorphI_map_succAbove_one (w : StdSimplex ℝ (Fin 1)) :
    homeomorphI (map (Fin.succAbove (1 : Fin 2)) w) = 0 := by
  rw [Subsingleton.elim w (single 0), map_single]
  exact homeomorphI_single_zero

end Convexity.StdSimplex

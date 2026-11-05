/- GID: D5/S3/Topology/SphereBrouwerObstruction
   generality: G
   mirror-B: D5/B/S3/Topology/SphereBrouwerObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Homotopy.Contractible]
   utility: none
   digest: A positive-dimensional Euclidean sphere is not contractible, by a lawful TauCeti source port. -/

import D5.S3.Topology.TauCeti.AlgebraicTopology.Sphere.Contractible

set_option autoImplicit false

open Metric
open scoped Topology

noncomputable section

namespace D5.S3.Topology.SphereBrouwerObstruction

/-!
The exact endpoint is adopted from `TauCeti.not_contractibleSpace_sphere` by source port.
The port is required because the supplier pins Mathlib `ccbef15ebdb41c2addfac682131f83c75904c3c1`,
while this repository pins `56a005855ea17e0b0958f73ec801ae140b0a1679`; dependency-form reuse is
therefore unavailable. The adapted source files retain the TauCeti copyright and complete
Apache-2.0 license in `docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`.
-/

/-- A positive-dimensional Euclidean unit sphere cannot be contractible.

This declaration is the receiving specialization of the exact TauCeti endpoint; the proof does
not reproduce its homology obstruction locally. -/
theorem not_contractible_unit_sphere (n : ℕ) (hn : 0 < n) :
    ¬ ContractibleSpace (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let E := EuclideanSpace ℝ (Fin n)
  letI : FiniteDimensional ℝ E := inferInstance
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by
    dsimp [E]
    rw [finrank_euclideanSpace_fin]
    exact hn)
  exact TauCeti.not_contractibleSpace_sphere

end D5.S3.Topology.SphereBrouwerObstruction

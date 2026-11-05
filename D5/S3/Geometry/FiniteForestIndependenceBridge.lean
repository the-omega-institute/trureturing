/- GID: D5/S3/Geometry/FiniteForestIndependenceBridge
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteForestIndependenceBridge
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Complement-neighborhood bridge for the Carnero width-five reduction. -/

import D5.S3.Geometry.FiniteForestIndependence

namespace D5.S3.Geometry.FiniteForestIndependence

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The residual vertices are exactly the open neighbors of `v` in the complement graph,
which is the complement of the closed neighborhood of `v` in `G`. -/
theorem residualSet_eq_compl_neighborSet (G : SimpleGraph V) (v : V) :
    residualSet G v = Gᶜ.neighborSet v := by
  ext x
  simp [residualSet, SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj,
    and_comm, eq_comm]

end D5.S3.Geometry.FiniteForestIndependence

#print axioms D5.S3.Geometry.FiniteForestIndependence.residualSet_eq_compl_neighborSet

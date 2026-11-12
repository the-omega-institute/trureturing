import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.FiniteConvexFiberMap

/-!
The complete source telescope is retained. A four-slot registration still needs a
source-bound arena for varying compact Hausdorff bases, normed vector spaces,
finite covers, entire fibers, convex neighborhoods and forbidden sets. The
continuous map is existentially constructed, and its evaluations occur in both
membership and segment clauses. A lawful enrolled readout, exact sourceSelection,
realization equivalence, whole-family intervention and sensitivity, and actual
observational dependence are not supplied. No completed registration is asserted. The missing evidence is tracked at
https://github.com/the-omega-institute/trureturing/issues/29762.
-/

namespace Reg.D5.S3.Topology.FiniteConvexFiberMap

abbrev source_scope.{u,v} := type_of%
  (@_root_.D5.S3.Topology.FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map.{u,v})

theorem source_proof : source_scope :=
  @_root_.D5.S3.Topology.FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map

end Reg.D5.S3.Topology.FiniteConvexFiberMap

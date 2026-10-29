import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.SphereBrouwerObstruction

/-!
Exact theorem telescopes and source proofs are retained below. Four-slot
registration is incomplete: the dependent-family template still needs a
whole-source arena for the cover, topology and varying dimension, an enrolled
readout and sourceSelection, a realization-equivalence bridge, whole-family
variation and sensitivity, and actual observational dependence.
No declared_validated registration is claimed. The linked-issue exception
is tracked at https://github.com/the-omega-institute/trureturing/issues/23716.
-/

namespace Reg.D5.S3.Topology.SphereBrouwerObstruction

abbrev not_contractible_unit_sphere_scope := type_of%
  (@_root_.D5.S3.Topology.SphereBrouwerObstruction.not_contractible_unit_sphere)
theorem not_contractible_unit_sphere_source : not_contractible_unit_sphere_scope :=
  @_root_.D5.S3.Topology.SphereBrouwerObstruction.not_contractible_unit_sphere

end Reg.D5.S3.Topology.SphereBrouwerObstruction

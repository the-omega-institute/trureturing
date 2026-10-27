import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Separation.DisjointCopyTower

/-!
The exact source scope retains the arbitrary carrier, topology, Hausdorff
structure, sequence of compact nonempty levels, and disjoint successor copies.
The source theorem supplies the actual-positive binding below.

Four-slot registration is incomplete. The dependent-family template still
needs a whole-source arena and enrolled readout on pairs of ambient subsets,
source reconstruction and sourceSelection, a realization-equivalence bridge,
whole-family variation and sensitivity, and actual observational dependence.
No finite catalog or declared_validated registration is asserted.
The exact theorem's unfinished audit is tracked at
https://github.com/the-omega-institute/trureturing/issues/22033
under the existing linked-issue exception; this does not assert audit completion.
-/

namespace Reg.D5.S3.Topology.Separation.DisjointCopyTower

universe u

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Topology.Separation.DisjointCopyTower.exists_disjoint_infinite_closed_copies.{u})

theorem exact_source : sourceScope.{u} :=
  @_root_.D5.S3.Topology.Separation.DisjointCopyTower.exists_disjoint_infinite_closed_copies.{u}

end Reg.D5.S3.Topology.Separation.DisjointCopyTower

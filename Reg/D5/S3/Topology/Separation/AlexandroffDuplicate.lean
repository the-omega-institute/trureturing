import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Separation.AlexandroffDuplicate

/-!
The source scope retains the original carrier universe, topology, compactness,
Hausdorffness, connectedness and nontriviality instances, and all eight result
clauses. This is actual-positive evidence, not a declared four-slot registration.
The dependent-family source reconstruction and observation binding are missing.
In particular a Unit-state readout of the whole true conclusion cannot satisfy
DependentFamily.ObservationalDependence. A lawful source observation must retain
the duplicate point and its actual clopen-neighborhood tests, with the complete
ambient topology and both source injections; it cannot replace them by a truth
flag or discard the compactness, separation and closed-embedding clauses.
-/

namespace Reg.D5.S3.Topology.Separation.AlexandroffDuplicate

open _root_.D5.S3.Topology.Separation.AlexandroffDuplicate

universe u

abbrev frontierScope := type_of% (@topological_frontier.{u})

theorem frontier_actual : frontierScope.{u} := @topological_frontier.{u}

end Reg.D5.S3.Topology.Separation.AlexandroffDuplicate

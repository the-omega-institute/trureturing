import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
import Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
import Reg.Support.DependentFamily

namespace Reg.Catalogs.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.RootCatalog
open LeanInformationAudit

def rootCatalog.{u_1} : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance.{u_1}), theoremName := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance, objectArenaName := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena, statementIdentity := some "sha256:b0402a35876d7baf34f9739ea040e967bd9424a79b7beeec1e4813eca3c8b804", registrationModuleName := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance.{u_1}), theoremName := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance, objectArenaName := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.arena, statementIdentity := some "sha256:b0402a35876d7baf34f9739ea040e967bd9424a79b7beeec1e4813eca3c8b804", registrationModuleName := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance } }

end Reg.Catalogs.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.RootCatalog

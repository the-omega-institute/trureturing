import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
import Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
import Reg.Support.DependentFamily

namespace Reg.Catalogs.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance), theoremName := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance, objectArenaName := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.arena, statementIdentity := some "sha256:f93df77c5b48e83e40d3dba0b9f74eefc46b8a1e5a1d7c3ddecb5d0cff0457ca", registrationModuleName := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance), theoremName := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance, objectArenaName := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.arena, statementIdentity := some "sha256:f93df77c5b48e83e40d3dba0b9f74eefc46b8a1e5a1d7c3ddecb5d0cff0457ca", registrationModuleName := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance } }

end Reg.Catalogs.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.RootCatalog

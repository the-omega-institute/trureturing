import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
import Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
import Reg.Support.DependentFamily

namespace Reg.Catalogs.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound), theoremName := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound, objectArenaName := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.arena, statementIdentity := some "sha256:0784cf503dfe5b78a65875009000f173bf6ffa84e7614fb47b4041a701fe3e3e", registrationModuleName := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound), theoremName := `D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.shared_control_bit_storage_bound, objectArenaName := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.arena, statementIdentity := some "sha256:0784cf503dfe5b78a65875009000f173bf6ffa84e7614fb47b4041a701fe3e3e", registrationModuleName := `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound } }

end Reg.Catalogs.D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound.RootCatalog

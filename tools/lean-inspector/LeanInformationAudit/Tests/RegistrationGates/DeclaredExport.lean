import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings
import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural

namespace LeanInformationAudit.Tests.DeclaredExport
open Lean Meta Elab Command TemplateBinding

run_meta do
  let snapshot ← exportSnapshot
  let expected := #[
    `LeanInformationAudit.Tests.DeclaredBindings.validated,
    `LeanInformationAudit.Tests.DeclaredBindings.unresolved,
    `LeanInformationAudit.Tests.DeclaredBindings.undeclared,
    `LeanInformationAudit.Tests.DeclaredStructural.declared,
    `LeanInformationAudit.Tests.DeclaredStructural.undeclared]
  unless snapshot.selected.size == expected.size &&
      expected.all (fun name => snapshot.selected.any (·.occurrence.key.theoremName == name)) do
    throwError "setup: export inventory differs from the five independent occurrences"
  let modules := #[`LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings,
      `LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural].map fun moduleName =>
    (moduleName, snapshot.originals.filter (·.occurrence.key.registrationModule == moduleName)
      |>.map (·.occurrence.key))
  let wires ← reportJson modules
  unless wires.size == modules.size do throwError "setup: export lost a module"
  for ((_, registered), wire) in modules.zip wires do
    let .ok rows := wire.getObjValAs? (Array Json) "records"
      | throwError "setup: missing record wire"
    unless rows.size == registered.size do throwError "setup: export partition lost a row"
  logInfo "[PASS] complete_producer_loader_wire"

end LeanInformationAudit.Tests.DeclaredExport

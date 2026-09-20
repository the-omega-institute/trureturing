import LeanInformationAudit.FixedSnapshot
import LeanInformationAudit.FrozenBaseline

namespace LeanInformationAudit
open Lean

def frozenInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.InformationRoot

def designatedInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot

/-- Current production contracts. These rows are content inputs, independent of
registry output; migration moves their suppliers into Reg with their roots. -/
def currentRootCatalogContracts : Array RootCatalogContract := #[
  { rootId := frozenInformationRootId
    expected := frozenInformationRootBaseline
    source := fixedInformationSourceSnapshot.occurrences
    baseline := frozenInformationRootBaseline
    companionPrefix := some .anonymous },
  { rootId := designatedInformationRootId
    expected := fixedInformationSourceSnapshot.occurrences
    source := fixedInformationSourceSnapshot.occurrences
    baseline := frozenInformationRootBaseline }]

private initialize rootCatalogExt :
    SimplePersistentEnvExtension RootCatalogContract (Array RootCatalogContract) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) currentRootCatalogContracts }

namespace RootCatalogs

def find? (env : Environment) (rootId : Name) : Option RootCatalogContract :=
  (rootCatalogExt.getState env).find? (·.rootId == rootId)

/-- A root declares its contract before registering/sealing. Imported contracts
remain keyed by their original root and cannot change a downstream root. -/
def declare (contract : RootCatalogContract) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless contract.rootId == env.header.mainModule do
    throwError "IE-C028 RootContractOwnerMismatch: {contract.rootId}"
  if (find? env contract.rootId).isSome then
    throwError "IE-C028 DuplicateRootContract: {contract.rootId}"
  modifyEnv fun current =>
    let current := match contract.companionPrefix with
      | some companionPrefix => current.registerNamespace companionPrefix
      | none => current
    rootCatalogExt.addEntry current contract

end RootCatalogs
end LeanInformationAudit

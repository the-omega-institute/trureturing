import LeanInformationAuditInterface.Records

namespace LeanInformationAudit.TemplateBinding
open Lean

private initialize occurrenceInventory : SimplePersistentEnvExtension TemplateOccurrenceEvent (Array TemplateOccurrenceEvent) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize bindingClaims : SimplePersistentEnvExtension TemplateBindingClaim (Array TemplateBindingClaim) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

private initialize bindingRecords : SimplePersistentEnvExtension BindingRecord (Array BindingRecord) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

/-- Store declaration data without assessment or elaboration. -/
def addOccurrence (env : Environment) (event : TemplateOccurrenceEvent) : Environment :=
  occurrenceInventory.addEntry env event

def addClaim (env : Environment) (claim : TemplateBindingClaim) : Environment :=
  bindingClaims.addEntry env claim

/-- Retain a result-shaped payload as data. Insertion performs no assessment
and grants no certification; consumers still validate ownership and semantics. -/
def addRecord (env : Environment) (record : BindingRecord) : Environment :=
  bindingRecords.addEntry env record

def records (env : Environment) : Array BindingRecord := bindingRecords.getState env

def inventory (env : Environment) : Array TemplateOccurrenceEvent := occurrenceInventory.getState env

def claims (env : Environment) : Array TemplateBindingClaim := bindingClaims.getState env

/-- Origin labels come from the native extension container, separately from
the owner asserted in a claim. Local claims have the current module as origin. -/
def ownedClaims (env : Environment) : Array (Name × TemplateBindingClaim) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for claim in bindingClaims.getModuleEntries env index do
      result := result.push (owner, claim)
  for claim in bindingClaims.getEntries env do
    result := result.push (env.header.mainModule, claim)
  return result

def ownedEvents (env : Environment) : Array (Name × TemplateOccurrenceEvent) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for event in occurrenceInventory.getModuleEntries env index do
      result := result.push (owner, event)
  for event in (occurrenceInventory.getEntries env).reverse do
    result := result.push (env.header.mainModule, event)
  return result

/-- Imported records in module/entry order, labeled by their actual extension
container, independently of the owners asserted in their payloads. -/
def importedRecords (env : Environment) : Array (Name × BindingRecord) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for record in bindingRecords.getModuleEntries env index do
      result := result.push (owner, record)
  return result

/-- Imported records followed by local records in insertion order. Local
producer labels come from the current module, not the record payload. -/
def ownedRecords (env : Environment) : Array (Name × BindingRecord) := Id.run do
  let mut result := importedRecords env
  for record in (bindingRecords.getEntries env).reverse do
    result := result.push (env.header.mainModule, record)
  return result

end LeanInformationAudit.TemplateBinding

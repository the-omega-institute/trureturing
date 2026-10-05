import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.Contract.SourceAudit
import LeanInformationAudit.Contract.RootStructure

namespace LeanInformationAudit.Contract.Discovery
open Lean Meta

structure Definition where
  owner : Name
  info : DefinitionVal
  range : DeclarationRanges

structure Snapshot where
  definitions : Array Definition := #[]
  registrations : Array (Name × Decoder.CompanionInput) := #[]
  enrollments : Array (Name × TemplateEnrollmentInput) := #[]
  roots : Array (Name × RootCatalogContract) := #[]
  seals : Array (Name × SealInput) := #[]

def checkDefinition (info : ConstantInfo) : MetaM DefinitionVal := do
  match SourceAudit.checkInputDefinition info with
  | .ok value => return value
  | .error error => throwError error

def requireRange (name : Name) : MetaM DeclarationRanges := do
  let some range ← findDeclarationRanges? name
    | throwError "contract.discovery:source_range:{name}"
  return range

def moduleSource (name : Name) : IO System.FilePath := do
  if Repository.isImplementationSourceModule name then
    Repository.source ("tools/lean-inspector/" ++ name.toString.replace "." "/" ++ ".lean")
  else ArenaProvenance.moduleSource name

/-- Read the compiler inventory and declaration positions. Source text does not
authorize declarations or constrain their spelling. -/
def auditModule (owner : Name) (_source : String) : MetaM (Array Definition) := do
  let env := (← getEnv).setExporting false
  let names := if owner == env.header.mainModule then
      env.constants.map₂.toList.toArray.map Prod.fst
    else if let some idx := env.getModuleIdx? owner then
      env.header.moduleData[idx.toNat]!.constNames
    else #[]
  let mut found := #[]
  for name in names do
    let some info := env.find? name | throwError "contract.discovery:constant_missing:{name}"
    unless SourceAudit.isInput info do continue
    let value ← checkDefinition info
    let range ← requireRange name
    found := found.push ⟨owner, value, range⟩
  return found.qsort fun a b =>
    a.range.range.pos.line < b.range.range.pos.line ||
      (a.range.range.pos.line == b.range.range.pos.line &&
        a.range.range.pos.column < b.range.range.pos.column)


def discoverWithStructure (requirements : Array RootStructure.Requirement)
    (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
  let original ← getEnv
  setEnv (original.setExporting false)
  try
    RootStructure.checkScope requirements moduleNames
    let mut result : Snapshot := {}
    let mut seen : NameSet := {}
    for owner in moduleNames do
      if seen.contains owner then throwError "contract.discovery:duplicate_module:{owner}"
      seen := seen.insert owner
      unless owner == original.header.mainModule || (original.getModuleIdx? owner).isSome do
        throwError "contract.discovery:module_missing:{owner}"
      discard <| sourceOf owner
      let source := ""
      let definitions ← auditModule owner source
      for definition in definitions do
        let info := definition.info
        let head := info.type.getAppFn.constName!
        if head == ``Contract.Registration then
          result := { result with registrations := result.registrations.push (owner, ← Decoder.registration owner info source) }
        else if head == ``Contract.TemplateEnrollment then
          result := { result with enrollments := result.enrollments.push (owner, ← Decoder.enrollment owner info source) }
        else if head == ``Contract.RootCatalog then
          result := { result with roots := result.roots.push (owner, ← Decoder.rootCatalog info.value) }
        else if head == ``Contract.ExpectedDeclaration then
          throwError "contract.root_structure:independent_expected_not_allowed:{owner}:{info.name}"
        else if head == ``Contract.Seal then
          result := { result with seals := result.seals.push (owner, ← Decoder.readSeal info.name info.value) }
      result := { result with definitions := result.definitions ++ definitions }
    RootStructure.check requirements moduleNames result.roots result.seals
    return result
  finally setEnv original

/-- Production constructs obligations from the Reg source-tree path rule before
discovery. Isolated tests can supply requirements from their own source tree;
no decoded contract entry determines its module kind. -/
def discover (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
  let env ← getEnv
  let requirements ← RootStructure.required env
  for owner in env.header.moduleNames.push env.header.mainModule do
    if (`Reg).isPrefixOf owner && !moduleNames.contains owner then
      throwError "contract.root_structure:required_module_missing:{owner}"
  discoverWithStructure requirements moduleNames sourceOf

end LeanInformationAudit.Contract.Discovery

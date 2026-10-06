import LeanInformationAudit.Registry.ArenaProvenance
import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.Contract.SourceAudit
import LeanInformationAudit.Contract.RootStructure

namespace LeanInformationAudit.Contract.Discovery
open Lean

structure Definition where
  owner : Name
  info : DefinitionVal

structure Snapshot where
  definitions : Array Definition := #[]
  registrations : Array (Name × Decoder.CompanionInput) := #[]
  enrollments : Array (Name × TemplateEnrollmentInput) := #[]
  roots : Array (Name × RootCatalogContract) := #[]
  seals : Array (Name × SealInput) := #[]

def moduleSource (name : Name) : IO System.FilePath := do
  if Repository.isImplementationSourceModule name then
    Repository.source ("tools/lean-inspector/" ++ name.toString.replace "." "/" ++ ".lean")
  else ArenaProvenance.moduleSource name

/-- The compiler inventory identifies inputs. Source positions and spelling
have no role in discovery; names fix a reproducible order within each owner. -/
def auditConstants (owner : Name) (constants : Array ConstantInfo) :
    Except String (Array Definition) := do
  let mut found := #[]
  for info in constants do
    unless SourceAudit.isInput info do continue
    let value ← (SourceAudit.checkInputDefinition info).mapError fun reason =>
      s!"contract.decode_failed:{owner}:{info.name}:{reason}"
    found := found.push ⟨owner, value⟩
  return found.qsort fun a b => a.info.name.toString < b.info.name.toString

/-- Discover every typed input from compiled constant arrays. Axiom closure and
constant lookup come from the same compiled-data reader as the arrays. -/
def discoverCompiled (requirements : Array RootStructure.Requirement)
    (moduleNames : Array Name) (context : Literal.Context)
    (constantsOf : Name → IO (Array ConstantInfo))
    (axiomsOf : Name → IO (Array Name))
    (sourceOf : Name → IO System.FilePath := moduleSource) : IO Snapshot := do
  IO.ofExcept <| RootStructure.checkScope requirements moduleNames
  let mut result : Snapshot := {}
  let mut seen : NameSet := {}
  for owner in moduleNames do
    if seen.contains owner then
      throw <| IO.userError s!"contract.discovery:duplicate_module:{owner}"
    seen := seen.insert owner
    discard <| sourceOf owner
    let source := ""
    let definitions ← IO.ofExcept <| auditConstants owner (← constantsOf owner)
    for definition in definitions do
      let info := definition.info
      try
        let head := info.type.getAppFn.constName!
        if head == ``Contract.Registration then
          let row ← Decoder.registration context (← axiomsOf info.name) owner info source
          result := { result with registrations := result.registrations.push (owner, row) }
        else if head == ``Contract.TemplateEnrollment then
          let value ← IO.ofExcept <| Decoder.enrollment context.find owner info source
          result := { result with enrollments := result.enrollments.push (owner, value) }
        else if head == ``Contract.RootCatalog then
          let value ← IO.ofExcept <| Decoder.rootCatalog context.find info.value
          result := { result with roots := result.roots.push (owner, value) }
        else if head == ``Contract.ExpectedDeclaration then
          throw <| IO.userError s!"contract.root_structure:independent_expected_not_allowed:{owner}:{info.name}"
        else if head == ``Contract.Seal then
          let value ← IO.ofExcept <|
            Decoder.readSeal context (← axiomsOf info.name) info.name info.value
          result := { result with seals := result.seals.push (owner, value) }
      catch error =>
        throw <| IO.userError s!"contract.decode_failed:{owner}:{info.name}:{error}"
    result := { result with definitions := result.definitions ++ definitions }
  IO.ofExcept <| RootStructure.check requirements moduleNames result.roots result.seals
  return result

end LeanInformationAudit.Contract.Discovery

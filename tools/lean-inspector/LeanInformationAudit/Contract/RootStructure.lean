import LeanInformationAudit.Registry.Repository
import LeanInformationAuditInterface.Store

namespace LeanInformationAudit.Contract.RootStructure
open Lean Meta

/-- Ordinary modules have neither structural entry. Catalog modules own one
RootCatalog; sealed catalogs additionally own one Seal for the same root. -/
inductive Kind where
  | ordinary | catalog | sealedCatalog
  deriving BEq, Inhabited

structure Requirement where
  owner : Name
  rootId : Name
  kind : Kind

/-- The package manifest fixes obligations independently of source/compiled
candidate discovery. Its entire inventory is checked, then the loaded import
closure selects obligations even if the caller omits those modules from discover.
No discovered entry content selects a module kind. -/
def readManifest (env : Environment) (json : Json) : IO (Array Requirement) := do
  unless (← IO.ofExcept (json.getObjValAs? Nat "schema_version")) == 1 do
    throw <| IO.userError "contract.root_structure:manifest_version"
  let rows ← IO.ofExcept <| json.getObjValAs? (Array Json) "modules"
  let mut seen : NameSet := {}
  let mut result := #[]
  for row in rows do
    let owner := (← IO.ofExcept (row.getObjValAs? String "module")).toName
    unless (`Reg).isPrefixOf owner do
      throw <| IO.userError s!"contract.root_structure:manifest_owner:{owner}"
    if seen.contains owner then
      throw <| IO.userError s!"contract.root_structure:duplicate_requirement:{owner}"
    seen := seen.insert owner
    let kind ← match ← IO.ofExcept (row.getObjValAs? String "kind") with
      | "catalog" => pure Kind.catalog
      | "sealed_catalog" => pure Kind.sealedCatalog
      | _ => throw <| IO.userError s!"contract.root_structure:manifest_kind:{owner}"
    unless ← (← Repository.source
        (owner.toString.replace "." "/" ++ ".lean")).pathExists do
      throw <| IO.userError s!"contract.root_structure:required_source_missing:{owner}"
    if owner == env.header.mainModule || (env.getModuleIdx? owner).isSome then
      result := result.push ⟨owner, owner, kind⟩
  return result

/-- Production obligations come from the registered package module manifest. -/
def required (env : Environment) : IO (Array Requirement) := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile
    (← Repository.source "Meta/reg-contract-structure.json"))
  readManifest env json

/-- Required owners cannot disappear through the discover module filter. -/
def checkScope (requirements : Array Requirement) (modules : Array Name) : MetaM Unit := do
  let mut seen : NameSet := {}
  for requirement in requirements do
    if seen.contains requirement.owner then
      throwError "contract.root_structure:duplicate_requirement:{requirement.owner}"
    seen := seen.insert requirement.owner
    unless modules.contains requirement.owner do
      throwError "contract.root_structure:required_module_missing:{requirement.owner}"

/-- File kinds fix cardinalities and root identities. A Seal covers only its
declared root; its RootCatalog retains ordered expected/source/baseline arrays. -/
def check (requirements : Array Requirement) (modules : Array Name)
    (roots : Array (Name × RootCatalogContract)) (seals : Array (Name × SealInput))
    : MetaM Unit := do
  for owner in modules do
    let rule := requirements.find? (·.owner == owner)
    unless (`Reg).isPrefixOf owner || rule.isSome do continue
    let kind := rule.map (·.kind) |>.getD .ordinary
    let rootId := rule.map (·.rootId) |>.getD owner
    let catalogs := roots.filter (·.1 == owner)
    let sealEntries := seals.filter (·.1 == owner)
    let requiredCatalogs := if kind == .ordinary then 0 else 1
    let requiredSeals := if kind == .sealedCatalog then 1 else 0
    unless catalogs.size == requiredCatalogs do
      throwError "contract.root_structure:root_catalog_count:{owner}:expected={requiredCatalogs}:actual={catalogs.size}"
    unless sealEntries.size == requiredSeals do
      throwError "contract.root_structure:seal_count:{owner}:expected={requiredSeals}:actual={sealEntries.size}"
    for (_, catalog) in catalogs do
      unless catalog.rootId == rootId do
        throwError "contract.root_structure:root_catalog_owner:{owner}:{catalog.rootId}"
    for (_, sealEntry) in sealEntries do
      unless sealEntry.rootId == rootId do
        throwError "contract.root_structure:seal_owner:{owner}:{sealEntry.rootId}"

end LeanInformationAudit.Contract.RootStructure

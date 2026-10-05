import LeanInformationAudit.Registry.Repository
import LeanInformationAudit.RuntimeInputs

namespace LeanInformationAudit.Contract.RootStructure
open Lean

/-- Ordinary modules have neither structural entry. Catalog modules own one
RootCatalog; sealed catalogs additionally own one Seal for the same root. -/
inductive Kind where
  | ordinary | catalog | sealedCatalog
  deriving BEq, Inhabited

structure Requirement where
  owner : Name
  rootId : Name
  kind : Kind

/-- Only the Reg/Catalogs subtree reserves structural leaf names. D5 mirrors
and all other source files remain ordinary, independently of entry content. -/
def kindFromPath (path : System.FilePath) : Kind :=
  if (path.components.dropWhile (· != "Reg")).take 2 != ["Reg", "Catalogs"] then
    .ordinary
  else
  match path.fileName with
  | some "RootCatalog.lean" => .catalog
  | some "SealedCatalog.lean" => .sealedCatalog
  | _ => .ordinary

/-- Enumerated source members, not discovered contract values, supply every
obligation. The production caller uses the loaded Reg import closure and its
canonical source paths; isolated tests use their own source tree. -/
def requiredFor (owners : Array Name) (sourceOf : Name → IO System.FilePath)
    : IO (Array Requirement) := do
  let mut seen : NameSet := {}
  let mut result := #[]
  for owner in owners do
    if seen.contains owner then
      throw <| IO.userError s!"contract.root_structure:duplicate_requirement:{owner}"
    seen := seen.insert owner
    let path ← sourceOf owner
    unless ← path.pathExists do
      throw <| IO.userError s!"contract.root_structure:required_source_missing:{owner}"
    result := result.push ⟨owner, owner, kindFromPath path⟩
  return result

/-- The loaded Reg source tree fixes obligations before candidate discovery.
Unmoved legacy files are ordinary under this rule; their typed-entry migration
state is measured separately rather than inferred from legacy catalog commands. -/
def required (env : Environment) : IO (Array Requirement) :=
  requiredFor (env.header.moduleNames.push env.header.mainModule |>.filter ((`Reg).isPrefixOf ·))
    fun owner => Repository.source (owner.toString.replace "." "/" ++ ".lean")

/-- Required owners cannot disappear through the discover module filter. -/
def checkScope (requirements : Array Requirement) (modules : Array Name) : Except String Unit := do
  let mut seen : NameSet := {}
  for requirement in requirements do
    if seen.contains requirement.owner then
      throw s!"contract.root_structure:duplicate_requirement:{requirement.owner}"
    seen := seen.insert requirement.owner
    unless modules.contains requirement.owner do
      throw s!"contract.root_structure:required_module_missing:{requirement.owner}"

/-- File kinds fix cardinalities and root identities. A Seal covers only its
declared root; its RootCatalog retains ordered expected/source/baseline arrays. -/
def check (requirements : Array Requirement) (modules : Array Name)
    (roots : Array (Name × RootCatalogContract)) (seals : Array (Name × SealInput))
    : Except String Unit := do
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
      throw s!"contract.root_structure:root_catalog_count:{owner}:expected={requiredCatalogs}:actual={catalogs.size}"
    unless sealEntries.size == requiredSeals do
      throw s!"contract.root_structure:seal_count:{owner}:expected={requiredSeals}:actual={sealEntries.size}"
    for (_, catalog) in catalogs do
      unless catalog.rootId == rootId do
        throw s!"contract.root_structure:root_catalog_owner:{owner}:{catalog.rootId}"
    for (_, sealEntry) in sealEntries do
      unless sealEntry.rootId == rootId do
        throw s!"contract.root_structure:seal_owner:{owner}:{sealEntry.rootId}"

end LeanInformationAudit.Contract.RootStructure

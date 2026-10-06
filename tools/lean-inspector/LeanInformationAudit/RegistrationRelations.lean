import LeanInformationAudit.Sha256
import LeanInformationAudit.TemplateData
import LeanInformationAudit.RegistrationData
import LeanInformationAudit.Registry.ArenaProvenance
import LeanInformationAudit.Contract.NodeFacts

namespace LeanInformationAudit.RegistrationReifier
open Lean

def occurrenceBinding (e : InformationRegistryEntry) : Array Name := #[
  e.theoremName, e.unitName, e.arenaName, e.realizationName, e.variationWitness,
  e.sensitivityWitness, e.catalogId, e.registrationModuleName, e.objectArenaName,
  e.resolvedArenaName, e.canonicalObjectArenaName, e.effectiveCatalogId]
end LeanInformationAudit.RegistrationReifier

namespace LeanInformationAudit
open Lean

/-- Canonical identity is a named operand of a bound ExactMatch. Generic head
facts ending at constructors cannot select a registry name. No alias body,
application, binder or local term is evaluated here. -/
def resolveCanonicalArena (find : Name → Option ConstantInfo)
    (facts : Array Contract.NodeFacts.BoundOperand) (arena : Expr) : Except String Expr := do
  let mut candidates : Array Expr := #[]
  for fact in facts do
    unless fact.relation == some ``Contract.NodeFact.exact && fact.value.equal arena do continue
    let some other := fact.other | continue
    let .const name _ := other.getAppFn | continue
    let some info := find name | throw s!"IE-C003 ArenaResolutionFailed: {name}"
    if let .ctorInfo _ := info then continue
    unless candidates.contains other do candidates := candidates.push other
  let some canonical := candidates[0]?
    | throw s!"contract.node_binding:arena.canonical_fact_missing:{arena.getAppFn.constName!}"
  unless candidates.size == 1 do throw "contract.node_binding:arena.canonical_fact_ambiguous"
  for operand in #[arena, canonical] do
    let name := operand.getAppFn.constName!
    let some info := find name | throw s!"IE-C003 ArenaResolutionFailed: {name}"
    if info.value?.any (fun value => (value.find? fun node =>
        match node with
        | .mdata data _ => data.contains ArenaProvenance.unsupported
        | _ => false).isSome) then
      throw s!"IE-C003 ArenaSourceUnsupported arena={arena.getAppFn.constName!} owner={name}"
  return canonical

def InformationRegistryEntry.occurrenceKey
    (entry : InformationRegistryEntry) : Name × Name :=
  (entry.canonicalObjectArenaName, entry.theoremName)

private def jsonStringArray (values : Array String) : String :=
  (Json.arr <| values.map Json.str).compress

def InformationRegistryEntry.occurrenceKeyString
    (entry : InformationRegistryEntry) : String :=
  entry.canonicalObjectArenaName.toString ++ "/" ++ entry.theoremName.toString

def qualifiedNameCollisionError (rootId : Name) (catalogId : CatalogId)
    (generatedName : Name) (entries : Array InformationRegistryEntry) : String :=
  let occurrences := entries.map (·.occurrenceKeyString) |>.toList.eraseDups.toArray
    |>.qsort (· < ·)
  s!"IE-C025 QualifiedNameCollision root={rootId} catalog={catalogId} \
generated_name={generatedName} occurrences={jsonStringArray occurrences}"

def qualifiedNameCollisionEntries (entries : Array InformationRegistryEntry)
    (generatedName : Name) (prospective : InformationRegistryEntry) :
    Array InformationRegistryEntry :=
  let owners := (entries.filter fun entry =>
    entry.unitName == generatedName || entry.realizationName == generatedName).push prospective
  owners.foldl (init := #[]) (fun result entry =>
    if result.any (fun owner => owner.occurrenceKey == entry.occurrenceKey) then result
    else result.push entry)
    |>.qsort (fun left right => left.occurrenceKeyString < right.occurrenceKeyString)

def rejectKernelAddressSemanticUse (rootId : Name) (catalogId : CatalogId)
    (address consumer : String) : Except String Unit :=
  .error s!"IE-C030 KernelAddressUsedAsSemanticEvidence root={rootId} \
catalog={catalogId} address={address} consumer={consumer}"

/-- Reachability is relative to the requested registration root. -/
def moduleReachable (importsOf : Name → Array Name) (root owner : Name) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut pending := [root]
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    if name == owner then return true
    seen := seen.insert name
    pending := (importsOf name).toList ++ pending
  return false

/-- The root's complete import closure, shared by owner filters and joins. -/
def reachableModules (importsOf : Name → Array Name) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut pending := [root]
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    pending := (importsOf name).toList ++ pending
  return seen

def snapshotExpectations (rootId : Name) (rows : Array SnapshotOccurrence) :
    Array ExpectedOccurrence :=
  rows.map fun row => {
    rootId
    objectArenaName := row.objectArenaName
    theoremName := row.theoremName
    statementIdentity := if !row.statementIdentity.isEmpty then row.statementIdentity
      else row.capturedStatement.map
        (fun type => "sha256:" ++ Sha256.hex (toString type).toUTF8) |>.getD ""
    capturedStatement := row.capturedStatement
    registrationModuleName := row.registrationModuleName
  }

/-- Complete, deterministic payload shared by prechecks, insertion and sealing.
`entries` contains every contributing registration, including a prospective one
when rejecting insertion; module names are a sorted set, count counts entries. -/
def duplicateRegistrationError (entry : InformationRegistryEntry)
    (entries : Array InformationRegistryEntry) : String :=
  let modules := entries.map (·.registrationModuleName.toString)
    |>.toList.eraseDups.toArray |>.qsort (· < ·)
  s!"IE-C002 DuplicateRegistration object_arena={entry.canonicalObjectArenaName} \
theorem_name={entry.theoremName} registration_modules={jsonStringArray modules} \
count={entries.size}"

private def sameCertificate : Option AutoDerivedSemanticCertificate →
    Option AutoDerivedSemanticCertificate → Bool
  | none, none => true
  | some a, some b =>
    a.occurrence == b.occurrence && a.catalogKind == b.catalogKind &&
      a.localRegistrationNames == b.localRegistrationNames && a.statementIdentity == b.statementIdentity &&
      a.levelParams == b.levelParams && a.nondegenerate == b.nondegenerate &&
      a.statement.equal b.statement && a.descriptor.equal b.descriptor &&
      a.arena.equal b.arena && a.outputEvidence.equal b.outputEvidence
  | _, _ => false

def sameEntry (left right : InformationRegistryEntry) : Bool :=
  RegistrationReifier.occurrenceBinding left == RegistrationReifier.occurrenceBinding right &&
    left.catalogKind == right.catalogKind && left.statementIdentity == right.statementIdentity &&
    left.localRegistrationNames == right.localRegistrationNames && left.sourceBound == right.sourceBound &&
    left.compiledMathematics == right.compiledMathematics &&
    sameCertificate left.derivedCertificate right.derivedCertificate

private def nameLess (a b : Name) : Bool := a.lt b
private def nameArrayJson (names : Array Name) : String :=
  (Json.arr (names.map (Json.str ∘ Name.toString))).compress
private def distinctNames (names : Array Name) : Array Name :=
  names.foldl (init := #[]) fun result name =>
    if result.contains name then result else result.push name

def validateMaximalCatalog (rootId arenaName : Name)
    (entries : Array InformationRegistryEntry) : Except String CatalogId := do
  let maximal := entries.filter fun entry => entry.catalogKind == .canonicalMaximal
  if maximal.isEmpty then
    let occurrences := entries.map (·.theoremName) |>.qsort nameLess
    throw s!"IE-C026 MissingMaximalCatalog root={rootId} arena={arenaName} \
occurrences={nameArrayJson occurrences}"
  let catalogIds := distinctNames (entries.map (·.effectiveCatalogId))
    |>.qsort nameLess
  if catalogIds.size != 1 then
    throw s!"IE-C024 SplitCanonicalArenaCatalog root={rootId} arena={arenaName} \
catalogs={nameArrayJson catalogIds}"
  pure catalogIds[0]!

end LeanInformationAudit

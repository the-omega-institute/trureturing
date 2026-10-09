import LeanInformationAudit.Sha256
import LeanInformationAudit.TemplateData
import LeanInformationAudit.RegistrationData
import LeanInformationAudit.Registry.ArenaProvenance

namespace LeanInformationAudit.RegistrationReifier
open Lean

def occurrenceBinding (e : InformationRegistryEntry) : Array Name := #[
  e.theoremName, e.unitName, e.arenaName, e.realizationName, e.variationWitness,
  e.sensitivityWitness, e.catalogId, e.registrationModuleName, e.objectArenaName,
  e.resolvedArenaName, e.canonicalObjectArenaName, e.effectiveCatalogId]
end LeanInformationAudit.RegistrationReifier

namespace LeanInformationAudit
open Lean

/-- A correctness bound, independent of host speed and caller heartbeat options.
Every head transition, declaration lookup and compiled-table lookup spends one unit. -/
def arenaAliasWorkBudget : Nat := 4096

private inductive AliasClosure where
  | mk (term : Expr) (bindings : List AliasClosure)

/-- Fuelled weak-head reduction of forwarding aliases only (delta/beta/zeta).
Closures avoid substitution and never traverse or normalize argument subtrees.
Unlike unrestricted `whnfR`, this stops at constructors, projections and recursors,
and never performs structure eta. A bare named target becomes the next owner;
an application that constructs a value retains the last named owner.
The single budget covers both outer aliases and all work inside applications. -/
def resolveCanonicalArenaName (find : Name → Option ConstantInfo)
    (spelling : Name) : Except String Name := do
  unless (find spelling).isSome do return spelling
  let mut owner := spelling
  let mut current := AliasClosure.mk (mkConst spelling) []
  let mut arguments : List AliasClosure := []
  let mut fuel := arenaAliasWorkBudget
  while fuel > 0 do
    fuel := fuel - 1
    let .mk term bindings := current
    match term with
    | .mdata data body =>
      if data.contains arenaConstructionMarker then return owner
      if data.contains ArenaProvenance.unsupported then
        throw s!"IE-C003 ArenaSourceUnsupported arena={spelling} owner={owner}"
      current := .mk body bindings
    | .app fn arg =>
      arguments := .mk arg bindings :: arguments
      current := .mk fn bindings
    | .letE _ _ value body _ =>
      current := .mk body (.mk value bindings :: bindings)
    | .lam _ _ body _ =>
      match arguments with
      | [] => return owner
      | arg :: rest =>
        arguments := rest
        current := .mk body (arg :: bindings)
    | .bvar index =>
      match bindings with
      | [] => throw s!"IE-C003 ArenaResolutionFailed: {spelling}"
      | value :: rest =>
        current := if index == 0 then value else .mk (.bvar (index - 1)) rest
    | .const name _ =>
      if arguments.isEmpty then owner := name
      match find name with
      | some (.defnInfo info) => current := .mk info.value []
      | _ => return owner
    | _ => return owner
  throw s!"IE-C003 ArenaResolutionBudgetExceeded arena={spelling} limit={arenaAliasWorkBudget}"

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

import LeanInformationAudit.Registry
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import Mathlib.Data.Fin.VecNotation

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command
open Lean.Meta
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

/-- A closed catalog and the canonical theorem-to-index assignment used by the seal. -/
structure CatalogUnitRecord where
  theoremName : Name
  unitName : Name
  sourceUnitName : Name
  realizationName : Name
  registrationModuleName : Name
  index : Nat
  deriving Inhabited

structure CatalogRecord where
  rootId : Name
  catalogId : CatalogId
  catalogKind : CatalogKind
  arenaName : Name
  catalogName : Name
  units : Array CatalogUnitRecord
  compatibilityV2 : Bool

structure PreparedCatalog where
  record : CatalogRecord
  arenaValue : Expr
  type : Expr
  value : Expr
  declaration : Declaration

private def nameLess (left right : Name) : Bool :=
  left.lt right

private def catalogNameFor (rootId arenaName : Name) (catalogId : CatalogId)
    (compatibilityV2 : Bool) : Name :=
  if compatibilityV2 then arenaName.str "__information_catalog"
  else catalogQualifiedName rootId arenaName catalogId arenaName "__information_catalog"

private def entryArenaValue (entry : InformationRegistryEntry) : MetaM Expr := do
  if entry.objectArenaName.isAnonymous then
    mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
      #[mkConst entry.arenaName]
  else
    mkConstWithFreshMVarLevels entry.objectArenaName

private def propositionIsTrue (proposition : Expr) : MetaM Bool := do
  let decision ← mkDecide proposition
  reduceEval decision

private def validateEntry (env : Environment) (entry : InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM Unit := do
  match ← validatePersistedEntry env entry with
  | .ok () => pure ()
  | .error message => throwError message
  let unitExpr := mkConst entry.unitName
  let primitives ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
    #[unitExpr]
  let nonempty ← mkAppM
    `D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.Nonempty #[primitives]
  unless ← propositionIsTrue nonempty do
    throwError "IE-C013 MissingPrimitiveBundle: {entry.theoremName}"

private def makeUnitVector (units : Array Expr) : Lean.Elab.Term.TermElabM Expr := do
  let finZero := mkApp (mkConst ``Fin) (mkNatLit 0)
  let mut vector ← withLocalDeclD `impossible finZero fun impossible => do
    mkLambdaFVars #[impossible] units[0]!
  for unit in units.reverse do
    vector ← mkAppM ``Matrix.vecCons #[unit, vector]
  pure vector

private def nameArrayJson (names : Array Name) : String :=
  (Json.arr <| names.map fun name => Json.str name.toString).compress

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

private def prepareCatalog (rootId arenaName : Name) (compatibilityV2 : Bool)
    (entries : Array InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM PreparedCatalog := do
  let sorted := entries.qsort fun left right => nameLess left.theoremName right.theoremName
  let catalogId <- match validateMaximalCatalog rootId arenaName sorted with
    | .ok catalogId => pure catalogId
    | .error message => throwError message
  let some firstEntry := sorted[0]?
    | throwError "IE-C026 MissingMaximalCatalog root={rootId} arena={arenaName} occurrences=[]"
  let arena ← entryArenaValue firstEntry
  let nondegenerate ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.Nondegenerate #[arena]
  unless ← propositionIsTrue nondegenerate do
    throwError "IE-C004 DegenerateArena: {arenaName}"
  let unitExprs := sorted.map fun entry => mkConst entry.computationalUnitName
  let vector ← makeUnitVector unitExprs
  let value ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector #[vector]
  let type ← inferType value
  let units := sorted.mapIdx fun index entry => {
    theoremName := entry.theoremName
    unitName := entry.unitName
    sourceUnitName := entry.computationalUnitName
    realizationName := entry.realizationName
    registrationModuleName := entry.registrationModuleName
    index
  }
  let catalogName := catalogNameFor rootId arenaName catalogId compatibilityV2
  let declaration := .defnDecl {
    name := catalogName
    levelParams := []
    type
    value
    hints := .abbrev
    safety := .safe
  }
  pure {
    record := {
      rootId
      catalogId
      catalogKind := .canonicalMaximal
      arenaName
      catalogName
      units
      compatibilityV2
    }
    arenaValue := arena
    type
    value
    declaration
  }

private def groupEntries (entries : Array InformationRegistryEntry) :
    Array (Name × Array InformationRegistryEntry) :=
  entries.foldl (init := #[]) fun groups entry =>
    match groups.findIdx? fun group => group.1 == entry.canonicalObjectArenaName with
    | some index => groups.modify index fun group => (group.1, group.2.push entry)
    | none => groups.push (entry.canonicalObjectArenaName, #[entry])

/-- Validate source entries and prepare catalogs from their seal-qualified forms. -/
def prepareCatalogsFromEntries (sourceEntries catalogEntries :
    Array InformationRegistryEntry) : CommandElabM (Array PreparedCatalog) := do
  let env ← getEnv
  if sourceEntries.isEmpty then
    throwError "IE-C001 UnregisteredTheoremUnit: registry is empty"
  liftTermElabM <| sourceEntries.forM (validateEntry env)
  let rootId := env.header.mainModule
  let compatibilityV2 := sourceEntries.all fun entry =>
    entry.legacyNaming && entry.registrationModuleName == rootId
  let groups := (groupEntries catalogEntries).qsort fun left right => nameLess left.1 right.1
  let catalogs <- liftTermElabM <| groups.mapM fun group =>
    prepareCatalog rootId group.1 compatibilityV2 group.2
  pure <| catalogs.qsort fun left right =>
    nameLess left.record.catalogId right.record.catalogId ||
      (left.record.catalogId == right.record.catalogId &&
        nameLess left.record.arenaName right.record.arenaName)

/-- Validate the registry and prepare catalogs without changing the environment. -/
def prepareCatalogs : CommandElabM (Array PreparedCatalog) := do
  let entries := InformationRegistry.entries (← getEnv)
  prepareCatalogsFromEntries entries entries

end LeanInformationAudit

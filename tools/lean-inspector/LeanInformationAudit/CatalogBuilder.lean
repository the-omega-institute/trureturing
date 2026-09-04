import LeanInformationAudit.Registry
import D5.S3.ConceptDynamics.InformationEscape.ExactRate

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command
open Lean.Meta
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

/-- A closed catalog and the canonical theorem-to-index assignment used by the seal. -/
structure CatalogRecord where
  arenaName : Name
  catalogName : Name
  units : Array (Name × Nat)

private structure PendingCatalog where
  record : CatalogRecord
  type : Expr
  value : Expr

private def nameLess (left right : Name) : Bool :=
  left.toString < right.toString

private def catalogNameFor (arenaName : Name) : Name :=
  arenaName.str "__information_catalog"

private def arenaValue (arenaName : Name) : MetaM Expr := do
  mkAppM `PrimitiveLawArena.toArena #[mkConst arenaName]

private def validateEntry (env : Environment) (entry : InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM Unit := do
  match ← validatePersistedEntry env entry with
  | .ok () => pure ()
  | .error message => throwError message
  let unitExpr := mkConst entry.unitName
  let primitives ← mkAppM `TheoremUnit.primitives #[unitExpr]
  let nonempty ← mkAppM `PrimitiveBundle.Nonempty #[primitives]
  try
    let _ ← mkDecideProof nonempty
    pure ()
  catch _ =>
    throwError "IE-C013 MissingPrimitiveBundle: {entry.theoremName}"

private def makeUnitVector (units : Array Expr) : Lean.Elab.Term.TermElabM Expr := do
  let finZero := mkApp (mkConst ``Fin) (mkNatLit 0)
  let mut vector ← withLocalDeclD `impossible finZero fun impossible => do
    mkLambdaFVars #[impossible] units[0]!
  for unit in units.reverse do
    vector ← mkAppM ``Fin.cons #[unit, vector]
  pure vector

private def prepareCatalog (arenaName : Name)
    (entries : Array InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM PendingCatalog := do
  let sorted := entries.qsort fun left right => nameLess left.theoremName right.theoremName
  let arena ← arenaValue arenaName
  let nondegenerate ← mkAppM `Arena.Nondegenerate #[arena]
  try
    let _ ← mkDecideProof nondegenerate
    pure ()
  catch _ =>
    throwError "IE-C004 DegenerateArena: {arenaName}"
  let unitExprs := sorted.map fun entry => mkConst entry.unitName
  let vector ← makeUnitVector unitExprs
  let value ← mkAppM `Catalog.ofVector #[vector]
  let type ← inferType value
  let units := sorted.mapIdx fun index entry => (entry.theoremName, index)
  pure {
    record := { arenaName, catalogName := catalogNameFor arenaName, units }
    type
    value
  }

private def groupEntries (entries : Array InformationRegistryEntry) :
    Array (Name × Array InformationRegistryEntry) :=
  entries.foldl (init := #[]) fun groups entry =>
    match groups.findIdx? fun group => group.1 == entry.arenaName with
    | some index => groups.modify index fun group => (group.1, group.2.push entry)
    | none => groups.push (entry.arenaName, #[entry])

/-- Validate the registry, construct canonical catalogs, and add their reducible definitions. -/
def buildCatalogs : CommandElabM (Array CatalogRecord) := do
  let env ← getEnv
  let entries := InformationRegistry.entries env
  if entries.isEmpty then
    throwError "IE-C001 UnregisteredTheoremUnit: registry is empty"
  liftTermElabM <| entries.forM (validateEntry env)
  let groups := (groupEntries entries).qsort fun left right => nameLess left.1 right.1
  let pending ← liftTermElabM <| groups.mapM fun group =>
    prepareCatalog group.1 group.2
  for catalog in pending do
    liftCoreM <| addAndCompile <| .defnDecl {
      name := catalog.record.catalogName
      levelParams := []
      type := catalog.type
      value := catalog.value
      hints := .abbrev
      safety := .safe
    }
  pure <| pending.map (·.record)

end LeanInformationAudit

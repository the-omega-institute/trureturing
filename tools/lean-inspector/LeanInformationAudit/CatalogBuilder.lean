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
  index : Nat

structure CatalogRecord where
  arenaName : Name
  catalogName : Name
  units : Array CatalogUnitRecord

structure PreparedCatalog where
  record : CatalogRecord
  type : Expr
  value : Expr
  declaration : Declaration

private def nameLess (left right : Name) : Bool :=
  left.lt right

private def catalogNameFor (arenaName : Name) : Name :=
  arenaName.str "__information_catalog"

private def arenaValue (arenaName : Name) : MetaM Expr := do
  mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
    #[mkConst arenaName]

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

private def prepareCatalog (arenaName : Name)
    (entries : Array InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM PreparedCatalog := do
  let sorted := entries.qsort fun left right => nameLess left.theoremName right.theoremName
  let arena ← arenaValue arenaName
  let nondegenerate ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.Nondegenerate #[arena]
  unless ← propositionIsTrue nondegenerate do
    throwError "IE-C004 DegenerateArena: {arenaName}"
  let unitExprs := sorted.map fun entry => mkConst entry.unitName
  let vector ← makeUnitVector unitExprs
  let value ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector #[vector]
  let type ← inferType value
  let units := sorted.mapIdx fun index entry => {
    theoremName := entry.theoremName
    unitName := entry.unitName
    index
  }
  let catalogName := catalogNameFor arenaName
  let declaration := .defnDecl {
    name := catalogName
    levelParams := []
    type
    value
    hints := .abbrev
    safety := .safe
  }
  pure {
    record := { arenaName, catalogName, units }
    type
    value
    declaration
  }

private def groupEntries (entries : Array InformationRegistryEntry) :
    Array (Name × Array InformationRegistryEntry) :=
  entries.foldl (init := #[]) fun groups entry =>
    match groups.findIdx? fun group => group.1 == entry.arenaName with
    | some index => groups.modify index fun group => (group.1, group.2.push entry)
    | none => groups.push (entry.arenaName, #[entry])

/-- Validate the registry and prepare catalogs without changing the environment. -/
def prepareCatalogs : CommandElabM (Array PreparedCatalog) := do
  let env ← getEnv
  let entries := InformationRegistry.entries env
  if entries.isEmpty then
    throwError "IE-C001 UnregisteredTheoremUnit: registry is empty"
  liftTermElabM <| entries.forM (validateEntry env)
  let groups := (groupEntries entries).qsort fun left right => nameLess left.1 right.1
  liftTermElabM <| groups.mapM fun group =>
    prepareCatalog group.1 group.2

end LeanInformationAudit

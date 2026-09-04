import LeanInformationAudit.CatalogBuilder

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command
open Lean.Meta
open D5.S3.ConceptDynamics.InformationEscape

/-- Computed theorem data retained for summaries and the optional artifact. -/
structure SealTheoremRecord where
  theoremName : Name
  index : Nat
  uniqueCaptureCount : Nat
  fullEscapeCount : Nat
  withoutEscapeCount : Nat
  proofMethod : String

/-- Computed arena data retained for summaries and the optional artifact. -/
structure SealArenaRecord where
  catalog : CatalogRecord
  stateCard : Nat
  theorems : Array SealTheoremRecord

private structure PendingTheorem where
  name : Name
  type : Expr
  value : Expr

private def finValue (index size : Nat) : MetaM Expr := do
  let bound ← mkLT (mkNatLit index) (mkNatLit size)
  let boundProof ← mkDecideProof bound
  mkAppM ``Fin.mk #[mkNatLit index, boundProof]

private def natValue (expr : Expr) : MetaM Nat :=
  reduceEval expr

private def theoremProofs (record : CatalogRecord) : MetaM
    (Array PendingTheorem × SealArenaRecord) := do
  let catalog := mkConst record.catalogName
  let arena ← mkAppM `PrimitiveLawArena.toArena #[mkConst record.arenaName]
  let nondegenerateType ← mkAppM `Arena.Nondegenerate #[arena]
  let nondegenerateProof ← mkDecideProof nondegenerateType
  let stateCardExpr ← mkAppM `Arena.card #[arena]
  let stateCard ← natValue stateCardExpr
  let fullSet ← mkAppM `Catalog.fullIndexSet #[catalog]
  let fullExpr ← mkAppM `Catalog.escapeNumerator #[catalog, fullSet]
  let fullCount ← natValue fullExpr
  let mut declarations := #[]
  let mut theoremRecords := #[]
  for unit in record.units do
    let theoremName := unit.1
    let indexNat := unit.2
    let index ← finValue indexNat record.units.size
    let uniqueExpr ← mkAppM `Catalog.uniqueCaptureCount #[catalog, index]
    let uniqueCount ← natValue uniqueExpr
    let withoutSet ← mkAppM `Catalog.without #[catalog, index]
    let withoutExpr ← mkAppM `Catalog.escapeNumerator #[catalog, withoutSet]
    let withoutCount ← natValue withoutExpr
    if uniqueCount == 0 then
      throwError
        "IE-C007 ZeroUniqueCapture: theorem {theoremName} arena {record.arenaName} \
full {fullCount} without {withoutCount}"
    let positiveType ← mkLT (mkNatLit 0) uniqueExpr
    let positiveProof ← mkDecideProof positiveType
    let characterization ← mkAppM
      `Catalog.lowersEscape_iff_uniqueCaptureCount_pos
      #[catalog, index, nondegenerateProof]
    let lowersProof ← mkAppM ``Iff.mpr #[characterization, positiveProof]
    let lowersType ← inferType lowersProof
    let lowersName := theoremName.str "__lowers_escape"
    declarations := declarations.push {
      name := lowersName
      type := lowersType
      value := lowersProof
    }
    let theoremExpr := mkConst theoremName
    let theoremType ← inferType theoremExpr
    let enrichedType ← mkAppM ``And #[theoremType, lowersType]
    let enrichedProof ← mkAppM ``And.intro #[theoremExpr, lowersProof]
    declarations := declarations.push {
      name := theoremName.str "__escape_enriched"
      type := enrichedType
      value := enrichedProof
    }
    theoremRecords := theoremRecords.push {
      theoremName
      index := indexNat
      uniqueCaptureCount := uniqueCount
      fullEscapeCount := fullCount
      withoutEscapeCount := withoutCount
      proofMethod := "decide"
    }
  let finType := mkApp (mkConst ``Fin) (mkNatLit record.units.size)
  let irredundantType ← withLocalDeclD `index finType fun index => do
    let lowers ← mkAppM `Catalog.LowersEscape #[catalog, index]
    mkForallFVars #[index] lowers
  let irredundantProof ← mkDecideProof irredundantType
  declarations := declarations.push {
    name := record.arenaName.str "__catalog_irredundant"
    type := irredundantType
    value := irredundantProof
  }
  pure (declarations, { catalog := record, stateCard, theorems := theoremRecords })

/-- Construct every proof first, then atomically expose all theorem declarations. -/
def buildProofs (catalogs : Array CatalogRecord) :
    CommandElabM (Array SealArenaRecord) := do
  let results ← liftTermElabM <| catalogs.mapM theoremProofs
  for result in results do
    for declaration in result.1 do
      addDecl <| .thmDecl {
        name := declaration.name
        levelParams := []
        type := declaration.type
        value := declaration.value
      }
  pure <| results.map (·.2)

end LeanInformationAudit

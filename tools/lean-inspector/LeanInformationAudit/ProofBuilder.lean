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

private def mkDecideProofWith (proposition decidable : Expr) : MetaM Expr := do
  let decision := mkApp2 (mkConst ``Decidable.decide) proposition decidable
  let decisionTrue ← mkEq decision (mkConst ``Bool.true)
  let reflexivity ← mkEqRefl (mkConst ``Bool.true)
  let reduction := mkExpectedPropHint reflexivity decisionTrue
  pure <| mkApp3 (mkConst ``of_decide_eq_true) proposition decidable reduction

private def theoremProofs (record : CatalogRecord) : Lean.Elab.Term.TermElabM
    (Array PendingTheorem × SealArenaRecord) := do
  let catalog := mkConst record.catalogName
  let arena ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
    #[mkConst record.arenaName]
  let nondegenerateType ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.Nondegenerate #[arena]
  let nondegenerateProof ← mkDecideProof nondegenerateType
  let stateCardExpr ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.card #[arena]
  let stateCard ← natValue stateCardExpr
  let fullSet ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Catalog.fullIndexSet #[catalog]
  let fullExpr ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Catalog.escapeNumerator
    #[catalog, fullSet]
  let fullCount ← natValue fullExpr
  let mut declarations := #[]
  let mut theoremRecords := #[]
  for unit in record.units do
    let theoremName := unit.1
    let indexNat := unit.2
    let index ← finValue indexNat record.units.size
    let uniqueExpr ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
      #[catalog, index]
    let uniqueCount ← natValue uniqueExpr
    let withoutSet ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.without #[catalog, index]
    let withoutExpr ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.escapeNumerator
      #[catalog, withoutSet]
    let withoutCount ← natValue withoutExpr
    if uniqueCount == 0 then
      throwError
        "IE-C007 ZeroUniqueCapture: theorem {theoremName} arena {record.arenaName} \
full {fullCount} without {withoutCount}"
    let positiveType ← mkLT (mkNatLit 0) uniqueExpr
    let positiveProof ← mkDecideProof positiveType
    let characterization ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos
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
  let allPositiveType ← withLocalDeclD `index finType fun index => do
    let count ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
      #[catalog, index]
    let positive ← mkLT (mkNatLit 0) count
    mkForallFVars #[index] positive
  let positivePredicate ← withLocalDeclD `index finType fun index => do
    let count ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
      #[catalog, index]
    let positive ← mkLT (mkNatLit 0) count
    mkLambdaFVars #[index] positive
  let decidablePredicate ← withLocalDeclD `index finType fun index => do
    let count ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
      #[catalog, index]
    let decision := mkApp2 (mkConst ``Nat.decLt) (mkNatLit 0) count
    mkLambdaFVars #[index] decision
  let finFintypeType ← mkAppM ``Fintype #[finType]
  let finFintype ← synthInstance finFintypeType
  let allPositiveDecidable := mkAppN
    (mkConst ``Fintype.decidableForallFintype [0])
    #[finType, positivePredicate, decidablePredicate, finFintype]
  let allPositiveProof ←
    mkDecideProofWith allPositiveType allPositiveDecidable
  let irredundantProof ← withLocalDeclD `index finType fun index => do
    let positiveProof := mkApp allPositiveProof index
    let characterization ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos
      #[catalog, index, nondegenerateProof]
    let lowersProof ← mkAppM ``Iff.mpr #[characterization, positiveProof]
    mkLambdaFVars #[index] lowersProof
  let irredundantType ← inferType irredundantProof
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
      liftCoreM <| addDecl <| .thmDecl {
        name := declaration.name
        levelParams := []
        type := declaration.type
        value := declaration.value
      }
  pure <| results.map (·.2)

end LeanInformationAudit

import LeanInformationAudit.CatalogBuilder

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command
open Lean.Meta
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

universe u v w

/-- Computed theorem data retained for summaries and the optional artifact. -/
structure SealTheoremRecord where
  theoremName : Name
  unitName : Name
  index : Nat
  primitiveCount : Nat
  primitiveAxes : Array String
  primitiveKernelAddress : String
  uniqueCaptureCount : Nat
  fullEscapeCount : Nat
  withoutEscapeCount : Nat
  roleSignatureHistogram : Array (String × Nat)
  proofMethod : String

/-- Computed arena data retained for summaries and the optional artifact. -/
structure SealArenaRecord where
  catalog : CatalogRecord
  stateCard : Nat
  offDiagonalPairCount : Nat
  fullEscapeCount : Nat
  theorems : Array SealTheoremRecord

structure PreparedProofs where
  declarations : Array Declaration
  records : Array SealArenaRecord

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

private def primitiveCount {X : Type u} (bundle : PrimitiveBundle X) : Nat :=
  @Fintype.card bundle.Index bundle.indexFintype

private def primitiveAxisCount {X : Type u} (bundle : PrimitiveBundle X)
    (axis : PrimitiveAxis) : Nat := by
  letI := bundle.indexFintype
  letI := bundle.indexDecidableEq
  exact (Finset.univ.filter fun index => (bundle.atom index).axis = axis).card

/-- Hash the canonical ordinal partition induced by the compiled primitive kernel. -/
private unsafe def primitiveKernelAddress {X : Type u} (stateFintype : Fintype X)
    (bundle : PrimitiveBundle X) : String := by
  letI := stateFintype
  let states := (unsafe stateFintype.elems.val.unquot).toArray
  let ordinals := List.range states.size
  let classes := ordinals.foldl (init := #[]) fun classes ordinal =>
    match classes.findIdx? fun candidate =>
        match states[ordinal]?, candidate[0]? with
        | some state, some representative =>
            match states[representative]? with
            | some representativeState => bundle.agreesB state representativeState
            | none => false
        | _, _ => false with
    | some index => classes.modify index fun candidate => candidate.push ordinal
    | none => classes.push #[ordinal]
  exact toString (hash classes)

private def uniqueCaptureSignatureCount {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (index : catalog.Index)
    (cutBit flowBit admitBit anchorBit : Bool) : Nat :=
  let signature : Fin 4 → Bool := ![cutBit, flowBit, admitBit, anchorBit]
  ((catalog.uniqueCapturePairs index).filter fun pair =>
    (catalog.theoremAt index).primitives.roleSignature pair.1 pair.2 = signature).card

private def signatureBit (mask coordinate : Nat) : Bool :=
  mask / (2 ^ (3 - coordinate)) % 2 == 1

private def signatureLabel (mask : Nat) : String :=
  String.ofList <| (List.range 4).map fun coordinate =>
    if signatureBit mask coordinate then '1' else '0'

private def proofConstruction (theoremName : Name)
    (action : Lean.Elab.Term.TermElabM α) : Lean.Elab.Term.TermElabM α := do
  try action catch error =>
    throwError "IE-C009 ProofConstructionFailed: {theoremName}\n{error.toMessageData}"

private def theoremProofs (prepared : PreparedCatalog) : Lean.Elab.Term.TermElabM
    (Array Declaration × SealArenaRecord) := do
  let record := prepared.record
  let catalog := prepared.value
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
    let theoremName := unit.theoremName
    let unitName := unit.unitName
    let indexNat := unit.index
    let index ← finValue indexNat record.units.size
    let unitExpr := mkConst unitName
    let primitives ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
      #[unitExpr]
    let primitiveCountExpr ← mkAppM ``primitiveCount #[primitives]
    let primitiveCount ← natValue primitiveCountExpr
    let stateFintype ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Arena.stateFintype #[arena]
    let kernelAddressExpr ← mkAppM ``primitiveKernelAddress #[stateFintype, primitives]
    let primitiveKernelAddress ← unsafe evalExpr String (mkConst ``String)
      kernelAddressExpr (safety := .unsafe)
    let mut primitiveAxes := #[]
    for (axisName, label) in
        #[( ``PrimitiveAxis.cut, "cut"), (``PrimitiveAxis.flow, "flow"),
          (``PrimitiveAxis.admit, "admit"), (``PrimitiveAxis.anchor, "anchor")] do
      let countExpr ← mkAppM ``primitiveAxisCount
        #[primitives, mkConst axisName]
      let count ← natValue countExpr
      for _ in [:count] do
        primitiveAxes := primitiveAxes.push label
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
    let positiveProof ← proofConstruction theoremName <| mkDecideProof positiveType
    let mut roleSignatureHistogram := #[]
    for mask in [1:16] do
      let signatureCountExpr ← mkAppM ``uniqueCaptureSignatureCount
        #[catalog, index,
          mkConst (if signatureBit mask 0 then ``Bool.true else ``Bool.false),
          mkConst (if signatureBit mask 1 then ``Bool.true else ``Bool.false),
          mkConst (if signatureBit mask 2 then ``Bool.true else ``Bool.false),
          mkConst (if signatureBit mask 3 then ``Bool.true else ``Bool.false)]
      let signatureCount ← natValue signatureCountExpr
      if signatureCount != 0 then
        roleSignatureHistogram := roleSignatureHistogram.push
          (signatureLabel mask, signatureCount)
    let histogramTotal := roleSignatureHistogram.foldl (init := 0)
      fun total entry => total + entry.2
    unless histogramTotal == uniqueCount do
      throwError "IE-C009 ProofConstructionFailed: {theoremName}\nrole histogram mismatch"
    let (lowersProof, lowersType) ← proofConstruction theoremName do
      let characterization ← mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos
        #[catalog, index, nondegenerateProof]
      let lowersProof ← mkAppM ``Iff.mpr #[characterization, positiveProof]
      pure (lowersProof, ← inferType lowersProof)
    let lowersName := theoremName.str "__lowers_escape"
    declarations := declarations.push <| .thmDecl {
      name := lowersName
      levelParams := []
      type := lowersType
      value := lowersProof
    }
    let theoremExpr := mkConst theoremName
    let theoremType ← inferType theoremExpr
    let enrichedType ← mkAppM ``And #[theoremType, lowersType]
    let enrichedProof ← mkAppM ``And.intro #[theoremExpr, lowersProof]
    declarations := declarations.push <| .thmDecl {
      name := theoremName.str "__escape_enriched"
      levelParams := []
      type := enrichedType
      value := enrichedProof
    }
    theoremRecords := theoremRecords.push {
      theoremName
      unitName
      index := indexNat
      primitiveCount
      primitiveAxes
      primitiveKernelAddress
      uniqueCaptureCount := uniqueCount
      fullEscapeCount := fullCount
      withoutEscapeCount := withoutCount
      roleSignatureHistogram
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
  declarations := declarations.push <| .thmDecl {
    name := record.arenaName.str "__catalog_irredundant"
    levelParams := []
    type := irredundantType
    value := irredundantProof
  }
  pure (declarations, {
    catalog := record
    stateCard
    offDiagonalPairCount := stateCard * (stateCard - 1)
    fullEscapeCount := fullCount
    theorems := theoremRecords
  })

/-- Construct all theorem declarations without changing the environment. -/
def prepareProofs (catalogs : Array PreparedCatalog) : CommandElabM PreparedProofs := do
  let results ← liftTermElabM <| catalogs.mapM theoremProofs
  pure {
    declarations := results.foldl (init := #[]) fun all result => all ++ result.1
    records := results.map (·.2)
  }

end LeanInformationAudit

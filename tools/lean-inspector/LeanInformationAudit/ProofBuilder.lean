import LeanInformationAudit.CatalogBuilder
import LeanInformationAudit.Sha256
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
-- Enumerations is imported only to expose the production `__state_enumeration` witnesses.
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations

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
  realizationName : Name
  certificateName : Name
  registrationModuleName : Name
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
  irredundantCertificateName : Name
  proofMethod : String
  stateCard : Nat
  offDiagonalPairCount : Nat
  fullEscapeCount : Nat
  theorems : Array SealTheoremRecord

structure PreparedProofs where
  declarations : Array Declaration
  records : Array SealArenaRecord

/-- A strict host-side copy of one reflected catalog-wide count. -/
private structure ReflectedFusedSnapshot where
  full : Nat
  unique : Array Nat
  roleBins : Array (Array Nat)

/-- Marker consumed only by the custom `ReduceEval` instance below. -/
private def reflectedSnapshotRequest {n : Nat}
    (counts : Catalog.FusedCounts (Fin n)) : Catalog.FusedCounts (Fin n) :=
  counts

private def finValue (index size : Nat) : MetaM Expr := do
  let bound ← mkLT (mkNatLit index) (mkNatLit size)
  let boundProof ← mkDecideProof bound
  mkAppM ``Fin.mk #[mkNatLit index, boundProof]

private instance : ReduceEval ReflectedFusedSnapshot where
  reduceEval request := do
    unless request.isAppOfArity ``reflectedSnapshotRequest 2 do
      throwError "reduceEval: expected a reflected fused snapshot request"
    let size : Nat ← reduceEval (request.getArg! 0)
    let counts ← whnf (request.getArg! 1)
    unless counts.isAppOfArity ``Catalog.FusedCounts.mk 4 do
      throwError "reduceEval: failed to match the fused counts constructor"
    let full : Nat ← reduceEval (counts.getArg! 1)
    let uniqueFn := counts.getArg! 2
    let roleBinsFn := counts.getArg! 3
    let mut unique := #[]
    let mut roleBins := #[]
    for indexNat in [:size] do
      let index ← finValue indexNat size
      unique := unique.push (← reduceEval (mkApp uniqueFn index))
      let mut bins := #[]
      for bucketNat in [:15] do
        let bucket ← finValue bucketNat 15
        bins := bins.push (← reduceEval (mkApp2 roleBinsFn index bucket))
      roleBins := roleBins.push bins
    pure { full, unique, roleBins }

private def natValue (expr : Expr) : MetaM Nat :=
  reduceEval expr

private def primitiveCount {X : Type u} (bundle : PrimitiveBundle X) : Nat :=
  @Fintype.card bundle.Index bundle.indexFintype

private def primitiveAxisCount {X : Type u} (bundle : PrimitiveBundle X)
    (axis : PrimitiveAxis) : Nat := by
  letI := bundle.indexFintype
  letI := bundle.indexDecidableEq
  exact (Finset.univ.filter fun index => (bundle.atom index).axis = axis).card

/--
Serialize classes in first-representative order as
`class_count;class_1_ordinals;...`, then SHA-256 those ASCII bytes. The address is
an output-only projection and is never read as seal decision input.
-/
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
  let encodedClasses := classes.toList.map fun candidate =>
    String.intercalate "," (candidate.toList.map toString)
  let serialization := String.intercalate ";" (toString classes.size :: encodedClasses)
  exact "sha256:" ++ Sha256.hex serialization.toUTF8

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

/-- Keep CIRPT-40(8) as an independent host-side check on all fifteen buckets. -/
private def validateRoleHistogram (theoremName : Name) (uniqueCount : Nat)
    (roleBins : Array Nat) : Except String Unit := do
  let histogramTotal := roleBins.foldl (init := 0) (· + ·)
  unless histogramTotal == uniqueCount do
    throw s!"IE-C009 ProofConstructionFailed: {theoremName}\nrole histogram mismatch"

private def natArrayJson (values : Array Nat) : String :=
  (Json.arr <| values.map toJson).compress

private def catalogIndexCount {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Nat :=
  @Fintype.card catalog.Index catalog.indexFintype

/-- Bind the checked vector to the compiled catalog's full index domain. -/
def validateCompleteCountVector (rootId : Name) (catalogId : CatalogId)
    (memberCount : Nat) (expectedCounts checkedCounts : Array Nat) : Except String Unit := do
  unless expectedCounts.size == memberCount && checkedCounts == expectedCounts do
    let expected := toJson (memberCount, expectedCounts)
    let actual := toJson (checkedCounts.size, checkedCounts)
    throw s!"IE-C028 AnalysisCertificateMismatch root={rootId} catalog={catalogId} \
component=count-vector expected={expected.compress} actual={actual.compress}"

/-- Independently derive and check every zero index from the complete count vector. -/
def validateRedundantIndices (rootId : Name) (catalogId : CatalogId)
    (uniqueCounts certified : Array Nat) (phase : String) : Except String Unit := do
  let expected := (uniqueCounts.foldl (init := (#[], 0))
    (fun (result, index) count =>
      (if count == 0 then result.push index else result, index + 1))).1
  unless expected == certified do
    throw s!"IE-C033 IncompleteRedundantIndexSet key={rootId}/{catalogId} \
expected={natArrayJson expected} certified={natArrayJson certified} phase={phase}"

private structure ReflectedRoute where
  witness : Expr
  indices : Expr
  counts : Expr
  snapshot : ReflectedFusedSnapshot

private inductive CountingRoute where
  | decide
  | reflected (route : ReflectedRoute)

private def proofConstruction (theoremName : Name)
    (action : Lean.Elab.Term.TermElabM α) : Lean.Elab.Term.TermElabM α := do
  try action catch error =>
    throwError "IE-C009 ProofConstructionFailed: {theoremName}\n{error.toMessageData}"

private def discoverCountingRoute (prepared : PreparedCatalog) (arena : Expr) :
    Lean.Elab.Term.TermElabM CountingRoute := do
  let record := prepared.record
  let witnessName := record.arenaName.str "__state_enumeration"
  let env ← getEnv
  match env.find? witnessName with
  | none => pure .decide
  | some _ =>
      let _ ← getConstInfo witnessName
      let witness ← mkConstWithFreshMVarLevels witnessName
      let expectedType ← mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration #[arena]
      unless ← isDefEq (← inferType witness) expectedType do
        throwError
          "IE-C009 ProofConstructionFailed: {witnessName}\nexpected type \
Arena.StateEnumeration {record.arenaName}.toArena"
      let indices ← mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration
        #[mkNatLit record.units.size]
      let counts ← mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Catalog.fusedCounts
        #[prepared.value, witness, indices]
      let request ← mkAppM ``reflectedSnapshotRequest #[counts]
      let failureName := (record.units.map (·.theoremName))[0]!
      let snapshot ← proofConstruction failureName <|
        reduceEval request
      pure <| .reflected { witness, indices, counts, snapshot }

private def finSuccN (offset : Nat) (index : Expr) : MetaM Expr := do
  let mut result := index
  for _ in [:offset] do
    result ← mkAppM ``Fin.succ #[result]
  pure result

private def loweringMotive (catalog : Expr) (offset remaining : Nat) : MetaM Expr := do
  let finType := mkApp (mkConst ``Fin) (mkNatLit remaining)
  withLocalDeclD `index finType fun index => do
    let globalIndex ← finSuccN offset index
    let target ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.LowersEscape
      #[catalog, globalIndex]
    mkLambdaFVars #[index] target

private partial def finCasesValue (catalog : Expr) (names : Array Name)
    (offset remaining : Nat) (index : Expr) : MetaM Expr := do
  if remaining == 0 then
    let globalIndex ← finSuccN offset index
    let target ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.LowersEscape
      #[catalog, globalIndex]
    pure <| mkApp2 (mkConst ``Fin.elim0 [0]) target index
  else
    let motive ← loweringMotive catalog offset remaining
    let head := mkConst names[offset]!
    let tailType := mkApp (mkConst ``Fin) (mkNatLit (remaining - 1))
    let tail ← withLocalDeclD `index tailType fun tailIndex => do
      let body ← finCasesValue catalog names (offset + 1) (remaining - 1) tailIndex
      mkLambdaFVars #[tailIndex] body
    pure <| mkAppN (mkConst ``Fin.cases [0])
      #[mkNatLit (remaining - 1), motive, head, tail, index]

private def irredundantFromLoweringProofs (catalog : Expr)
    (names : Array Name) : MetaM Expr := do
  let finType := mkApp (mkConst ``Fin) (mkNatLit names.size)
  withLocalDeclD `index finType fun index => do
    let body ← finCasesValue catalog names 0 names.size index
    mkLambdaFVars #[index] body

private def theoremProofs (prepared : PreparedCatalog) : Lean.Elab.Term.TermElabM
    (Array Declaration × SealArenaRecord) := do
  let record := prepared.record
  let catalog := prepared.value
  let arena := prepared.arenaValue
  let nondegenerateType ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.Nondegenerate #[arena]
  let nondegenerateProof ← mkDecideProof nondegenerateType
  let stateCardExpr ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.card #[arena]
  let stateCard ← natValue stateCardExpr
  let route ← discoverCountingRoute prepared arena
  let pairBudget := stateCard * (stateCard - 1)
  if pairBudget > 65536 then
    match route with
    | .decide =>
        throwError
          "IE-C032 SizeBudgetRequiresReflectedSeal root={record.rootId} \
catalog={record.catalogId} pair_budget={pairBudget} limit=65536 seal={record.rootId}"
    | .reflected _ => pure ()
  let fullCount ← match route with
    | .decide =>
        let fullSet ← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.Catalog.fullIndexSet #[catalog]
        let fullExpr ← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.Catalog.escapeNumerator
          #[catalog, fullSet]
        natValue fullExpr
    | .reflected reflected => pure reflected.snapshot.full
  let mut declarations := #[]
  let mut theoremRecords := #[]
  let mut loweringProofNames := #[]
  let mut uniqueCounts := #[]
  let mut withoutCounts := #[]
  for unit in record.units do
    let index <- finValue unit.index record.units.size
    let uniqueExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
      #[catalog, index]
    let uniqueCount <- match route with
      | .decide => natValue uniqueExpr
      | .reflected reflected => pure reflected.snapshot.unique[unit.index]!
    let withoutCount <- match route with
      | .decide =>
          let withoutSet <- mkAppM
            `D5.S3.ConceptDynamics.InformationEscape.Catalog.without #[catalog, index]
          let withoutExpr <- mkAppM
            `D5.S3.ConceptDynamics.InformationEscape.Catalog.escapeNumerator
            #[catalog, withoutSet]
          natValue withoutExpr
      | .reflected _ => pure (fullCount + uniqueCount)
    uniqueCounts := uniqueCounts.push uniqueCount
    withoutCounts := withoutCounts.push withoutCount
  let compiledSize ← natValue (← mkAppM ``catalogIndexCount #[catalog])
  let expectedCounts ← match route with
    | .decide => (Array.range compiledSize).mapM fun indexNat => do
        let index ← finValue indexNat compiledSize
        natValue (← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
          #[catalog, index])
    | .reflected reflected => pure reflected.snapshot.unique
  let mut redundantIndices := #[]
  for index in [:uniqueCounts.size] do
    if uniqueCounts[index]! == 0 then
      redundantIndices := redundantIndices.push index
  let mut certifiedRedundantIndices := #[]
  for indexNat in redundantIndices do
    let index <- finValue indexNat record.units.size
    let uniqueExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount
      #[catalog, index]
    let zeroProof <- proofConstruction record.units[indexNat]!.theoremName <| match route with
      | .decide => do
          let zeroType <- mkEq uniqueExpr (mkNatLit 0)
          mkDecideProof zeroType
      | .reflected reflected => do
          let fusedUnique <- mkAppM
            `D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.unique
            #[reflected.counts, index]
          let fusedZero <- mkDecideProof (← mkEq fusedUnique (mkNatLit 0))
          let fusedEq <- mkAppM
            `D5.S3.ConceptDynamics.InformationEscape.Catalog.fusedUnique_eq_uniqueCaptureCount
            #[catalog, reflected.witness, reflected.indices, index]
          let actualToFused <- mkAppM ``Eq.symm #[fusedEq]
          mkAppM ``Eq.trans #[actualToFused, fusedZero]
    checkWithKernel zeroProof
    certifiedRedundantIndices := certifiedRedundantIndices.push indexNat
  match validateRedundantIndices record.rootId record.catalogId expectedCounts
      certifiedRedundantIndices "complete-scan" with
  | .ok () => pure ()
  | .error message => throwError message
  match validateCompleteCountVector record.rootId record.catalogId compiledSize
      expectedCounts uniqueCounts with
  | .ok () => pure ()
  | .error message => throwError message
  if let some firstZero := redundantIndices[0]? then
    let members := certifiedRedundantIndices.map fun index =>
      record.units[index]!.theoremName.toString
    logInfo s!"information seal redundancy: root={record.rootId} catalog={record.catalogId} \
counts={natArrayJson uniqueCounts} certified={natArrayJson certifiedRedundantIndices} \
members={(toJson members).compress}"
    let unit := record.units[firstZero]!
    throwError
      "IE-C007 ZeroUniqueCapture: theorem {unit.theoremName} arena {record.arenaName} \
full {fullCount} without {withoutCounts[firstZero]!}"
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
    let uniqueCount := uniqueCounts[indexNat]!
    let withoutCount := withoutCounts[indexNat]!
    let positiveType ← mkLT (mkNatLit 0) uniqueExpr
    let positiveProof ← match route with
      | .decide => proofConstruction theoremName <| mkDecideProof positiveType
      | .reflected reflected => proofConstruction theoremName do
          let fusedUnique ← mkAppM
            `D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.unique
            #[reflected.counts, index]
          let fusedPositiveType ← mkLT (mkNatLit 0) fusedUnique
          let fusedPositiveProof ← mkDecideProof fusedPositiveType
          mkAppM
            `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount_pos_of_fused
            #[catalog, reflected.witness, reflected.indices, index, fusedPositiveProof]
    let mut roleBins := #[]
    let mut roleSignatureHistogram := #[]
    for bucket in [:15] do
      let signatureCount ← match route with
        | .decide =>
            let mask := bucket + 1
            let signatureCountExpr ← mkAppM ``uniqueCaptureSignatureCount
              #[catalog, index,
                mkConst (if signatureBit mask 0 then ``Bool.true else ``Bool.false),
                mkConst (if signatureBit mask 1 then ``Bool.true else ``Bool.false),
                mkConst (if signatureBit mask 2 then ``Bool.true else ``Bool.false),
                mkConst (if signatureBit mask 3 then ``Bool.true else ``Bool.false)]
            natValue signatureCountExpr
        | .reflected reflected =>
            pure (reflected.snapshot.roleBins[indexNat]!)[bucket]!
      roleBins := roleBins.push signatureCount
      if signatureCount != 0 then
        roleSignatureHistogram := roleSignatureHistogram.push
          (signatureLabel (bucket + 1), signatureCount)
    match validateRoleHistogram theoremName uniqueCount roleBins with
    | .ok () => pure ()
    | .error message => throwError message
    let (lowersProof, lowersType) ← proofConstruction theoremName do
      let characterization ← mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos
        #[catalog, index, nondegenerateProof]
      let lowersProof ← mkAppM ``Iff.mpr #[characterization, positiveProof]
      pure (lowersProof, ← inferType lowersProof)
    let lowersName := if record.compatibilityV2 then
      theoremName.str "__lowers_escape"
    else
      catalogQualifiedName record.rootId record.arenaName record.catalogId theoremName
        "__lowers_escape"
    loweringProofNames := loweringProofNames.push lowersName
    declarations := declarations.push <| .thmDecl {
      name := lowersName
      levelParams := []
      type := lowersType
      value := lowersProof
    }
    let theoremExpr := mkConst theoremName
    let theoremType ← inferType theoremExpr
    let enrichedType ← mkAppM ``And #[theoremType, lowersType]
    let enrichedProof := mkAppN (mkConst ``And.intro)
      #[theoremType, lowersType, theoremExpr, mkConst lowersName]
    let enrichedName := if record.compatibilityV2 then
      theoremName.str "__escape_enriched"
    else
      catalogQualifiedName record.rootId record.arenaName record.catalogId theoremName
        "__escape_enriched"
    declarations := declarations.push <| .thmDecl {
      name := enrichedName
      levelParams := []
      type := enrichedType
      value := enrichedProof
    }
    theoremRecords := theoremRecords.push {
      theoremName
      unitName
      realizationName := unit.realizationName
      certificateName := lowersName
      registrationModuleName := unit.registrationModuleName
      index := indexNat
      primitiveCount
      primitiveAxes
      primitiveKernelAddress
      uniqueCaptureCount := uniqueCount
      fullEscapeCount := fullCount
      withoutEscapeCount := withoutCount
      roleSignatureHistogram
      proofMethod := match route with
        | .decide => if record.compatibilityV2 then "decide" else "direct"
        | .reflected _ => "reflected-fused-counts"
    }
  let irredundantProof ← irredundantFromLoweringProofs catalog loweringProofNames
  let irredundantType ← inferType irredundantProof
  let irredundantName := if record.compatibilityV2 then
    record.arenaName.str "__catalog_irredundant"
  else
    catalogQualifiedName record.rootId record.arenaName record.catalogId record.arenaName
      "__catalog_irredundant"
  declarations := declarations.push <| .thmDecl {
    name := irredundantName
    levelParams := []
    type := irredundantType
    value := irredundantProof
  }
  pure (declarations, {
    catalog := record
    irredundantCertificateName := irredundantName
    proofMethod := match route with
      | .decide => if record.compatibilityV2 then "decide" else "direct"
      | .reflected _ => "reflected-fused-counts"
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

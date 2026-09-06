import LeanInformationAudit.AnalysisProjection
import LeanInformationAudit.ProjectionValidation
import LeanInformationAudit.ProjectionReflection

namespace LeanInformationAudit

open Lean Lean.Meta
open D5.S3.ConceptDynamics.InformationEscape

structure KernelProjectionRequest where
  selected : Array (Array Nat) := #[]
  transitions : Array (Array Nat × Nat) := #[]
  schedules : Array (String × Array Nat) := #[]
  complete : Bool := false
  deriving Inhabited

private structure CertifiedProjectionSnapshot where
  rootId : Name
  catalogId : Name
  catalog : Expr
  reflectedCatalog : Expr
  projection : KernelProjectionRecord
  analysis : AnalysisProjectionRecord
  layers : Array LayerChainRow
  propositions : Array (Name × Expr)
  definitions : Array DefinitionVal
  countingMethod : String

private initialize certifiedProjectionExt : SimplePersistentEnvExtension
    CertifiedProjectionSnapshot (Array CertifiedProjectionSnapshot) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

/-- Compare at emission with rows retained by the proof builder, before callers can edit them.
The retained propositions also bind the subsequently staged declarations to that builder run. -/
def validateCertifiedProjection (root catalogId : Name) (catalog : Expr)
    (projection : KernelProjectionRecord) (analysis : AnalysisProjectionRecord)
    (layers : Array LayerChainRow) : MetaM Expr := do
  let key := projection.certificates.find? (·.1 == "readout_reflection")
  let some snapshot := (certifiedProjectionExt.getState (← getEnv)).find? fun snapshot =>
      snapshot.rootId == root && snapshot.catalogId == catalogId &&
      snapshot.projection.certificates.find? (·.1 == "readout_reflection") == key
    | throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=certified-snapshot expected=retained actual=missing"
  unless ← isDefEq catalog snapshot.catalog do
    throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=certified-catalog expected=retained actual=different"
  match validateProjectionSnapshot root catalogId snapshot.projection projection with
  | .error message => throwError message
  | .ok () => pure ()
  unless analysis == snapshot.analysis do
    throwError "IE-C028 AnalysisCertificateMismatch root={root} catalog={catalogId} \
component=analysis expected=certified-snapshot actual=different"
  unless layers == snapshot.layers do
    let chain := layers[0]?.map (·.chainId) |>.getD "missing"
    throwError "IE-C031 InvalidLayerChain root={root} catalog={catalogId} \
chain={chain} layer=0 reason=certified-snapshot-mismatch"
  for (name, expected) in snapshot.propositions do
    let some (.thmInfo info) := (← getEnv).find? name
      | throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=certificate:{name} expected=Lean-theorem actual=missing"
    unless ← isDefEq info.type expected do
      throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=certificate:{name} expected=retained-proposition actual=different"
  for expected in snapshot.definitions do
    let some (.defnInfo actual) := (← getEnv).find? expected.name
      | throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=definition:{expected.name} expected=Lean-definition actual=missing"
    unless actual.levelParams == expected.levelParams && (← isDefEq actual.type expected.type) do
      throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=definition:{expected.name} expected=retained-type actual=different"
    unless ← isDefEq actual.value expected.value do
      throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=definition:{expected.name} expected=retained-value actual=different"
  return snapshot.reflectedCatalog

def validateProjectionCountingRoute (root catalogId : Name) (projection : KernelProjectionRecord)
    (method : String) : MetaM Unit := do
  let key := projection.certificates.find? (·.1 == "readout_reflection")
  let snapshots := certifiedProjectionExt.getState (← getEnv)
  unless snapshots.any (fun entry => entry.rootId == root && entry.catalogId == catalogId &&
      entry.projection.certificates.find? (·.1 == "readout_reflection") == key &&
      entry.countingMethod == method) do
    throwError "IE-C028 AnalysisCertificateMismatch root={root} catalog={catalogId} \
component=proof-method expected=certified-catalog actual=different"

private structure MaterializedKernel where
  selected : Array Nat
  selection : Expr
  node : Expr
  kernelName : Name
  row : ProjectionNode
  deriving Inhabited

private def generated (catalog : Expr) (size : Nat) (selected : Array Nat) : MetaM Expr := do
  mkAppM ``Catalog.generatedKernel #[catalog, ← ProjectionProof.selection size selected]

private def sameNode (first second : Expr) : MetaM Bool := do
  ProjectionProof.truth (← mkEq first second)

private def normalizeSelection (selected : Array Nat) : Array Nat :=
  selected.toList.eraseDups.toArray.qsort (· < ·)

private def subsetOf (left right : Array Nat) : Bool := left.all right.contains

/-- Absorption for conjunction clauses and for their minimal sufficient generator sets. -/
private def absorb (sets : Array (Array Nat)) (candidate : Array Nat) : Array (Array Nat) :=
  if sets.any (subsetOf · candidate) then sets
  else (sets.filter fun other => !subsetOf candidate other).push candidate

private def arenaStates (catalog : Expr) : MetaM (Array Expr) := do
  let arena := (← whnf (← inferType catalog)).appArg!
  let fintype ← mkAppM ``Arena.stateFintype #[arena]
  let states ← mkAppOptM ``Fintype.elems #[some (← mkAppM ``Arena.State #[arena]), some fintype]
  let values ← whnf (← mkAppM ``Finset.val #[states])
  unless values.isAppOfArity ``Quot.mk 3 do throwError "cannot reflect closure states"
  let mut rest := values.getArg! 2
  let mut result := #[]
  repeat
    rest ← whnf rest
    if rest.isAppOf ``List.nil then return result
    unless rest.isAppOfArity ``List.cons 3 do throwError "cannot reflect closure state list"
    result := result.push (rest.getArg! 1)
    rest := rest.getArg! 2

/-- Derive exact representatives from separation clauses, after quotienting equal generators.
No subset traversal occurs here. Essential generators close independent targets immediately.
Otherwise, conjunction and absorption derive the antichain of minimal sufficient sets; its
least cardinality/Name member is canonical. This antichain can be exponentially large for
genuinely redundant catalogs: no polynomial completion claim or new search cap is made.
The only availability bounds are the caller's Lean maxHeartbeats/maxRecDepth options; resource
failure is IE-C042 at materialization, never a truncated certificate or partial artifact.
Only prepareKernelProjection's explicit complete=true branch enumerates all subsets. The
second result retains the subset-visit metric and is zero for this closure algorithm. -/
def canonicalSelectionWork (catalog : Expr) (members : Array Name) (selected : Array Nat)
    (_complete : Bool := false) : MetaM (Array Nat × Nat) := do
  let size := members.size
  let selected := normalizeSelection selected
  let target ← generated catalog size selected
  let mut eligible := #[]
  for index in (Array.range size).qsort (fun i j => members[i]!.toString < members[j]!.toString) do
    let singleton ← generated catalog size #[index]
    if ← ProjectionProof.truth (← mkLE target singleton) then
      unless ← eligible.anyM (fun other => do
          sameNode singleton (← generated catalog size #[other])) do
        eligible := eligible.push index
  let mut forced := #[]
  for index in eligible do
    unless ← sameNode target (← generated catalog size (eligible.filter (· != index))) do
      forced := forced.push index
  if ← sameNode target (← generated catalog size forced) then return (forced, 0)
  let states ← arenaStates catalog
  let singletons ← eligible.mapM fun index => generated catalog size #[index]
  let mut clauses := #[]
  for x in states do
    for y in states do
      let related : Bool ← reduceEval (← mkAppM ``Catalog.GeneratedKernel.relationB #[target, x, y])
      if related then continue
      let mut clause := #[]
      for index in eligible, singleton in singletons do
        let agrees : Bool ← reduceEval
          (← mkAppM ``Catalog.GeneratedKernel.relationB #[singleton, x, y])
        unless agrees do clause := clause.push index
      if clause.isEmpty then throwError "generated relation has no separation clause"
      clauses := absorb clauses clause
  let mut sufficient := #[forced]
  for clause in clauses.qsort (fun a b => a.size < b.size) do
    let mut next := #[]
    for candidate in sufficient do
      if clause.any candidate.contains then next := absorb next candidate
      else
        for index in clause do
          let extended := candidate.push index
          if extended.size ≤ selected.size then next := absorb next extended
    sufficient := next
  let ordered := sufficient.map (fun indices =>
    indices.qsort (fun i j => members[i]!.toString < members[j]!.toString))
  let ordered := ordered.qsort fun a b => a.size < b.size ||
    (a.size == b.size && compare (a.toList.map (members[·]!.toString))
      (b.toList.map (members[·]!.toString)) == .lt)
  let some result := ordered[0]? | throwError "generated relation has no representative"
  unless ← sameNode target (← generated catalog size result) do
    throwError "closure representative failed relation equality"
  return (result, 0)

private def canonicalSelection (catalog : Expr) (members : Array Name) (selected : Array Nat)
    (complete : Bool) (root catalogId : Name) : MetaM (Array Nat) := do
  try
    return (← canonicalSelectionWork catalog members selected complete).1
  catch error =>
    let options ← getOptions
    throwError "IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalogId} \
component=representative-closure expected=exact actual=unavailable \
maxHeartbeats={Core.getMaxHeartbeats options} maxRecDepth={maxRecDepth.get options} \
reason={error.toMessageData}"

private def kernelIndex (kernels : Array MaterializedKernel) (node : Expr) : MetaM Nat := do
  for i in [:kernels.size] do
    if ← sameNode kernels[i]!.node node then return i
  throwError "required generated relation was not materialized"

private def selectionKey (selected : Array Nat) : String :=
  "K_" ++ String.intercalate "_" (selected.toList.map toString)

private def materialize (catalog : Expr) (members : Array Name) (certPrefix : Name)
    (required : Array (Array Nat)) (complete : Bool) (root catalogId : Name) :
    ProjectionM (Array MaterializedKernel) := do
  let mut kernels := #[]
  for selected in required do
    let requestedNode ← generated catalog members.size selected
    if ← kernels.anyM (fun other => sameNode other.node requestedNode) then continue
    let selected ← canonicalSelection catalog members selected complete root catalogId
    let selection ← ProjectionProof.selection members.size selected
    let node ← mkAppM ``Catalog.generatedKernel #[catalog, selection]
    let key := selectionKey selected
    let kernelName ← ProjectionProof.value (certPrefix.str key) node
    let escape ← mkAppM ``Catalog.GeneratedKernel.escapeCount #[node]
    let escapeCount : Nat ← reduceEval escape
    let relationProof ← mkDecideProof (← mkEq requestedNode node)
    let cardinalityProof ← mkDecideProof (← mkEq
      (← mkAppM ``Finset.card #[selection]) (mkNatLit selected.size))
    let countProof ← mkDecideProof (← mkEq escape (mkNatLit escapeCount))
    let relationCertificate ← ProjectionProof.proof (certPrefix.str (key ++ "_relation"))
      (← ProjectionProof.conjunction #[relationProof, cardinalityProof, countProof])
    kernels := kernels.push {
      selected, selection, node, kernelName,
      row := { key := key, generators := selected.map (members[·]!), escapeCount, relationCertificate } }
  pure (kernels.qsort fun a b => a.kernelName.toString < b.kernelName.toString)

private def prepareEdges (catalog : Expr) (members : Array Name) (certPrefix : Name)
    (kernels : Array MaterializedKernel) (reflected : ProjectionProof.CheckedRefinement) :
    ProjectionM (Array ProjectionEdge × Array CollapsedAddition) := do
  let mut edges := #[]
  let mut collapsed := #[]
  for sourceIndex in [:kernels.size] do
    let source := kernels[sourceIndex]!
    for i in [:members.size] do
      let added ← ProjectionProof.fin i members.size
      let selection ← ProjectionProof.selection members.size
        (normalizeSelection (source.selected.push i))
      let targetNode ← mkAppM ``Catalog.generatedKernel #[catalog, selection]
      let mut found := none
      for j in [:kernels.size] do
        if ← sameNode targetNode kernels[j]!.node then found := some j
      let some j := found | continue
      let target := kernels[j]!
      let step ← mkAppM ``projection_generator_step #[catalog, source.selection, added]
      let inserted ← mkAppM ``Insert.insert #[added, source.selection]
      let insertedNode ← mkAppM ``Catalog.generatedKernel #[catalog, inserted]
      let targetEquality ← mkDecideProof (← mkEq insertedNode target.node)
      let suffix := source.row.key ++ s!"_add_{i}"
      if source.row.key == target.row.key then
        let equalityCertificate ← ProjectionProof.proof (certPrefix.str suffix)
          (← ProjectionProof.conjunction #[step, targetEquality])
        collapsed := collapsed.push {
          atNode := source.row.key, theoremName := members[i]!, equalityCertificate }
      else
        let targetIndex ← ProjectionProof.fin j kernels.size
        let sourceIndex ← ProjectionProof.fin sourceIndex kernels.size
        let forward ← mkDecideProof (← mkEq
          (mkApp2 reflected.table targetIndex sourceIndex) (mkConst ``Bool.true))
        let reverse ← mkDecideProof (← mkEq
          (mkApp2 reflected.table sourceIndex targetIndex) (mkConst ``Bool.false))
        let strict ← mkAppM ``reflectedStrict_sound
          #[reflected.nodes, reflected.table, reflected.checked, targetIndex, sourceIndex,
            forward, reverse]
        let test ← mkAppM ``projectionCover #[catalog, source.selection, target.node]
        let isCover ← ProjectionProof.truth test
        let equivalence ← mkAppM ``projection_cover_iff #[catalog, source.selection, target.node]
        let coverProof ← if isCover then
          mkAppM ``Iff.mp #[equivalence, ← mkDecideProof test]
        else
          mkAppM ``Iff.mp #[← mkAppM ``not_congr #[equivalence],
            ← mkDecideProof (← mkAppM ``Not #[test])]
        let captureCount := source.row.escapeCount - target.row.escapeCount
        let reduction ← mkAppM ``projectionEdgeCount_eq
          #[source.node, target.node, ← mkAppM ``le_of_lt #[strict]]
        let reduced := (← inferType reduction).eq?.get!.2.2
        let countProof ← mkAppM ``Eq.trans
          #[reduction, ← mkDecideProof (← mkEq reduced (mkNatLit captureCount))]
        let certificate ← ProjectionProof.proof (certPrefix.str suffix)
          (← ProjectionProof.conjunction #[step, targetEquality, strict, coverProof, countProof])
        edges := edges.push {
          source := source.row.key, target := target.row.key,
          theoremName := members[i]!, isCover, captureCount, certificate }
  pure (edges, collapsed)

private def prepareSchedule (catalog : Expr) (members : Array Name) (certPrefix : Name)
    (kernels : Array MaterializedKernel) (edges : Array ProjectionEdge)
    (collapsed : Array CollapsedAddition) (chainId : String) (order : Array Nat) :
    ProjectionM (CertifiedScheduleRow × LayerChainRow) := do
  let orderExpr ← ProjectionProof.vector
    (← order.mapM fun i => ProjectionProof.fin i members.size)
  let bijective ← mkAppM ``Function.Bijective #[orderExpr]
  let schedule ← mkAppM ``projectionSchedule #[catalog, orderExpr, ← mkDecideProof bijective]
  let _ ← ProjectionProof.value (certPrefix.str "schedule") schedule
  let mut nodes := #[]
  let mut stepClasses := #[]
  let mut increments := #[]
  let mut stepCertificates := #[]
  let mut partitionProofs := #[]
  for i in [:order.size + 1] do
    let current ← mkAppM ``GeneratorSchedule.node
      #[schedule, ← ProjectionProof.fin i (order.size + 1)]
    let index ← kernelIndex kernels current
    partitionProofs := partitionProofs.push (← mkDecideProof (← mkEq current kernels[index]!.node))
    nodes := nodes.push kernels[index]!.row.key
    if i > 0 then
      let source := nodes[i - 1]!
      let target := nodes[i]!
      let theoremName := members[order[i - 1]!]!
      let expression ← mkAppM ``GeneratorSchedule.incrementCount
        #[schedule, ← ProjectionProof.fin (i - 1) order.size]
      let (count, _) ← ProjectionProof.count (certPrefix.str s!"increment_{i - 1}") expression
      let reduced ← mkAppM ``projectionIncrementCount_eq
        #[schedule, ← ProjectionProof.fin (i - 1) order.size]
      let value := (← inferType reduced).eq?.get!.2.2
      partitionProofs := partitionProofs.push (← mkAppM ``Eq.trans
        #[reduced, ← mkDecideProof (← mkEq value (mkNatLit count))])
      increments := increments.push count
      if source == target then
        stepClasses := stepClasses.push "collapsed"
        let some row := collapsed.find? fun row =>
          row.atNode == source && row.theoremName == theoremName
          | throwError "missing certified collapsed schedule step"
        stepCertificates := stepCertificates.push row.equalityCertificate
      else
        stepClasses := stepClasses.push "strict"
        let some row := edges.find? fun row => row.source == source && row.target == target &&
            row.theoremName == theoremName
          | throwError "missing certified strict schedule step"
        stepCertificates := stepCertificates.push row.certificate
  let layer ← prepareLayerProjection schedule chainId (certPrefix.str "layers")
  let terminal ← mkAppM ``GeneratorSchedule.node
    #[schedule, ← ProjectionProof.fin order.size (order.size + 1)]
  partitionProofs := partitionProofs.push (← mkDecideProof (← mkEq
    (← mkAppM ``Catalog.GeneratedKernel.escapeCount #[terminal])
    (mkNatLit layer.unresolved.count)))
  for theoremName in #[``chain_increment_pairwise_disjoint, ``chain_increment_union,
      ``chain_count_telescopes] do
    partitionProofs := partitionProofs.push (← mkAppM theoremName #[schedule])
  partitionProofs := partitionProofs.push
    (← mkAppM ``schedule_terminal_eq_generatedKernel_full #[schedule])
  let partitionCertificate ← ProjectionProof.proof (certPrefix.str "partition")
    (← ProjectionProof.conjunction partitionProofs)
  pure ({
    chainId, nodes, generators := order.map (members[·]!), stepClasses, increments,
    stepCertificates, terminalEscapeCount := layer.unresolved.count, partitionCertificate }, layer)

def prepareKernelProjection (catalog arena : Expr) (members : Array Name)
    (rootId catalogId arenaName certPrefix : Name) (request : KernelProjectionRequest := {}) :
    ProjectionM (KernelProjectionRecord × AnalysisProjectionRecord × Array LayerChainRow) :=
    withTransparency .all do
  let originalCatalog ← instantiateMVars catalog
  let size := members.size
  let (catalog, readoutEquality) ← ProjectionProof.reflectCatalog catalog size
  let readoutCertificate ← ProjectionProof.proof (certPrefix.str "readout_reflection") readoutEquality
  let full := Array.range size
  let canonicalOrder := full.qsort fun i j => members[i]!.toString < members[j]!.toString
  let schedules := if request.schedules.isEmpty then #[ ("canonical", canonicalOrder) ]
    else request.schedules.qsort fun a b => a.1 < b.1
  for (chainId, order) in schedules do
    unless order.qsort (· < ·) == full do
      throwError "IE-C031 InvalidLayerChain root={rootId} catalog={catalogId} \
chain={chainId} layer=0 reason=not-a-complete-ordering"
  let mut required := #[#[], full] ++ full.map (fun i => full.filter (· != i)) ++ request.selected
  for (selected, added) in request.transitions do
    required := required.push selected |>.push (normalizeSelection (selected.push added))
  for (_, order) in schedules do
    for i in [:order.size + 1] do required := required.push (order.extract 0 i)
  if request.complete then
    let mut selections : Array (Array Nat) := #[#[]]
    for i in full do selections := selections ++ selections.map (·.push i)
    required := required ++ selections
  for selected in required do
    unless selected.all (· < size) do
      throwError "IE-C039 InvalidGeneratedKernelNode root={rootId} catalog={catalogId} \
node=request reason=invalid-generator-index"
  let enum ← ProjectionProof.enumeration arena arenaName
  let kernels ← materialize catalog members certPrefix required request.complete rootId catalogId
  let reflected ← ProjectionProof.reflectRefinement
    (← ProjectionProof.vector (kernels.map (·.node))) (certPrefix.str "refinement")
  let (edges, collapsedAdditions) ← prepareEdges catalog members certPrefix kernels reflected
  let analysis ← prepareAnalysisProjection catalog enum members (certPrefix.str "analysis")
  let selections ← ProjectionProof.vector (kernels.map (·.selection))
  let mut completenessCertificates := #[]
  if request.complete then
    let certificate ← ProjectionProof.decide (certPrefix.str "complete")
      (← mkAppM ``projectionComplete #[catalog, selections])
    completenessCertificates := #[("complete", certificate)]
  let nodeCatalog ← mkAppM ``projectionNodeCatalog #[catalog, selections]
  let (overlapMatrix, refinementMatrix, _, nodeCertificates) ←
    prepareMatrices nodeCatalog enum (kernels.map (·.kernelName)) (certPrefix.str "nodes")
  let mut leaveOneOut := #[]
  let mut redundantIndices := #[]
  for i in [:size] do
    let index ← ProjectionProof.fin i size
    let without ← mkAppM ``Catalog.without #[catalog, index]
    let withoutNode ← mkAppM ``Catalog.generatedKernel #[catalog, without]
    let node := kernels[← kernelIndex kernels withoutNode]!
    let relationProof ← mkDecideProof (← mkEq withoutNode node.node)
    let equality ← mkAppM ``projectionLeaveOneOut_eq #[catalog, index, node.node, relationProof]
    let countExpr ← mkAppM ``Catalog.uniqueCaptureCount #[catalog, index]
    let uniqueCaptureCount : Nat ← reduceEval countExpr
    let countProof ← mkDecideProof (← mkEq countExpr (mkNatLit uniqueCaptureCount))
    let certificate ← ProjectionProof.proof (certPrefix.str s!"leave_one_out_{i}")
      (← ProjectionProof.conjunction #[relationProof, equality, countProof])
    leaveOneOut := leaveOneOut.push {
      theoremName := members[i]!, node := node.row.key,
      uniqueCaptureCount, certificate }
    if uniqueCaptureCount == 0 then redundantIndices := redundantIndices.push members[i]!
  let mut certifiedChains := #[]
  let mut layers := #[]
  for (chainId, order) in schedules do
    let (chain, layer) ← prepareSchedule catalog members (certPrefix.str chainId)
      kernels edges collapsedAdditions chainId order
    certifiedChains := certifiedChains.push chain
    layers := layers.push layer
  let (denominator, denominatorCertificate) ← ProjectionProof.count
    (certPrefix.str "denominator") (← mkAppM ``escapeDenominator #[arena])
  let verdict := if redundantIndices.isEmpty then "irredundant" else "redundant"
  let verdictProp ← mkAppM
    (if redundantIndices.isEmpty then ``CatalogIrredundant else ``Catalog.CatalogRedundant)
    #[catalog]
  let verdictCertificate ← ProjectionProof.decide (certPrefix.str "verdict") verdictProp
  let projection : KernelProjectionRecord := {
    completeLatticeMaterialized := request.complete, nodes := kernels.map (·.row),
    edges, collapsedAdditions, leaveOneOut, certifiedChains, refinementMatrix, overlapMatrix,
    multiplicitySpectrum := analysis.spectrum, redundantIndices, verdict, denominator,
    certificates := analysis.certificates ++
      nodeCertificates.map (fun (key, name) => ("node_" ++ key, name)) ++ completenessCertificates ++
      #[("denominator", denominatorCertificate), ("verdict", verdictCertificate),
        ("readout_reflection", readoutCertificate),
        ("reflected_refinement", reflected.certificate)] }
  match projection.validateReferences rootId catalogId with
  | .error message => throwError message
  | .ok () => pure ()
  let canonical := projection.canonical
  let propositions := (← get).filterMap fun declaration => match declaration with
    | .thmDecl info => some (info.name, info.type)
    | _ => none
  let definitions := (← get).filterMap fun declaration => match declaration with
    | .defnDecl info => some info
    | _ => none
  modifyEnv fun env => certifiedProjectionExt.addEntry env {
    rootId, catalogId, catalog := originalCatalog, reflectedCatalog := catalog, projection := canonical,
    analysis, layers, propositions, definitions, countingMethod := "reflected-readout" }
  pure (canonical, analysis, layers)

end LeanInformationAudit

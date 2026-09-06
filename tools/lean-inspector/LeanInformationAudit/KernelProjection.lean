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
  return snapshot.reflectedCatalog

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

private partial def firstRepresentative (catalog target : Expr) (size : Nat)
    (eligible : Array Nat) (remaining start : Nat) (chosen : Array Nat) (limit : Option Nat) :
    StateRefT Nat MetaM (Option (Array Nat)) := do
  if let some limit := limit then
    if (← get) >= limit then
      throwError "bounded canonical representative search exhausted; request complete=true"
  modify (· + 1)
  if remaining == 0 then
    return if ← sameNode target (← generated catalog size chosen) then some chosen else none
  if eligible.size - start < remaining then return none
  unless ← sameNode target (← generated catalog size (chosen ++ eligible.extract start eligible.size)) do
    return none
  for position in [start:eligible.size] do
    if let some result ← firstRepresentative catalog target size eligible (remaining - 1)
        (position + 1) (chosen.push eligible[position]!) limit then return some result
  pure none

/-- Exact minimum representatives with a polynomial search-work cap in bounded mode.
Exhaustion fails closed; only explicit complete mode permits unrestricted subset search. -/
def canonicalSelectionWork (catalog : Expr) (members : Array Name) (selected : Array Nat)
    (complete : Bool := false) :
    MetaM (Array Nat × Nat) := (do
  let size := members.size
  let selected := normalizeSelection selected
  let target ← generated catalog size selected
  let mut eligible := #[]
  for index in [:size] do
    let singleton ← generated catalog size #[index]
    if ← ProjectionProof.truth (← mkLE target singleton) then eligible := eligible.push index
  eligible := eligible.qsort fun i j => members[i]!.toString < members[j]!.toString
  let mut forced := #[]
  for index in eligible do
    unless ← sameNode target (← generated catalog size (eligible.filter (· != index))) do
      forced := forced.push index
  if ← sameNode target (← generated catalog size forced) then return forced
  let optional := eligible.filter (!forced.contains ·)
  let limit := if complete then none else some ((size + 1) ^ 3)
  for count in [1:selected.size - forced.size + 1] do
    if let some representative ← firstRepresentative catalog target size optional count 0 forced limit then
      return representative.qsort fun i j => members[i]!.toString < members[j]!.toString
  throwError "generated relation has no representative" : StateRefT Nat MetaM _).run 0

private def canonicalSelection (catalog : Expr) (members : Array Name) (selected : Array Nat)
    (complete : Bool) : MetaM (Array Nat) :=
  return (← canonicalSelectionWork catalog members selected complete).1

private def kernelIndex (kernels : Array MaterializedKernel) (node : Expr) : MetaM Nat := do
  for i in [:kernels.size] do
    if ← sameNode kernels[i]!.node node then return i
  throwError "required generated relation was not materialized"

private def selectionKey (selected : Array Nat) : String :=
  "K_" ++ String.intercalate "_" (selected.toList.map toString)

private def materialize (catalog : Expr) (members : Array Name) (certPrefix : Name)
    (required : Array (Array Nat)) (complete : Bool) : ProjectionM (Array MaterializedKernel) := do
  let mut kernels := #[]
  for selected in required do
    let requestedNode ← generated catalog members.size selected
    let selected ← canonicalSelection catalog members selected complete
    let selection ← ProjectionProof.selection members.size selected
    let node ← mkAppM ``Catalog.generatedKernel #[catalog, selection]
    if ← kernels.anyM (fun other => sameNode other.node node) then continue
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
  let kernels ← materialize catalog members certPrefix required request.complete
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
  modifyEnv fun env => certifiedProjectionExt.addEntry env {
    rootId, catalogId, catalog := originalCatalog, reflectedCatalog := catalog, projection := canonical,
    analysis, layers, propositions }
  pure (canonical, analysis, layers)

end LeanInformationAudit

import LeanInformationAudit.Census.Stream
import LeanInformationAudit.DispositionCensus

namespace LeanInformationAudit.CensusQuery

open Lean Meta DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

/-- The closure is read from imported module headers; missing modules are errors. -/
def importClosure (env : Environment) (root : Name) : MetaM (Array Name) := do
  let mut visited : Std.HashSet Name := {}
  let mut pending := [root]
  let mut modules := #[]
  repeat
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if visited.contains name then continue
      visited := visited.insert name
      let imports ← if name == env.header.mainModule then pure env.header.imports else do
        let some index := env.getModuleIdx? name
          | throwError "census query: existing-module required: {name}"
        pure env.header.moduleData[index.toNat]!.imports
      modules := modules.push name
      pending := imports.toList.map (·.module) ++ pending
  return modules.qsort Name.quickLt

def owningModule (env : Environment) (name : Name) : Name :=
  (env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!)
    |>.getD env.header.mainModule

structure Index where
  root : Name
  modules : Array Name
  finite : Array InformationRegistryEntry
  structural : Array StructuralProvenanceEntry
  named : Std.HashMap Name (Array Name)

/-- Fixture and elaborator queries enumerate ModuleData membership, including
the current source's staged declarations. Production supplies the detached
streamed index to the same assess function. -/
def indexScope (root : Name) : MetaM Index := do
  let env ← getEnv
  let modules ← importClosure env root
  let members : Std.HashSet Name := Std.HashSet.ofArray modules
  let mut named : Std.HashMap Name (Array Name) := {}
  for moduleName in modules do
    let data ← if moduleName == env.header.mainModule then mkModuleData env else do
      let some index := env.getModuleIdx? moduleName
        | throwError "census query: existing-module required: {moduleName}"
      pure env.header.moduleData[index.toNat]!
    for info in data.constants do
      if let some head := CensusStream.indexedHead info then
        named := named.insert head ((named.getD head #[]).push info.name)
  for head in CensusStream.evidenceTypes.push CensusStream.approximationHead do
    named := named.insert head ((named.getD head #[]).toList.eraseDups.toArray.qsort Name.quickLt)
  return {
    root, modules, named
    finite := (InformationRegistry.entries env).filter
      (fun entry => members.contains entry.registrationModuleName)
      |>.qsort (fun a b => Name.quickLt a.unitName b.unitName)
    structural := (structuralProvenanceEntries env).filter
      (fun entry => members.contains entry.registrationModule)
      |>.qsort (fun a b => Name.quickLt a.unitConst b.unitConst) }

private def matching (index : Index) (head : Name) (expected : Expr) : MetaM (Array Name) := do
  let mut result := #[]
  for name in index.named.getD head #[] do
    let matched ← withNewMCtxDepth do
      isDefEq (← inferType (← mkConstWithFreshMVarLevels name)) expected
    if matched then result := result.push name
  return result

private def certified (index : Index) (head : String) (key : StatementKey)
    (value : AnalysisDisposition key) : MetaM (CensusAssessment key) := do
  validateEvidence index.root ⟨head, #[⟨key, .certified value⟩]⟩ (some index.modules)
  return .certified value

/-- Exhaustive within the declared query domain, never a mathematical classifier.
Absence of the required named certificates leaves a diagnostic observation;
errors from discovery or validation are propagated and never become observations. -/
def assess (index : Index) (head : String) (key : StatementKey)
    (recordedOwner : Option Name := none) : MetaM (CensusAssessment key) := do
  let env ← getEnv
  let owner := recordedOwner.getD (owningModule env key.theoremName)
  unless ← CensusOwnership.recordedModuleContainsTheorem env index.modules owner key.theoremName do
    throwError "census query: theorem outside declared import scope: {key.theoremName}"
  let statement ← inferType (← mkConstWithFreshMVarLevels key.theoremName)
  let mut candidates := #[]
  let mut dispositions : Array (AnalysisDisposition key) := #[]
  for entry in index.finite do
    if entry.theoremName != key.theoremName then continue
    candidates := candidates ++ #[entry.unitName, entry.realizationName]
    let arena ← mkAppM ``PrimitiveLawArena.toArena #[← mkConstWithFreshMVarLevels entry.arenaName]
    let nondegenerate ← matching index ``Arena.Nondegenerate
      (← mkAppM ``Arena.Nondegenerate #[arena])
    let enumerations ← matching index ``Arena.StateEnumeration
      (← mkAppM ``Arena.StateEnumeration #[arena])
    if (finiteSealInScope? env index.modules key.theoremName
        entry.canonicalObjectArenaName).isSome then
      if let (some proof, some enumeration) := (nondegenerate[0]?, enumerations[0]?) then
        dispositions := dispositions.push <| .finiteOccurrence {
          canonicalArena := entry.canonicalObjectArenaName
          registration := entry.unitName
          «realization» := entry.realizationName
          nondegeneracyCertificate := proof
          stateEnumerationCertificate := enumeration }
  for entry in index.structural do
    if entry.theoremName == key.theoremName then
      candidates := candidates ++ #[entry.unitConst, entry.realizationConst]
  for name in index.named.getD ``StructuralRegistrationEvidence #[] do
    let type ← inferType (← mkConstWithFreshMVarLevels name)
    let args := type.getAppArgs
    let registered : Name ← reduceEval args[0]!
    if registered != key.theoremName then continue
    candidates := candidates.push name
    let some provenance := index.structural.find? (·.theoremName == key.theoremName)
      | continue
    let strictness ← matching index ``StructuralCatalog.StructurallyLowersEscape
      (← mkAppM ``StructuralCatalog.StructurallyLowersEscape #[args[3]!, args[4]!])
    let witnesses ← matching index ``StructuralStrictnessCertificate
      (← mkAppM ``StructuralStrictnessCertificate #[args[3]!, args[4]!])
    if let (some proof, some witness) := (strictness[0]?, witnesses[0]?) then
      dispositions := dispositions.push <| .structuralOccurrence {
        canonicalArena := provenance.canonicalArena, registration := name
        «realization» := provenance.realizationConst
        strictnessCertificate := proof, witnessCertificate := witness }
  for evidenceHead in [``BoundedTruncationFamily, ``UnreachableElaborationEvidence] do
    for name in index.named.getD evidenceHead #[] do
      let value ← mkConstWithFreshMVarLevels name
      let type ← inferType value
      unless ← withNewMCtxDepth (isDefEq type.getAppArgs[0]! statement) do continue
      if evidenceHead == ``UnreachableElaborationEvidence then
        let evidence ← whnf value
        if evidence.isAppOfArity ``UnreachableElaborationEvidence.mk 5 then
          let obligation ← whnf evidence.getAppArgs[4]!
          if obligation.isAppOfArity ``Option.some 2 then
            let obligationName : Name ← reduceEval obligation.getAppArgs[1]!
            if ← CensusOwnership.nameInScope env index.modules obligationName then
              let obligationType := (← getConstInfo obligationName).type
              if [``ClosedNumericalObligation, ``InfinitePrimitiveObligation,
                  ``UnfaithfulPrimitiveObligation].contains
                    (obligationType.getAppFn.constName?.getD .anonymous) then
                let recorded : Name ← reduceEval obligationType.getAppArgs[0]!
                if recorded != key.theoremName then continue
        candidates := candidates.push name
        let reasonExpr ← whnf (← mkAppM ``UnreachableElaborationEvidence.reason #[value])
        let reason ← match reasonExpr.constName? with
          | some ``UnreachableReason.noCanonicalObjectCarrier => pure UnreachableReason.noCanonicalObjectCarrier
          | some ``UnreachableReason.noFinitePrimitiveBundle => pure UnreachableReason.noFinitePrimitiveBundle
          | some ``UnreachableReason.noFaithfulPrimitiveRealization => pure UnreachableReason.noFaithfulPrimitiveRealization
          | _ => throwError "census query: invalid unreachable reason"
        dispositions := dispositions.push (.unreachable ⟨reason, name⟩)
      else
        candidates := candidates.push name
        for comparison in index.named.getD ``BoundedTruncationFamily.approximation #[] do
          let comparisonType ← inferType (← mkConstWithFreshMVarLevels comparison)
          let .forallE _ _ conclusion _ := comparisonType | continue
          unless conclusion.getAppArgs[1]!.isConstOf name do continue
          let some bound := (← whnf conclusion.getAppArgs[2]!).rawNatLit? | continue
          let approximation ← mkAppM ``BoundedTruncationFamily.approximation #[value, mkNatLit bound]
          unless ← withNewMCtxDepth (isDefEq comparisonType (← mkArrow statement approximation)) do continue
          dispositions := dispositions.push <| .boundedFiniteTruncation {
            truncationFamily := name, bound, comparisonStatement := comparison, certification := .reportOnly }
  for evidenceHead in [``AnalysisDisposition, ``CensusAssessment] do
    for name in index.named.getD evidenceHead #[] do
      let value ← mkConstWithFreshMVarLevels name
      let type ← inferType value
      let recorded : StatementKey ← do
        unsafe evalExpr StatementKey (mkConst ``StatementKey) type.getAppArgs[0]!
      if recorded != key then continue
      candidates := candidates.push name
      if evidenceHead == ``AnalysisDisposition then
        let row ← do unsafe evalExpr (AnalysisDisposition key) type value
        dispositions := dispositions.push row
      else
        let row ← do unsafe evalExpr (CensusAssessment key) type value
        if let .certified row := row then dispositions := dispositions.push row
  -- Validate every discovered disposition, including alternatives to the chosen row.
  for value in dispositions do discard <| certified index head key value
  if let some value := dispositions[0]? then return .certified value
  return .observed {
    owningModule := owner
    root := index.root
    importScope := ⟨index.modules, true⟩
    queryCompleted := true
    candidates := candidates.toList.eraseDups.toArray.qsort Name.quickLt
    note := "Exhaustive query completed within this import scope and the supported syntactic named-evidence domain; no complete evidence found in that domain." }

end LeanInformationAudit.CensusQuery

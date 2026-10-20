import LeanInformationAuditRegAnalysis.SearchReduction.Runner
import LeanInformationAudit.Contract.FibApplications
import LeanInformationAudit.ArtifactAssessment

/-! Binding of optional law evidence to the current ordinary registration.
All decisions use compiled terms and typed assessor results, never report JSON. -/
namespace LeanInformationAudit.SearchReduction
open Lean CompiledSourceScope

private abbrev sourceHead := `LeanInformationAudit.Analysis.Source.ofRegistration
private abbrev familyHead := `LeanInformationAudit.AuricFib.Contract.LawFamily

/-- Select the original field term using the compiler's record layout. -/
private def rawField (name : Name) (record : Expr) : FibSource.M Expr := do
  let some projection := (← read).provenance.view.getProjectionFnInfo? name
    | FibSource.fail "record_field_unknown"
  let fields ← FibSource.fields projection.ctorName record
  let some field := fields[projection.i]? | FibSource.fail "record_field_layout_unknown"
  return field

/-- Unfold data aliases while preserving the required constructor provenance. -/
private partial def registeredSource (term : Expr) (fuel : Nat := 256) : FibSource.M Expr := do
  debit
  if fuel == 0 then FibSource.fail "source_registration_shape_unknown"
  let term := term.consumeMData
  if term.getAppFn.constName? == some sourceHead then return term
  if let .letE _ _ value body _ := term then
    return ← registeredSource (body.instantiate1 value) (fuel - 1)
  let head := term.getAppFn
  if head.isLambda then return ← registeredSource (head.beta term.getAppArgs) (fuel - 1)
  if let some name := head.constName? then
    if let .defnInfo info ← getConstInfo name then
      unless info.safety == .safe && !(← read).recursive name &&
          !(← read).implementedBy name && !(← read).extern name do
        FibSource.fail "source_registration_shape_unknown"
      return ← registeredSource
        ((info.value.instantiateLevelParams info.levelParams head.constLevels!).beta term.getAppArgs)
        (fuel - 1)
  FibSource.fail "source_not_registered"

/-- Follow only compiled dependency branches which can reach a supplied S.
The per-request source-work bound covers this traversal as well. -/
private def disjoint (terms : Array Expr) (structures : Array Name) : FibSource.M Unit := do
  if structures.isEmpty then return
  let mut pending := terms.toList
  let mut seen : NameSet := {}
  let indices ← structures.mapM fun n => do
    let owner ← ownerOf n
    let some index := (← read).moduleIndex? owner
      | FibSource.fail "structure_owner_unknown"
    pure index
  let earliest := indices.foldl min indices[0]!
  while let term :: rest := pending do
    pending := rest
    debit
    for name in term.getUsedConstants do
      if structures.contains name then FibSource.fail s!"law_vocabulary_intersects_S:{name}"
      if seen.contains name then continue
      seen := seen.insert name
      let owner ← ownerOf name
      let some index := (← read).moduleIndex? owner
        | FibSource.fail "law_dependency_owner_unknown"
      if index < earliest then continue
      let info ← getConstInfo name
      pending := info.type :: pending
      if let some value := info.value? (allowOpaque := true) then pending := value :: pending

private def readFace (store : RawArtifacts.Store) (state : ArtifactRegistration.State)
    (target : Name) (structures : Array Name) (application : ConstantInfo) :
    FibSource.M InformationReading := do
  let .defnInfo definition := application | FibSource.fail "application_not_safe_definition"
  unless definition.safety == .safe do FibSource.fail "application_not_safe_definition"
  unless application.levelParams.isEmpty && application.type.isAppOfArity
      `LeanInformationAudit.AuricFib.Contract.Application 2 do
    FibSource.fail "application_shape_unknown"
  let occurrence := application.type.getAppArgs[1]!
  unless occurrence.isConst && occurrence.constName! == target do
    FibSource.fail "target_occurrence_mismatch"
  let some original := store.constants.find? target | FibSource.fail "target_missing"
  unless occurrence.constLevels! == original.levelParams.map Level.param &&
      application.type.getAppArgs[0]!.equal original.type do
    FibSource.fail "target_occurrence_mismatch"
  let applicationFields ← FibSource.fields
    `LeanInformationAudit.AuricFib.Contract.Application.mk definition.value
  let evidence ← FibSource.constructorHead applicationFields[0]!
  unless evidence.getAppFn.constName? == some
      `LeanInformationAudit.AuricFib.Contract.Evidence.law do
    FibSource.fail "evidence_not_law"
  let fs ← FibSource.fields `LeanInformationAudit.AuricFib.Contract.Evidence.law evidence
  let clientFields ← FibSource.fields `LeanInformationAudit.Analysis.Client.mk fs[0]!
  let source ← registeredSource clientFields[0]!
  let args := source.getAppArgs
  unless args.size == 6 && args[1]!.equal occurrence do
    FibSource.fail "source_registration_shape_unknown"
  let registration := args[3]!
  let mut matched : Option BindingRecord := none
  for record in state.records do
    unless record.occurrence.key.theoremName == target do continue
    if let .declaredValidated _ := record.result then
      let name := record.occurrence.realizationName
      let info ← getConstInfo name
      let reference := mkConst name (info.levelParams.map Level.param)
      if registration.consumeMData.equal reference then matched := some record
  let some record := matched | FibSource.fail "registration_not_DTR_Declared"
  let selected ← FibSource.selection clientFields[0]!
  let some claim := state.claims.find? (fun row => row.2.key == record.occurrence.key)
    | FibSource.fail "registration_selection_missing"
  unless claim.2.escapeInput.sourceSelection == some selected do
    FibSource.fail "registration_selection_mismatch"
  let bound ← FibSource.bind original original occurrence fs[0]!
  let family := fs[1]!
  let role ← projectField (familyHead ++ `role) family
  unless ← bound.roles.anyM (sameShape role) do FibSource.fail "family_role_not_selected"
  let simplex ← FibSource.constructorHead (← projectField (familyHead ++ `simplex) family)
  unless simplex.isAppOfArity ``Option.none 1 do FibSource.fail "free_simplex_or_unknown"
  -- A Boolean parameter domain contains at most two laws, so cannot cover the
  -- free five-mode simplex. Other shapes require an independently checked route.
  let params ← projectField
    `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Params bound.signature
  unless ← sameShape params (mkConst ``Bool) do FibSource.fail "non_simplex_shape_unknown"
  let law ← rawField (familyHead ++ `law) family
  let domain ← rawField (familyHead ++ `domain) family
  let actual ← projectField `LeanInformationAudit.Analysis.Source.actual bound.source
  let readout ← rawField
    `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout actual
  let readout := readout.beta #[role]
  disjoint #[law, domain, readout] structures
  let (separated, identifiable, clean) ← FibLaw.informationFacts target fs[3]!
  unless clean do FibSource.fail "facts_use_target_results"
  let capture := AuricFib.classifyCapture separated identifiable
  let face := match capture with
    | .strict => InformationFace.strictBound
    | .collapsed => .collapsedBound
    | .unknown => .unknownBound
  return {
    face := face
    application := some application.name
    registration := some record.occurrence.realizationName }

/-- The ordinary assessor is rerun on this exact compiled request. Its typed
records accompany the optional reading; no receipt or JSON is read as evidence. -/
unsafe def acquireInformation (source : Environment) (target : Name)
    (structures : Array Name) (application : Option Name) : IO InformationReading := do
  let some name := application | return {}
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  try
    let some index := source.getModuleIdxFor? name
      | throw <| IO.userError "application_owner_missing"
    let owner := source.header.moduleNames[index.toNat]!
    RawArtifacts.loadModule owner reader
    RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
    let store ← reader.get
    let some info := store.constants.find? name
      | throw <| IO.userError "application_missing"
    -- Reject unregistered sources before paying for ordinary reassessment.
    let context ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store owner
      {} (({} : NameSet).insert target)
    let precheck : FibSource.M Unit := do
      let .defnInfo definition := info | FibSource.fail "application_not_safe_definition"
      unless definition.safety == .safe do FibSource.fail "application_not_safe_definition"
      let app ← FibSource.fields
        `LeanInformationAudit.AuricFib.Contract.Application.mk definition.value
      let evidence ← FibSource.fields `LeanInformationAudit.AuricFib.Contract.Evidence.law app[0]!
      let client ← FibSource.fields `LeanInformationAudit.Analysis.Client.mk evidence[0]!
      discard <| registeredSource client[0]!
    discard <| (precheck.run 524288).run context
    let (state, _) ← ArtifactAssessment.assess store owner
    let context ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts state.store owner
      {} (({} : NameSet).insert target)
    let (reading, _) ← ((readFace state.store state target structures info).run 524288).run context
    let records ← state.records.mapM (TemplateBinding.recordJson (m := IO))
    let closures ← IO.mkRef ({ closure := store.metadata.axioms } : CompiledAxioms.AxiomClosureState)
    let axioms ← CompiledAxioms.collectAxiomsShared store.constants.find? closures name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError "unaccepted_axiom_closure"
    return {reading with ordinaryRecords := records}
  catch error => return {face := .notBound error.toString, application := some name}
  finally RawArtifacts.release reader

end LeanInformationAudit.SearchReduction

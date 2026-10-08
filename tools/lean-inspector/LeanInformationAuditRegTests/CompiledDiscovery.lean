import LeanInformationAuditRegTests.ContractRoots
import LeanInformationAuditRegTests.ContractPaths
import LeanInformationAuditRegTests.ContractTypeCarrier
import LeanInformationAuditRegTests.CompiledCalculations
import LeanInformationAuditRegTests.CompiledSeal
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.CompiledSourceOperands
import LeanInformationAudit.CompiledEvidence
import LeanInformationAudit.ArtifactRegistration

namespace LeanInformationAuditRegTests.CompiledDiscovery
open Lean LeanInformationAudit

@[noinline] private unsafe def releaseFixture (reader : IO.Ref RawArtifacts.Store) :
    IO (Array Name × Nat) := do
  RawArtifacts.loadModule `LeanInformationAudit.Contract.SourceAudit reader
  let store ← reader.get
  return (store.moduleOrder.map RawArtifacts.ownName, RawArtifacts.mapSize store.constants)

/-- Detached import keys remain usable after explicit release and reload. -/
unsafe def checkTargetRelease : IO Unit := do
  let target := `LeanInformationAudit.Contract.SourceAudit
  let shared ← RawArtifacts.sharedModules #[(target, #[]), (target, #[]), (target, #[])] true
  unless shared.contains target && shared.contains `Init do
    throw <| IO.userError "[FAIL] CompiledTargetRegionRelease: detached import plan"
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  let (names, count) ← releaseFixture reader
  unless count > 0 && !names.isEmpty do
    throw <| IO.userError "[FAIL] CompiledTargetRegionRelease: empty fixture"
  RawArtifacts.release reader
  let cleared ← reader.get
  unless RawArtifacts.mapSize cleared.constants == 0 && cleared.modules.isEmpty && cleared.regions.isEmpty
      && cleared.metadata.axioms.isEmpty && RawArtifacts.mapSize cleared.owners == 0
      && cleared.moduleIndices.isEmpty && cleared.protectedModules.isEmpty do
    throw <| IO.userError "[FAIL] CompiledTargetRegionRelease: retained target roots"
  let (reloaded, newCount) ← releaseFixture reader
  unless names == reloaded && count == newCount do
    throw <| IO.userError "[FAIL] CompiledTargetRegionRelease: detached keys or reload changed"
  RawArtifacts.release reader
  IO.println "[PASS] CompiledTargetRegionRelease"

@[noinline] private unsafe def verifyFork (base : RawArtifacts.Store)
    (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  let target := `LeanInformationAudit.Contract.RootStructure
  RawArtifacts.loadModule target reader
  let fork ← reader.get
  unless RawArtifacts.mapSize fork.constants > RawArtifacts.mapSize base.constants &&
      !base.modules.contains target && fork.modules.contains target do
    throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: base changed or target absent"
  unless fork.constants.map₁.size == base.constants.map₁.size &&
      fork.owners.map₁.size == base.owners.map₁.size && !fork.constants.map₂.isEmpty do
    throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: imported table copied for target"
  let name := (← base.getModule `LeanInformationAudit.Contract.SourceAudit).constNames[0]!
  let some info := base.constants.find? name
    | throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: shared constant missing"
  let replaced := fork.constants.insert name info
  unless RawArtifacts.mapSize replaced == RawArtifacts.mapSize fork.constants &&
      (replaced.find? name).map (·.type) == some info.type do
    throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: shadowed key counted twice"
  for index in [:fork.moduleOrder.size] do
    let owner := fork.moduleOrder[index]!
    unless fork.moduleIndices[owner]? == some index do
      throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: compiler order index"
  unless fork.protectedModules[target]? == some true &&
      fork.protectedModules[`Init]? == some false do
    throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: provenance ownership index"
  for owner in base.moduleOrder do
    unless fork.moduleIndices[owner]? == base.moduleIndices[owner]? &&
        fork.protectedModules[owner]? == base.protectedModules[owner]? do
      throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: shared prefix changed"

/-- A target extends immutable compiler indexes and then releases its own regions;
the original base remains readable for a second independent target. -/
unsafe def checkTargetIndexIsolation : IO Unit := do
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  RawArtifacts.loadModule `LeanInformationAudit.Contract.SourceAudit reader
  try
    let base ← reader.get
    let fork ← IO.mkRef ({} : RawArtifacts.Store)
    for _ in [:2] do
      fork.set base.fork
      try verifyFork base fork
      finally RawArtifacts.release fork
      let cleared ← fork.get
      unless cleared.moduleIndices.isEmpty && cleared.protectedModules.isEmpty do
        throw <| IO.userError "[FAIL] CompiledTargetIndexIsolation: completed target index retained"
      discard <| base.getModule `LeanInformationAudit.Contract.SourceAudit
    IO.println "[PASS] CompiledTargetIndexIsolation"
  finally RawArtifacts.release reader

/-- Read names from compiled implementation expressions, without maintaining a
second list of contract constants. Whole name literals are visited once. -/
private def contractNames (value : Expr) : NameSet := Id.run do
  let mut pending := #[value]
  let mut names : NameSet := {}
  while !pending.isEmpty do
    let value := pending.back!
    pending := pending.pop
    if let .ok name := Contract.Literal.name "contract_name" value then
      let scope := `LeanInformationAudit.Contract
      if scope != name && scope.isPrefixOf name then names := names.insert name
      continue
    match value with
    | .app function argument => pending := pending.push function |>.push argument
    | .lam _ type body _ | .forallE _ type body _ =>
        pending := pending.push type |>.push body
    | .letE _ type assigned body _ => pending := pending.push type |>.push assigned |>.push body
    | .mdata _ body | .proj _ _ body => pending := pending.push body
    | _ => pure ()
  return names

/-- Executable imports determine native linking. Contract data is instead read
from its compiler artifacts, and every quoted contract constant must exist. -/
unsafe def checkProgramBoundary (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  let roots := #[`Inspector, `LeanInformationAuditRegTests.CompiledDiscovery]
  let mut names : NameSet := {}
  for root in roots do
    -- Each executable owns a different `main` in its own compiler closure.
    let programReader ← IO.mkRef ({} : RawArtifacts.Store)
    RawArtifacts.loadModule root programReader
    let programs ← programReader.get
    let closure := reachableModules (ArtifactRegistration.importsOf programs) root
    let forbidden := closure.toArray.filter fun name =>
      #[`D5, `Reg, `Mathlib].any (·.isPrefixOf name)
    unless forbidden.isEmpty do
      throw <| IO.userError s!"compiled.program:mathematical_import:{root}:{forbidden}"
    IO.println s!"COMPILED_PROGRAM_IMPORTS root={root} total={closure.size} D5=0 Reg=0 Mathlib=0"
    for owner in programs.moduleOrder do
      unless (`LeanInformationAudit).isPrefixOf owner do continue
      for info in (← programs.getModule owner).constants do
        if let some value := info.value? (allowOpaque := true) then
          names := (contractNames value).toArray.foldl (fun acc name => acc.insert name) names
  unless !names.isEmpty do throw <| IO.userError "compiled.contract:no_names_checked"
  RawArtifacts.loadModule `LeanInformationAuditInterface.Contract.Catalog reader
  RawArtifacts.loadModule `LeanInformationAuditInterface.Contract.Registration reader
  let contracts ← reader.get
  for name in names.toArray.qsort Name.quickLt do
    unless contracts.constants.contains name do
      throw <| IO.userError s!"compiled.contract:missing_constant:{name}"
  IO.println s!"COMPILED_CONTRACT_NAMES {names.toArray.qsort Name.quickLt}"
  IO.println s!"[PASS] compiled contract names: {names.size} references exist in compiler artifacts"
  let missing := `LeanInformationAudit.Contract.AbsentNativeBoundaryConstant
  let result := Contract.Decoder.checkTarget (contracts.constants.find?) missing (mkConst missing)
  let expected := s!"contract.cannot_decode:{missing}:missing_constant"
  unless (match result with | .error reason => reason == expected | .ok _ => false) do
    throw <| IO.userError "compiled.contract:missing_name_accepted"
  IO.println s!"CONTRACT_DIAGNOSTIC boundary.missing_name {expected}"
  let result := Contract.Decoder.fields (contracts.constants.find?)
    `LeanInformationAudit.Contract.RootCatalog (mkNatLit 0) 1
  let expected := "contract.literal:LeanInformationAudit.Contract.RootCatalog:nonliteral:"
  let error ← try
    discard <| result
    pure "accepted"
  catch error => pure error.toString
  unless error.startsWith expected do
    throw <| IO.userError "compiled.contract:wrong_structure_accepted"
  IO.println s!"CONTRACT_DIAGNOSTIC boundary.wrong_structure {error}"
  let missingModule := `LeanInformationAuditRegTests.AbsentNativeBoundaryModule
  let error ← try
    discard <| RawArtifacts.readOwn missingModule
    pure "accepted"
  catch error => pure error.toString
  unless error.startsWith s!"raw.read_failed:{missingModule}:" do
    throw <| IO.userError "compiled.contract:missing_data_accepted"
  IO.println s!"CONTRACT_DIAGNOSTIC boundary.missing_data {error}"
  IO.println "[PASS] compiled boundary: missing names, structures and artifacts fail by name"

/-- Exercise the standalone artifact-reader boundary on every contract input
kind, including an indexed partial-slot family and rigid theorem universes. -/
unsafe def readFixtures (reader : IO.Ref RawArtifacts.Store) (start limit : Nat) : IO Unit := do
  let fixturePath ← Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  let saved ← searchPathRef.get
  searchPathRef.set (fixturePath :: saved)
  try
    let owners := #[`LeanInformationAuditRegTests.ContractFixtures]
    for owner in owners do RawArtifacts.loadModule owner reader
    RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
    RawArtifacts.loadModule `LeanInformationAuditRegTests.Fixtures.TemplateBodies reader
    RawArtifacts.loadModule `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit reader
    let store ← reader.get
    unless store.owners.find? (owners[0]!.str "source0") == some owners[0]! do
      throw <| IO.userError "compiled.metadata:declaration_owner"
    let positions := store.moduleOrder.foldl (init := ({} : NameMap Nat)) fun indices name =>
      indices.insert name indices.size
    for owner in store.moduleOrder do
      for item in (← store.getModule owner).imports do
        unless (positions.find? item.module).getD store.moduleOrder.size <
            (positions.find? owner).getD 0 do
          throw <| IO.userError s!"compiled.metadata:import_order:{owner}:{item.module}"
    let some projection := store.metadata.projections.find? `Fintype.elems
      | throw <| IO.userError "compiled.metadata:projection_missing"
    unless projection.ctorName == `Fintype.mk && projection.numParams == 1 &&
        projection.i == 0 && projection.fromClass &&
        store.metadata.classes.contains `Fintype &&
        store.metadata.instances.contains `Unit.fintype &&
        store.metadata.implementedBy.find? `Array.modifyM == some `Array.modifyMUnsafe &&
        store.metadata.externs.contains `Array.usize &&
        store.metadata.reducibility.find? `Array.uget == some .implicitReducible do
      throw <| IO.userError "compiled.metadata:declaration_semantics"
    IO.println s!"[PASS] compiled metadata owners={RawArtifacts.mapSize store.owners} \
      modules={store.moduleOrder.size} projections={store.metadata.projections.size} \
      classes={store.metadata.classes.toArray.size} instances={store.metadata.instances.toArray.size}"
    let context : Contract.CompiledExpressions.Context := {
      find := (store.constants.find?)
      heartbeatStart := start
      heartbeatLimit := limit }
    let natural := mkConst ``Nat
    let identity := Expr.lam `x natural (.bvar 0) .default
    let application := Expr.lam `f (mkForall `x .default natural natural)
      (mkApp (.bvar 0) (mkNatLit 0)) .default
    for other in #[application, mkConst ``Unit.unit] do
      let (same, _) ← Contract.CompiledExpressions.run context
        (Contract.CompiledExpressions.sameShape identity other)
      unless !same do throw <| IO.userError "compiled.shape:mismatched_function_domains"
    unless store.metadata.axioms.find?
        `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result ==
        some #[`propext, `Classical.choice, `Quot.sound] do
      throw <| IO.userError "compiled.metadata:exported_axioms"
    let closures ← IO.mkRef
      ({ closure := store.metadata.axioms } : CompiledAxioms.AxiomClosureState)
    let target := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result
    let some source := context.find target
      | throw <| IO.userError "compiled.axioms:source_missing"
    let aliasName := `compiledAxiomAlias
    let aliasInfo := ConstantInfo.defnInfo {
      name := aliasName, levelParams := source.levelParams, type := source.type,
      value := mkConst target (source.levelParams.map Level.param),
      hints := .abbrev, safety := .safe, all := [aliasName] }
    let aliasAxioms ← CompiledAxioms.collectAxiomsShared
      (fun name => if name == aliasName then some aliasInfo else context.find name) closures aliasName
    unless aliasAxioms.qsort Name.quickLt ==
        (store.metadata.axioms.find? target |>.getD #[]).qsort Name.quickLt do
      throw <| IO.userError s!"compiled.axioms:seeded_closure:{aliasAxioms}"
    unless (← closures.get).index.toArray.all (fun (name, _) =>
        !store.metadata.axioms.contains name) do
      throw <| IO.userError "compiled.axioms:exported_dependency_recomputed"
    let snapshot ← Contract.Discovery.discoverCompiled #[] owners context
      (fun owner => return (← store.getModule owner).constants)
      (CompiledAxioms.collectAxiomsShared context.find closures)
    unless snapshot.registrations.size == 16 && snapshot.enrollments.size == 1 &&
        snapshot.roots.size == 1 && snapshot.seals.size == 1 do
      throw <| IO.userError "compiled.discovery:input_inventory"
    let some (_, partialRow) := snapshot.registrations.find?
        (·.2.input.entry.unitName == `ContractTests.partialSensitivity.unit)
      | throw <| IO.userError "compiled.discovery:partial_slot_input"
    unless partialRow.input.entry.compiledMathematics.any (fun evidence =>
        evidence.partialReadouts == some #[true, false] && evidence.partialAnchors == some #[]) do
      throw <| IO.userError "compiled.discovery:partial_slot_support"
    let partialEntry ← CompiledRegistration.prepare context.find owners[0]! partialRow.input.entry
    let partialDiagnostic ← CompiledRegistration.validateFinite context.find partialEntry partialRow.input.options
    unless partialDiagnostic.any (fun message => message.startsWith "IE-C049" &&
        (message.splitOn "primitive=readout[1]").length == 2 &&
        (message.splitOn "support=[\"readout[0]\"]").length == 2) do
      throw <| IO.userError s!"compiled.registration:partial_support:{partialDiagnostic}"
    let some obligations := partialEntry.compiledMathematics
      | throw <| IO.userError "compiled.registration:obligations_missing"
    let noVariation := { partialEntry with compiledMathematics := some { obligations with variation := .absent } }
    unless (← CompiledRegistration.validateFinite context.find noVariation partialRow.input.options).any
        (fun message => message.startsWith "IE-C048" &&
          (message.splitOn "reason=missing_witness").length == 2) do
      throw <| IO.userError "compiled.registration:variation_precedence"
    IO.println "[PASS] compiled registration: finite partial support and variation precedence"
    for index in [:5] do
      let name := owners[0]!.str s!"source{index}"
      let some definition := snapshot.definitions.find? (·.info.name == name)
        | throw <| IO.userError s!"compiled.discovery:rigid_target:{name}"
      let target := definition.info.type.getAppArgs[1]!
      unless target.constLevels! == definition.info.levelParams.map Level.param do
        throw <| IO.userError s!"compiled.discovery:rigid_levels:{name}"
    IO.println "[PASS] compiled discovery reads 16 registrations, 1 enrollment, 1 root and 1 seal"
    let enrollmentContext ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store
      `LeanInformationAuditRegTests.Fixtures.TemplateBodies {} {}
    unless enrollmentContext.recursive `List.map && !enrollmentContext.recursive `Unit.fintype do
      throw <| IO.userError "compiled.enrollment:recursion_metadata"
    for (owner, enrollment) in snapshot.enrollments do
      let plan ← (TemplateAudit.CompiledEnrollment.compileTemplate owner enrollment.name
        enrollment.constructors).run enrollmentContext
      unless plan.data.sourceBound && plan.data.slots.size == 3 do
        throw <| IO.userError "compiled.enrollment:source_plan"
    let cases : Array (Name × Option String) := #[
      (`LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwise, none),
      (`LeanInformationAudit.Tests.DeclaredTemplates.boolCases, none),
      (`LeanInformationAudit.Tests.DeclaredTemplates.propositionSlot,
        some "unclassified_form:E1.proposition_slot"),
      (`LeanInformationAudit.Tests.DeclaredTemplates.wrongInterface,
        some "unclassified_form:E1.return_interface"),
      (`LeanInformationAudit.Tests.DeclaredTemplates.closedDecision,
        some "unclassified_form:E3.closed_decision"),
      (`LeanInformationAudit.Tests.DeclaredTemplates.recursiveBody,
        some "unclassified_form:E4.recursion:Nat.rec")]
    for (name, expected) in cases do
      let actual ← try
        let plan ← (TemplateAudit.CompiledEnrollment.compileTemplate
          enrollmentContext.provenance.view.mainModule name #[]).run enrollmentContext
        unless !plan.data.sourceBound && !plan.data.rules.isEmpty do
          throw <| IO.userError "compiled.enrollment:finite_plan"
        pure none
      catch error => pure (some error.toString)
      unless actual == expected do
        throw <| IO.userError s!"compiled.enrollment:{name}:expected={expected}:actual={actual}"
    let zero := { enrollmentContext with provenance := { enrollmentContext.provenance with
      options := ({} : Options).set `informationTemplate.work (0 : Nat) } }
    let exhausted ← try
      discard <| (TemplateAudit.CompiledEnrollment.compileTemplate
        zero.provenance.view.mainModule cases[0]!.1 #[]).run zero
      pure false
    catch error => pure (error.toString == "incomplete_closure:E8.erasure_work")
    unless exhausted do throw <| IO.userError "compiled.enrollment:zero_work"
    IO.println "[PASS] compiled enrollment: source, 6 finite cases, recursion metadata and zero work"
    let canonical := `Reg.D5.S0.Tower.GoldenGapZeckendorf
    let reachable := reachableModules (ArtifactRegistration.importsOf store) canonical
    let canonicalOwners := store.moduleOrder.filter (fun owner =>
      reachable.contains owner && (`Reg).isPrefixOf owner)
    let canonicalSnapshot ← Contract.Discovery.discoverCompiled #[] canonicalOwners context
      (fun owner => return (← store.getModule owner).constants)
      (CompiledAxioms.collectAxiomsShared context.find closures)
    let action : ArtifactRegistration.M Unit := do
      ArtifactRegistration.prepareSnapshot canonicalSnapshot
      let records ← ArtifactRegistration.assessJoined canonical
      unless records.size == canonicalSnapshot.registrations.size &&
          records.all (fun record => match record.result with
            | .declaredValidated _ => true | _ => false) do
        for record in records do
          if let .declaredUnresolved message := record.result then IO.println message
        throw <| IO.userError "compiled.registration:canonical_join_assessment"
      modify fun state => { state with records }
    let (_, canonicalState) ← action.run { store }
    let canonicalJson ← ArtifactRegistration.targetJson canonical canonicalState
    unless (canonicalJson.getObjValAs? (Array Json) "records").toOption.any
        (·.size == canonicalSnapshot.registrations.size) do
      throw <| IO.userError "compiled.registration:owner_records"
    let some firstEntry := canonicalState.entries[0]?
      | throw <| IO.userError "compiled.registration:empty_canonical_entries"
    let duplicate ← try
      CompiledRegistration.validateUnique firstEntry canonicalState.entries
      pure false
    catch error => pure (error.toString.startsWith "IE-C002 DuplicateRegistration")
    unless duplicate do throw <| IO.userError "compiled.registration:duplicate_accepted"
    IO.println "[PASS] compiled registration: complete canonical snapshot, companions, join and duplicate rejection"
    for sourceOwner in #[`Reg.D5.S0.Tower.GoldenGapZeckendorf,
        `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit] do
      let sourceSnapshot ← Contract.Discovery.discoverCompiled #[] #[sourceOwner] context
        (fun owner => return (← store.getModule owner).constants)
        (CompiledAxioms.collectAxiomsShared context.find closures)
      let some (_, sourceRow) := sourceSnapshot.registrations[0]?
        | throw <| IO.userError s!"compiled.source:registration_missing:{sourceOwner}"
      let entry := sourceRow.input.entry
      let some declaration := sourceRow.input.declaration
        | throw <| IO.userError "compiled.source:declaration_missing"
      let some selection := declaration.escapeInput.sourceSelection
        | throw <| IO.userError "compiled.source:selection_missing"
      let some sourceInfo := store.constants.find? entry.theoremName
        | throw <| IO.userError "compiled.source:target_missing"
      let some recordInfo := store.constants.find? entry.realizationName
        | throw <| IO.userError "compiled.source:record_missing"
      let sourceContext ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store sourceOwner
        sourceRow.input.options (({} : NameSet).insert entry.theoremName)
      let sourceAction : CompiledSourceScope.M Unit := do
        let scope ← CompiledSourceScope.resolve sourceInfo selection
        let record := mkConst entry.realizationName (recordInfo.levelParams.map Level.param)
        let arena := recordInfo.type.getAppArgs[0]!
        let family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
        let signature ← CompiledSourceScope.projectField (family ++ `Arena.signature) arena
        let actual ← CompiledSourceScope.projectField (family ++ `Registration.actual) record
        let law ← CompiledSourceScope.projectField (family ++ `Arena.Law) arena #[actual]
        CompiledSourceScope.reconstruct scope.expanded law
        CompiledSourceScope.validateFields scope signature actual
      discard <| (sourceAction.run 524288).run sourceContext
      let record := mkConst entry.realizationName (recordInfo.levelParams.map Level.param)
      let lawAction : CompiledSourceScope.M (Expr × Expr) := do
        let type ← CompiledSourceScope.projectType record
        let law ← CompiledSourceScope.projectField
          `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law type.getAppArgs[0]!
        let .forallE _ domain _ _ ← CompiledSourceScope.normalizeHead
            (← CompiledSourceScope.projectType law)
          | throw <| IO.userError "compiled.source:law_function_type"
        return (law, domain)
      let ((law, domain), _) ← (lawAction.run 524288).run sourceContext
      for evidence in #[none, some (record, law)] do
        let rejected ← try
          discard <| (CompiledSourceOperands.check entry.theoremName
            #[mkConst entry.theoremName (sourceInfo.levelParams.map Level.param)] 524288
            evidence).run sourceContext
          pure false
        catch error => pure (error.toString.startsWith "forbidden_dependency:source.operand_identity")
        unless rejected do throw <| IO.userError "compiled.source:theorem_identity_not_rejected"
      let unrelated := Expr.lam `realization domain (mkConst ``True) .default
      let unrelatedRejected ← try
        discard <| (CompiledSourceOperands.check entry.theoremName #[] 524288
          (some (record, unrelated))).run sourceContext
        pure false
      catch error => pure (error.toString.startsWith "unclassified_form:source.variation_law")
      unless unrelatedRejected do throw <| IO.userError "compiled.source:unrelated_variation_law"
      IO.println "[PASS] compiled source reconstruction, full observations and theorem identity rejection"
  finally searchPathRef.set saved


/-- The actual report executable must discover, assess and emit the typed input.
Direct assessment tests cannot detect a disconnected production dispatcher. -/
unsafe def checkProductionReport : IO Unit := do
  let executable ← Repository.source ".lake/build/lean-inspector/producer/bin/reportInspector"
  let temporary := (← IO.getEnv "TMPDIR").getD "/tmp"
  let directory : System.FilePath := s!"{temporary}/compiled-production-{← IO.monoNanosNow}"
  IO.FS.createDirAll directory
  try
    let report := directory / "report.json"
    let result ← IO.Process.output {
      cmd := executable.toString
      args := #["--output", report.toString, "--material-spool", (directory / "materials").toString,
        "Reg.D5.S0.Tower.GoldenGapZeckendorf", "Reg/D5/S0/Tower/GoldenGapZeckendorf.lean",
        "sha256:0000000000000000000000000000000000000000000000000000000000000000"] }
    unless result.exitCode == 0 do
      throw <| IO.userError s!"[FAIL] ProductionReportAssessesTypedRegistration: {result.stderr}"
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile report)
    let modules ← IO.ofExcept <| json.getObjValAs? (Array Json) "modules"
    let valid : Except String Unit := do
      let some row := modules[0]? | throw "missing module"
      let binding ← row.getObjVal? "information_templates"
      let records ← binding.getObjValAs? (Array Json) "records"
      unless records.size == 1 do throw s!"expected 1 registration, got {records.size}"
      let record := records[0]!
      unless (← record.getObjValAs? String "state") == "declared_validated" do
        throw s!"unvalidated registration: {record.compress}"
      let key ← record.getObjVal? "key"
      unless (← key.getObjValAs? String "theorem") ==
          "D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add" do throw "wrong target"
      pure ()
    if let .error reason := valid then
      throw <| IO.userError s!"[FAIL] ProductionReportAssessesTypedRegistration: {reason}"
    IO.println "[PASS] ProductionReportAssessesTypedRegistration"
  finally IO.FS.removeDirAll directory

end LeanInformationAuditRegTests.CompiledDiscovery

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let fixturePath ← LeanInformationAudit.Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  Lean.searchPathRef.modify (fixturePath :: ·)
  LeanInformationAuditRegTests.CompiledDiscovery.checkTargetRelease
  LeanInformationAuditRegTests.CompiledDiscovery.checkTargetIndexIsolation
  LeanInformationAuditRegTests.CompiledDiscovery.checkProductionReport
  let reader ← IO.mkRef ({} : LeanInformationAudit.RawArtifacts.Store)
  LeanInformationAuditRegTests.CompiledDiscovery.checkProgramBoundary reader
  LeanInformationAuditRegTests.CompiledDiscovery.readFixtures reader
    (← IO.getNumHeartbeats) (Lean.Core.getMaxHeartbeats ({} : Lean.Options))
  LeanInformationAuditRegTests.CompiledCalculations.check reader
  LeanInformationAuditRegTests.CompiledSeal.check reader
  LeanInformationAuditRegTests.ContractRoots.check reader
  LeanInformationAuditRegTests.ContractPaths.check reader
  LeanInformationAuditRegTests.ContractTypeCarrier.check reader
  LeanInformationAuditRegTests.ContractPaths.checkMirror reader

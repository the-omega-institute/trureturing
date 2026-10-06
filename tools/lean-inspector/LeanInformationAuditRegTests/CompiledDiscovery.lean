import LeanInformationAuditRegTests.ContractFixtures
import LeanInformationAuditRegTests.ContractWitnessFixture
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates
import LeanInformationAudit.CompiledSourceOperands

namespace LeanInformationAuditRegTests.CompiledDiscovery
open Lean LeanInformationAudit

/-- Exercise the standalone artifact-reader boundary on every contract input
kind, including an indexed partial-slot family and rigid theorem universes. -/
unsafe def readFixtures (start limit : Nat) : IO Unit := do
  let fixturePath ← Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  let saved ← searchPathRef.get
  searchPathRef.set (fixturePath :: saved)
  try
    let owners := #[`LeanInformationAuditRegTests.ContractFixtures,
      `LeanInformationAuditRegTests.ContractWitnessFixture]
    let reader ← IO.mkRef ({} : RawArtifacts.Store)
    for owner in owners do RawArtifacts.loadModule owner reader
    RawArtifacts.loadModule `LeanInformationAudit.Registry reader
    RawArtifacts.loadModule `LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates reader
    RawArtifacts.loadModule `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit reader
    let store ← reader.get
    unless store.owners[owners[0]!.str "source0"]? == some owners[0]! do
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
    IO.println s!"[PASS] compiled metadata owners={store.owners.size} \
      modules={store.moduleOrder.size} projections={store.metadata.projections.size} \
      classes={store.metadata.classes.toArray.size} instances={store.metadata.instances.toArray.size}"
    let context : Contract.CompiledExpressions.Context := {
      find := (store.constants[·]?)
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
    unless snapshot.registrations.size == 20 && snapshot.enrollments.size == 1 &&
        snapshot.roots.size == 1 && snapshot.seals.size == 1 do
      throw <| IO.userError "compiled.discovery:input_inventory"
    let some (_, partialRow) := snapshot.registrations.find?
        (·.2.input.entry.unitName == `ContractTests.partialSensitivity.unit)
      | throw <| IO.userError "compiled.discovery:partial_slot_input"
    unless partialRow.input.entry.compiledMathematics.any (fun evidence =>
        evidence.partialReadouts == some #[true, false] && evidence.partialAnchors == some #[]) do
      throw <| IO.userError "compiled.discovery:partial_slot_support"
    for index in [:5] do
      let name := owners[0]!.str s!"source{index}"
      let some definition := snapshot.definitions.find? (·.info.name == name)
        | throw <| IO.userError s!"compiled.discovery:rigid_target:{name}"
      let target := definition.info.type.getAppArgs[1]!
      unless target.constLevels! == definition.info.levelParams.map Level.param do
        throw <| IO.userError s!"compiled.discovery:rigid_levels:{name}"
    IO.println "[PASS] compiled discovery reads 20 registrations, 1 enrollment, 1 root and 1 seal"
    let enrollmentContext ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store
      `LeanInformationAudit.Tests.DeclaredTemplates {} {}
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
    for sourceOwner in #[`Reg.D5.S0.Tower.GoldenGapZeckendorf,
        `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit] do
      let sourceSnapshot ← Contract.Discovery.discoverCompiled #[] #[sourceOwner] context
        (fun owner => return (← store.getModule owner).constants)
        (CompiledAxioms.collectAxiomsShared context.find closures)
      let some (_, sourceRow) := sourceSnapshot.registrations[0]?
        | throw <| IO.userError "compiled.source:registration_missing"
      let entry := sourceRow.input.entry
      let some declaration := sourceRow.input.declaration
        | throw <| IO.userError "compiled.source:declaration_missing"
      let some selection := declaration.escapeInput.sourceSelection
        | throw <| IO.userError "compiled.source:selection_missing"
      let some sourceInfo := store.constants[entry.theoremName]?
        | throw <| IO.userError "compiled.source:target_missing"
      let some recordInfo := store.constants[entry.realizationName]?
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
      let rejected ← try
        discard <| (CompiledSourceOperands.check entry.theoremName
          #[mkConst entry.theoremName (sourceInfo.levelParams.map Level.param)] 524288).run sourceContext
        pure false
      catch error => pure (error.toString.startsWith "forbidden_dependency:source.operand_identity")
      unless rejected do throw <| IO.userError "compiled.source:theorem_identity_not_rejected"
      IO.println "[PASS] compiled source reconstruction, full observations and theorem identity rejection"
  finally searchPathRef.set saved

run_meta do
  readFixtures (← Lean.getInitHeartbeats) (← Lean.getMaxHeartbeats)

end LeanInformationAuditRegTests.CompiledDiscovery

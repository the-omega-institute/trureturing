import LeanInformationAudit.CompiledSourceScope
import LeanInformationAudit.Contract.Literal
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.ArtifactRegistration

namespace LeanInformationAuditRegTests.AuricFib.SourceContracts
open Lean LeanInformationAudit

/-- Tests call the existing reconstruction and readout correspondence checks on
current compiler artifacts. This does not implement production FIB acquisition. -/
private unsafe def checkSource (store : RawArtifacts.Store) (owner target sourceName : Name) : IO Unit := do
  let some targetInfo := store.constants.find? target
    | throw <| IO.userError s!"source-contract:missing-target:{target}"
  let some sourceInfo := store.constants.find? sourceName
    | throw <| IO.userError s!"source-contract:missing-source:{sourceName}"
  unless targetInfo.levelParams.length == sourceInfo.levelParams.length do
    throw <| IO.userError "source-contract:rigid-universe-count"
  let context ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store owner
    {} (({} : NameSet).insert target)
  let action : CompiledSourceScope.M Unit := do
    let source := mkConst sourceName (targetInfo.levelParams.map Level.param)
    let selectionTerm ← CompiledSourceScope.normalizeHead
      (← CompiledSourceScope.projectField `LeanInformationAudit.Analysis.Source.selection source)
    let selected ← IO.ofExcept (Contract.Literal.sourceSelection selectionTerm)
    let selection : LeanInformationAudit.SourceSelection := {
      owner := selected.owner
      definition := selected.definition.map fun d => { owner := d.owner, name := d.name, path := d.path }
      coordinates := selected.coordinates
      readouts := selected.readouts.map fun r => {
        path := r.path, stateBinder := r.stateBinder, functionOperand := r.functionOperand,
        stateOperand := r.stateOperand, booleanPredicate := r.booleanPredicate } }
    let scope ← CompiledSourceScope.resolve targetInfo selection
    let actual ← CompiledSourceScope.projectField `LeanInformationAudit.Analysis.Source.actual source
    let signature ← CompiledSourceScope.projectField `LeanInformationAudit.Analysis.Source.signature source
    let law ← CompiledSourceScope.projectField `LeanInformationAudit.Analysis.Source.rebuild source #[actual]
    CompiledSourceScope.reconstruct scope.expanded law
    CompiledSourceScope.validateFields scope signature actual
    let rejects (label expected : String) (test : CompiledSourceScope.M Unit) := do
      let observed ← try test; pure "accepted" catch error => pure error.toString
      unless observed == expected do
        throw <| IO.userError s!"source-contract:{label}:expected={expected}:actual={observed}"
      IO.println s!"[PASS] {label}: {observed}"
    rejects "unrelated-true-reconstruction" "unclassified_form:source.missing_binder"
      (CompiledSourceScope.reconstruct scope.expanded (mkConst ``True))
    rejects "wrong-source-owner" "unclassified_form:source.owner" do
      discard <| CompiledSourceScope.resolve targetInfo { selection with owner := `Unrelated }
    if let .forallE n d b _ := targetInfo.type then
      rejects "changed-implicit-binder" "unclassified_form:source.telescope_reconstruction"
        (CompiledSourceScope.reconstruct targetInfo.type (.forallE n d b .default))
    let withLet := Expr.letE `context (mkConst ``Nat) (mkNatLit 0) (mkConst ``True) true
    CompiledSourceScope.reconstruct withLet withLet
    rejects "changed-let-value" "unclassified_form:source.let_reconstruction"
      (CompiledSourceScope.reconstruct withLet
        (.letE `context (mkConst ``Nat) (mkNatLit 1) (mkConst ``True) true))
    rejects "erased-let-context" "unclassified_form:source.missing_let"
      (CompiledSourceScope.reconstruct withLet (mkConst ``True))
    IO.println s!"[PASS] source correspondence {target}: levels={scope.levels.length} telescope={scope.telescope.size} readouts={scope.readouts.size}"
  discard <| (action.run 524288).run context

/-- The native adapter retains the full original statement before selecting
its initialized single-window reader and appended-high task. -/
private unsafe def checkNativeSource (store : RawArtifacts.Store) : IO Unit := do
  let owner := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
  let target := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution
  let some info := store.constants.find? target
    | throw <| IO.userError "source-contract:missing-native-target"
  let context ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store owner
    {} (({} : NameSet).insert target)
  let action : CompiledSourceScope.M Unit := do
    let proof ← CompiledSourceScope.projectField
      `LeanInformationAudit.AuricFib.Contract.NativeSource.reconstruction
      (mkConst (owner ++ `source))
    let type ← CompiledSourceScope.projectType proof
    unless type.isAppOfArity `LeanInformationAudit.Analysis.Reconstruction 2 do
      throw <| IO.userError "source-contract:native-reconstruction-type"
    CompiledSourceScope.reconstruct info.type type.getAppArgs[0]!
    CompiledSourceScope.reconstruct info.type type.getAppArgs[1]!
    IO.println "[PASS] native reconstruction: complete original theorem before explicit specialization"
    let fixture := `LeanInformationAuditRegTests.AuricFib.CompiledFixture
    let some unrelated := store.constants.find? (fixture ++ `unrelated)
      | throw <| IO.userError "source-contract:missing-unrelated-fixture"
    let wrongProof ← CompiledSourceScope.projectField
      `LeanInformationAudit.AuricFib.Contract.NativeSource.reconstruction
      (mkConst (fixture ++ `wrongSource))
    let wrongType ← CompiledSourceScope.projectType wrongProof
    CompiledSourceScope.reconstruct unrelated.type wrongType.getAppArgs[0]!
    let rejection ← try
      CompiledSourceScope.reconstruct unrelated.type wrongType.getAppArgs[1]!
      pure "accepted"
    catch error => pure error.toString
    unless rejection == "unclassified_form:source.statement_reconstruction" do
      throw <| IO.userError s!"source-contract:propext-native-transport:{rejection}"
    IO.println s!"[PASS] propext native transport rejected by actual source reconstruction: {rejection}"
  discard <| (action.run 524288).run context

/-- Actual source-owned client closures are checked independently of compilation. -/
unsafe def check (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  let owners := #[`Reg.D5.S0.Diagonal.PigeonholeFiber,
    `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation,
    `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber]
  for owner in owners do RawArtifacts.loadModule owner reader
  RawArtifacts.loadModule `LeanInformationAuditRegTests.AuricFib.CompiledFixture reader
  RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
  let store ← reader.get
  let closures ← IO.mkRef ({} : CompiledAxioms.AxiomClosureState)
  for name in #[`Reg.D5.S0.Diagonal.PigeonholeFiber.finiteAnalysis,
      `Reg.D5.S0.Diagonal.PigeonholeFiber.constantAnalysis,
      `Reg.D5.S0.Diagonal.PigeonholeFiber.infiniteAnalysis,
      `Reg.D5.S0.Diagonal.PigeonholeFiber.quotientAnalysis,
      `Reg.D5.S0.Diagonal.PigeonholeFiber.restrictedAnalysis,
      `Reg.D5.S0.Diagonal.PigeonholeFiber.familyAnalysis,
      `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.analysis,
      `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.initializedWindow,
      `LeanInformationAudit.AuricFib.Contract.NativeSource.specialize,
      `LeanInformationAudit.AuricFib.Contract.NativeSource.continueHigh,
      `LeanInformationAudit.AuricFib.Contract.NativeBridge.reader_source,
      `LeanInformationAudit.AuricFib.Contract.NativeBridge.reply_source] do
    let axioms ← CompiledAxioms.collectAxiomsShared store.constants.find? closures name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError s!"source-contract:unaccepted-axioms:{name}:{axioms}"
    IO.println s!"[PASS] accepted axioms {name}: {axioms}"
  checkSource store owners[0]!
    `D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber
    `Reg.D5.S0.Diagonal.PigeonholeFiber.source
  checkSource store owners[1]!
    `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation
    `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.analysisSource
  checkNativeSource store
  let context := CompiledRegistration.expressionContext (store.constants.find?)
    (← IO.getNumHeartbeats) {}
  let snapshot ← Contract.Discovery.discoverCompiled #[] #[owners[1]!] context
    (fun owner => return (← store.getModule owner).constants)
    (CompiledAxioms.collectAxiomsShared context.find closures)
  unless snapshot.registrations.size == 1 do
    throw <| IO.userError "source-contract:ordinary-registration-inventory"
  let some (_, row) := snapshot.registrations[0]?
    | throw <| IO.userError "source-contract:ordinary-registration-missing"
  let entry := row.input.entry
  unless entry.sourceBound && entry.theoremName ==
      `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation &&
      entry.realizationName ==
      `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration do
    throw <| IO.userError "source-contract:ordinary-registration-correspondence"
  IO.println "[PASS] ordinary registration remains separate with its original source realization; no audit status assigned"

end LeanInformationAuditRegTests.AuricFib.SourceContracts

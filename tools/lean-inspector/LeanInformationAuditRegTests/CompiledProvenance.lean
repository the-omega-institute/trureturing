import LeanInformationAuditRegTests.Fixtures.ProvenanceFacts
import LeanInformationAudit.ReadoutProvenance
import LeanInformationAudit.Registry.Repository

namespace LeanInformationAuditRegTests.CompiledProvenance
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates

@[instance_reducible] def nonstandardOfNat : OfNat Nat 4 := ⟨137⟩

/-- Read real compiler artifacts and run provenance with no compiler context.
The assertions cover positive readouts, retained target identity, payload
rejection and the existing zero-work incomplete route. -/
unsafe def readFixture : IO Unit := do
  let fixturePath ← Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  let saved ← searchPathRef.get
  searchPathRef.set (fixturePath :: saved)
  let moduleName := `LeanInformationAuditRegTests.Fixtures.Provenance
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  RawArtifacts.loadModule `LeanInformationAuditRegTests.Fixtures.ProvenanceFacts reader
  let store ← reader.get
  let view := CompiledView.fromArtifacts store moduleName
  let factView : Contract.NodeFacts.View := {
    find := (store.constants[·]?), owner := (store.owners[·]?),
    external := fun name => inProtected view name &&
      (store.metadata.externs.contains name || store.metadata.implementedBy.contains name)
    sourceLeaf := fun name => !inProtected view name }
  let coordinate := fun declaration part => ({
    owner := moduleName, declaration, part, path := [] } : Contract.NodeCoordinate)
  let roots := #[coordinate `AllowlistBoundaries.target .type] ++
    (#[`AllowlistBoundaries.plain, `AllowlistBoundaries.proofArgument,
      `AllowlistBoundaries.forbiddenArgument, `AllowlistBoundaries.hiddenPayload]).flatMap
      (fun declaration => #[coordinate declaration .type, coordinate declaration .value])
  let some (.defnInfo coverage) :=
      store.constants[`LeanInformationAuditRegTests.Fixtures.ProvenanceFacts.coverage]?
    | throw <| IO.userError "compiled.provenance:coverage_missing"
  discard <| IO.ofExcept <| Contract.NodeFacts.coverage factView roots coverage.value
  let fields ← IO.ofExcept <| Contract.Literal.fields factView.find
    ``Contract.NodeCoverage coverage.value 2
  let names ← IO.ofExcept <| Contract.Literal.list "provenance.facts"
    (← IO.ofExcept <| Contract.Literal.resolveReferences factView.find fields[1]!)
  let nodeFacts ← names.mapM fun expression => do
    let name ← IO.ofExcept <| Contract.Literal.name "provenance.fact" expression
    IO.ofExcept <| Contract.NodeFacts.fact factView name
  let nodeFacts := nodeFacts.flatten
  unless !nodeFacts.isEmpty do
    throw <| IO.userError "compiled.provenance:empty_fact_closure"
  let session ← IO.mkRef ({} : ProvenanceSession)
  let context : QueryContext := {
    view, session, nodeFacts, heartbeatStart := (← IO.getNumHeartbeats),
    heartbeatLimit := provenanceDefEqHeartbeats,
    options := ({} : Options).setBool `trace.InformationProvenance.check true,
    trace := IO.println }
  let checkParameter := fun (label : String)
      (action : WalkM (Option ProvenanceAdmissionWitness)) (expected : Bool) => do
    let (actual, _) ← (action.run {
      theoremName := `AllowlistBoundaries.target, statement := mkConst ``True,
      decision := mkSort .zero, exprFuel := 100 }).run
        { context with nodeFacts := #[] }
    unless actual.isSome == expected do
      throw <| IO.userError s!"compiled.provenance:parameter:{label}"
    if let some actual := actual then
      unless actual.rule == .scopedParameter do
        throw <| IO.userError s!"compiled.provenance:parameter_rule:{label}"
    IO.println s!"[PASS] compiled provenance parameter {label} admitted={expected}"
  checkParameter "rigid_proposition" (withCompiledLocal `p .default (mkSort .zero)
    fun parameter => checkedStatementType view parameter) true
  checkParameter "assigned_proposition" (withCompiledLet `p (mkSort .zero) (mkConst ``True)
    fun parameter => checkedStatementType view parameter) false
  checkParameter "open_statement" (withCompiledLocal `p .default (mkSort .zero) fun parameter => do
    modify fun state => { state with statement := parameter }
    checkedStatementType view parameter) false
  checkParameter "data_parameter" (withCompiledLocal `n .default (mkConst ``Nat)
    fun parameter => checkedStatementType view parameter) false
  let equality := fun left right => mkAppN (mkConst ``Eq [.succ .zero])
    #[mkConst ``Nat, left, right]
  let four := mkNatLit 4
  let targetLiteral := mkNatLit 137
  let unknown := mkApp2 (mkConst ``Nat.add) four four
  let custom := mkAppN (mkConst ``OfNat.ofNat [.zero])
    #[mkConst ``Nat, mkRawNatLit 4, mkConst ``nonstandardOfNat]
  for (label, left, right, expected) in #[
      ("corresponding_literal", equality four unknown,
        equality targetLiteral unknown, true),
      ("same_literal", equality four four, equality four four, false),
      ("custom_dictionary", equality custom unknown,
        equality targetLiteral unknown, false),
      ("unknown_operands", equality unknown unknown,
        equality unknown unknown, false)] do
    unless naturalEqualityLiteralsApart left right == expected do
      throw <| IO.userError s!"compiled.provenance:literal_apart:{label}"
    IO.println s!"[PASS] compiled provenance literal apart {label} admitted={expected}"
  let (withoutFacts, _) ← ((checkedStatementType view (equality four four)).run {
    theoremName := `AllowlistBoundaries.target,
    statement := equality targetLiteral targetLiteral,
    decision := mkSort .zero, exprFuel := 100 }).run { context with nodeFacts := #[] }
  unless withoutFacts.isNone do
    throw <| IO.userError "compiled.provenance:literal_apart_without_exact"
  IO.println "[PASS] compiled provenance different literals without Exact have no authority"
  for (label, readout, rejected) in #[
      ("plain", `AllowlistBoundaries.plain, false),
      ("independent_proof", `AllowlistBoundaries.proofArgument, false),
      ("target_identity", `AllowlistBoundaries.forbiddenArgument, true),
      ("payload", `AllowlistBoundaries.hiddenPayload, true)] do
    let (actual, closure) ← (Compiled.readoutClosureCurrent
      `AllowlistBoundaries.target (mkConst readout)).run context
    unless actual == rejected && closure.isSome do
      throw <| IO.userError s!"compiled.provenance:{label}:{actual}:{closure}"
    IO.println s!"[PASS] compiled provenance {label} rejected={actual}"
  let (rejected, closure) ← (Compiled.readoutClosureCurrent
    `AllowlistBoundaries.target (mkConst `AllowlistBoundaries.plain)).run
      { context with options := ({} : Options).set `provenanceExpressionLimit (0 : Nat) }
  unless !rejected && closure.isNone do
    throw <| IO.userError "compiled.provenance:zero_work"
  for (label, querySession) in #[("cold", ← IO.mkRef ({} : ProvenanceSession)),
      ("warm", session)] do
    let (rejected, closure) ← (Compiled.readoutClosureCurrent
      `AllowlistBoundaries.target (mkConst `AllowlistBoundaries.plain)).run
        { context with
          session := querySession
          options := ({} : Options).set `provenanceDefEqLimit (0 : Nat) }
    unless !rejected && closure.isNone do
      throw <| IO.userError s!"compiled.provenance:zero_heartbeats:{label}"
    IO.println s!"[PASS] compiled provenance {label} zero heartbeats is incomplete"
  searchPathRef.set saved
  IO.println "[PASS] compiled provenance zero work is incomplete"

run_meta readFixture

end LeanInformationAuditRegTests.CompiledProvenance

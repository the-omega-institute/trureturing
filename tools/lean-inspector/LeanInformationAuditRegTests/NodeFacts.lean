import LeanInformationAudit.Contract.NodeFacts
import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.RegistrationRelations
import LeanInformationAudit.ReadoutProvenance.Carriers
import Reg.Support.DependentFamily
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Reg.Catalogs.IffRegistrations.SealedCatalog
import Reg.Support.CompiledNodeTerm

namespace LeanInformationAuditRegTests.NodeFacts
open Lean LeanInformationAudit LeanInformationAudit.Contract

def firstDecision : Decidable True := .isTrue True.intro
def secondDecision : Decidable True := .isTrue (And.left ⟨True.intro, True.intro⟩)
def firstBool := @decide True firstDecision
def secondBool := @decide True secondDecision

def decisionEquality : NodeFact := .equal
  (@decide True firstDecision) (@decide True secondDecision)
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.firstBool, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.secondBool, part := .value, path := [] }
  (congrArg (fun d => @decide True d) (Subsingleton.elim _ _))

def keepsProof : (x : Nat) → x = x → x = x := fun x h => h

def proofBoundary : NodeFact := .proof (∀ x : Nat, x = x → x = x)
  (fun x h => h)
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.keepsProof,
    part := .value, path := [.body,.body] }

def proofCoverage : NodeCoverage where
  roots := [{
    owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.keepsProof,
    part := .value, path := [] }]
  facts := [`LeanInformationAuditRegTests.NodeFacts.proofBoundary]

def truth : Prop := True
def otherTruth : Prop := ¬ False
def propositionBridge : NodeFact := .equivalent True (¬ False)
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.truth, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.otherTruth, part := .value, path := [] }
  (by simp)

def carrier : Type := Nat
def typeFact : NodeFact := .type Nat {
  owner := `LeanInformationAuditRegTests.NodeFacts,
  declaration := `LeanInformationAuditRegTests.NodeFacts.carrier, part := .value, path := [] }
def aliasUse : Type := carrier
def otherCarrier : Type := Bool
def otherAliasUse : Type := otherCarrier

def exactTypeFact : NodeFact := .exact carrier Nat
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.aliasUse, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.carrier, part := .value, path := [] }
  .evidence

def exactOtherTypeFact : NodeFact := .exact otherCarrier Bool
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.otherAliasUse, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.otherCarrier, part := .value, path := [] }
  .evidence

def unknownExact : NodeFact := .exact carrier Nat
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.aliasUse, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.carrier, part := .value, path := [] }
  .unknown

def dataValue : Nat := 7
def dataFact : NodeFact := .data Nat 7 {
  owner := `LeanInformationAuditRegTests.NodeFacts,
  declaration := `LeanInformationAuditRegTests.NodeFacts.dataValue, part := .value, path := [] }

def canonicalData : Nat := 7
def aliasData : Nat := dataValue
def canonicalDataUse : Nat := canonicalData

def notationData : NodeFact := compiled_fact% "data"
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"NodeFacts\",\"dataValue\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
def notationType : NodeFact := compiled_fact% "type"
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"NodeFacts\",\"carrier\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
def notationProof : NodeFact := compiled_fact% "proof"
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"NodeFacts\",\"keepsProof\"],\"part\":\"value\",\"path\":[\"body\",\"body\"],\"levels\":[]}"
def notationExact : NodeFact := compiled_exact%
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"NodeFacts\",\"aliasData\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"NodeFacts\",\"canonicalDataUse\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
def notationImportedType : NodeFact := compiled_fact% "type"
  "{\"declaration\":[\"Bool\"],\"part\":\"type\",\"path\":[],\"levels\":[]}"

def _root_.CompiledAddressOwnerMismatch.value : Nat := 7
def notationDifferentNamespace : NodeFact := compiled_fact% "data"
  "{\"declaration\":[\"CompiledAddressOwnerMismatch\",\"value\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

/-- error: compiled_fact:role -/
#guard_msgs in
example : NodeFact := compiled_fact% "relation"
  "{\"declaration\":[\"Bool\"],\"part\":\"type\",\"path\":[],\"levels\":[]}"

def canonicalEndpoint : NodeFact := .exact dataValue canonicalData
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.aliasData, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.canonicalDataUse, part := .value, path := [] }
  .evidence

def computedEndpoint : NodeFact := .exact dataValue 7
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.aliasData, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.dataValue, part := .value, path := [] }
  .evidence

def conflictingEndpoint : NodeFact := .exact dataValue dataValue
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.aliasData, part := .value, path := [] }
  { owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.aliasData, part := .value, path := [] }
  .evidence

def twoValues : Fin 2 → Nat := fun i => i.val
def tableEvidence : FiniteTable twoValues where
  entries := [
    { position := 0, within := by decide, item := 0, correct := rfl },
    { position := 1, within := by decide, item := 1, correct := rfl }]
  complete := rfl

def discards : Nat → Nat := fun _ => 0
def discardedInput : Nat := discards dataValue
def discardedCoverage : NodeCoverage where
  roots := [{
    owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.discardedInput, part := .value, path := [] }]
  facts := []

theorem genericIdentity.{u} {T : Sort u} (x : T) : x = x := rfl

def notationRawUniverse.{u} : NodeFact := compiled_fact% "type"
  "{\"declaration\":[\"LeanInformationAuditRegTests\",\"NodeFacts\",\"genericIdentity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"max\",[\"param\",[\"u\"]],[\"zero\"]]]}"

def genericRoot : RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.NodeFacts
  expected := [{
    statement := _
    proof := @genericIdentity.{1}
    theoremName := `LeanInformationAuditRegTests.NodeFacts.genericIdentity
    objectArenaName := `SyntheticArena
    statementIdentity := none
    registrationModuleName := `LeanInformationAuditRegTests.NodeFacts }].toArray
  source := #[]
  baseline := #[]
  companionPrefix := none } }

private def accept (label : String) (value : Except String α) : IO α := do
  match value with
  | .ok result => IO.println s!"[PASS] {label}"; pure result
  | .error reason => throw <| IO.userError s!"{label}:{reason}"

private def reject (label failurePrefix : String) (value : Except String α) : IO Unit := do
  match value with
  | .error reason =>
    unless reason.startsWith failurePrefix do throw <| IO.userError s!"{label}:wrong_failure:{reason}"
    IO.println s!"[PASS] {label}: {reason}"
  | .ok _ => throw <| IO.userError s!"{label}:accepted"

unsafe def check : IO Unit := do
  let reader ← IO.mkRef ({} : LeanInformationAudit.RawArtifacts.Store)
  LeanInformationAudit.RawArtifacts.loadModule `LeanInformationAuditRegTests.NodeFacts reader
  let store ← reader.get
  let view : Contract.NodeFacts.View := {
    find := fun n => store.constants[n]?
    owner := fun n => store.owners[n]?
    external := fun n => store.metadata.externs.contains n || store.metadata.implementedBy.contains n }
  let rawLevel := Expr.sort (.imax (.param `u) .zero)
  match Contract.Literal.instantiateRawLevels [`u] [.zero] rawLevel with
  | .sort (.imax .zero .zero) => pure ()
  | _ => throw <| IO.userError "universe_simplification"
  IO.println "[PASS] universe substitution preserves constructors"
  for (ordinary, abbreviated) in #[
      (`LeanInformationAuditRegTests.NodeFacts.dataFact,
        `LeanInformationAuditRegTests.NodeFacts.notationData),
      (`LeanInformationAuditRegTests.NodeFacts.typeFact,
        `LeanInformationAuditRegTests.NodeFacts.notationType),
      (`LeanInformationAuditRegTests.NodeFacts.proofBoundary,
        `LeanInformationAuditRegTests.NodeFacts.notationProof),
      (`LeanInformationAuditRegTests.NodeFacts.canonicalEndpoint,
        `LeanInformationAuditRegTests.NodeFacts.notationExact)] do
    let some ordinaryInfo := view.find ordinary | throw <| IO.userError "notation.ordinary_missing"
    let some abbreviatedInfo := view.find abbreviated | throw <| IO.userError "notation.abbreviated_missing"
    unless ordinaryInfo.type.equal abbreviatedInfo.type &&
        ordinaryInfo.value?.get!.equal abbreviatedInfo.value?.get! do
      throw <| IO.userError s!"notation.compiled_value:{abbreviated}"
    discard <| accept s!"notation constructor and address {abbreviated}" <|
      Contract.NodeFacts.fact view abbreviated
  for name in #[`LeanInformationAuditRegTests.NodeFacts.notationImportedType,
      `LeanInformationAuditRegTests.NodeFacts.notationDifferentNamespace] do
    let bound ← accept s!"notation actual module owner {name}" <| Contract.NodeFacts.fact view name
    unless bound.size == 1 && view.owner bound[0]!.location.declaration == some bound[0]!.location.owner do
      throw <| IO.userError s!"notation.owner:{name}"
  let universeBound ← accept "notation preserves raw universe constructors" <|
    Contract.NodeFacts.fact view `LeanInformationAuditRegTests.NodeFacts.notationRawUniverse
  unless universeBound.size == 1 do throw <| IO.userError "notation.universe_operand"
  match universeBound[0]!.location.levels with
  | [.max (.param parameter) .zero] =>
    unless parameter == `u do throw <| IO.userError "notation.universe_parameter"
  | _ => throw <| IO.userError "notation.universe_constructors"
  let facts := #[
    `Reg.Support.DependentFamily.bodyFact,
    `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.bridgeFact,
    `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.bridgeFact,
    `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.observationFact,
    `LeanInformationAuditRegTests.NodeFacts.decisionEquality,
    `LeanInformationAuditRegTests.NodeFacts.proofBoundary,
    `LeanInformationAuditRegTests.NodeFacts.propositionBridge,
    `LeanInformationAuditRegTests.NodeFacts.typeFact,
    `LeanInformationAuditRegTests.NodeFacts.dataFact,
    `LeanInformationAuditRegTests.NodeFacts.canonicalEndpoint,
    `LeanInformationAuditRegTests.NodeFacts.computedEndpoint,
    `LeanInformationAuditRegTests.NodeFacts.conflictingEndpoint,
    `LeanInformationAuditRegTests.NodeFacts.exactTypeFact,
    `LeanInformationAuditRegTests.NodeFacts.exactOtherTypeFact]
  let closure ← IO.mkRef ({} : LeanInformationAudit.CompiledAxioms.AxiomClosureState)
  for name in facts do
    let axioms ← LeanInformationAudit.CompiledAxioms.collectAxiomsShared view.find closure name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError s!"fact.axioms:{name}"
    let _ ← accept s!"compiled fact {name}" (Contract.NodeFacts.fact view name)
  let canonical ← IO.ofExcept <| Contract.NodeFacts.fact view
    `LeanInformationAuditRegTests.NodeFacts.canonicalEndpoint
  let computed ← IO.ofExcept <| Contract.NodeFacts.fact view
    `LeanInformationAuditRegTests.NodeFacts.computedEndpoint
  let selected ← accept "named canonical endpoint ignores computed endpoint" <|
    resolveCanonicalArena view.find (canonical ++ computed)
      (mkConst `LeanInformationAuditRegTests.NodeFacts.dataValue)
  unless selected.isConstOf `LeanInformationAuditRegTests.NodeFacts.canonicalData do
    throw <| IO.userError "canonical.endpoint"
  reject "missing named canonical endpoint" "contract.node_binding:arena.canonical_fact_missing" <|
    resolveCanonicalArena view.find computed (mkConst `LeanInformationAuditRegTests.NodeFacts.dataValue)
  let conflicting ← IO.ofExcept <| Contract.NodeFacts.fact view
    `LeanInformationAuditRegTests.NodeFacts.conflictingEndpoint
  reject "conflicting named canonical endpoints" "contract.node_binding:arena.canonical_fact_ambiguous" <|
    resolveCanonicalArena view.find (canonical ++ conflicting)
      (mkConst `LeanInformationAuditRegTests.NodeFacts.dataValue)
  let _ ← accept "positive conversion apartness" <| Contract.NodeFacts.inductiveApart view
    `LeanInformationAuditRegTests.NodeFacts.exactTypeFact `LeanInformationAuditRegTests.NodeFacts.exactOtherTypeFact
  let compiledView := RegistrationGates.CompiledView.fromArtifacts store
    `LeanInformationAuditRegTests.NodeFacts
  let checkApart := fun (label : String) (facts : Array Contract.NodeFacts.BoundOperand)
      (left right : Expr) (expected : Bool) => do
    let session ← IO.mkRef ({} : RegistrationGates.ProvenanceSession)
    let heartbeatStart ← IO.getNumHeartbeats
    let context : RegistrationGates.QueryContext := {
      view := compiledView, session, nodeFacts := facts,
      heartbeatStart, heartbeatLimit := RegistrationGates.provenanceDefEqHeartbeats }
    let (result, _) ← ((RegistrationGates.checkedStatementType compiledView left).run {
      theoremName := `LeanInformationAuditRegTests.NodeFacts,
      statement := right, decision := mkSort .zero, exprFuel := 100 }).run context
    unless result.isSome == expected do throw <| IO.userError s!"{label}:apartness_authority"
    if let some result := result then
      unless result.rule == .statementHeadApart do throw <| IO.userError s!"{label}:apartness_rule"
    IO.println s!"[PASS] {label}"
  checkApart "raw rigid heads have no apartness authority" #[]
    (mkConst ``Nat) (mkConst ``Bool) false
  let exactLeft ← IO.ofExcept <| Contract.NodeFacts.fact view
    `LeanInformationAuditRegTests.NodeFacts.exactTypeFact
  let exactRight ← IO.ofExcept <| Contract.NodeFacts.fact view
    `LeanInformationAuditRegTests.NodeFacts.exactOtherTypeFact
  checkApart "one exact endpoint has no apartness authority" exactLeft
    (mkConst `LeanInformationAuditRegTests.NodeFacts.carrier)
    (mkConst `LeanInformationAuditRegTests.NodeFacts.otherCarrier) false
  checkApart "two exact rigid endpoints certify apartness" (exactLeft ++ exactRight)
    (mkConst `LeanInformationAuditRegTests.NodeFacts.carrier)
    (mkConst `LeanInformationAuditRegTests.NodeFacts.otherCarrier) true
  let mathematicalBridge ← IO.ofExcept <| Contract.NodeFacts.fact view
    `LeanInformationAuditRegTests.NodeFacts.propositionBridge
  checkApart "mathematical Iff has no conversion apartness authority" mathematicalBridge
    (mkConst ``True) (mkApp (mkConst ``Not) (mkConst ``False)) false
  reject "absent definitional evidence" "contract.node_binding:exact_evidence_required"
    (Contract.NodeFacts.fact view `LeanInformationAuditRegTests.NodeFacts.unknownExact)
  let _ ← accept "statement exclusion" <| Contract.NodeFacts.exclusion view
    `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.exclusion
  let _ ← accept "finite family lift" <| Contract.NodeFacts.finiteLift view
    `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.finiteLiftFacts
    `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
    `Reg.Support.LegacyRelations.System.arena
    `Reg.Support.LegacyRelations.System.fromLegacy `Reg.Support.LegacyRelations.System.toLegacy
  let allEvidence := #[
    `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.exclusion,
    `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.finiteLiftFacts,
    `Reg.Catalogs.IffRegistrations.SealedCatalog.facts_0]
  for name in allEvidence do
    let axioms ← LeanInformationAudit.CompiledAxioms.collectAxiomsShared view.find closure name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError s!"evidence.axioms:{name}:{axioms}"
  let some (.defnInfo tab) := view.find `LeanInformationAuditRegTests.NodeFacts.tableEvidence
    | throw <| IO.userError "table.definition"
  let values ← accept "complete literal table" <| Contract.NodeFacts.table view tab.value 2
  unless (← IO.ofExcept (values.mapM (Contract.Literal.nat "test.value"))) == #[0,1] do
    throw <| IO.userError "table.values"
  reject "omitted table row" "contract.node_binding:table_positions"
    (Contract.NodeFacts.table view tab.value 3)

  let rootCount ← accept "root catalog" <| Contract.NodeFacts.root view
    `Reg.Catalogs.IffRegistrations.SealedCatalog.rootCatalog
  unless rootCount == 2 do throw <| IO.userError "root.count"
  let genericRootCount ← accept "root with explicit universe instance" <| Contract.NodeFacts.root view
    `LeanInformationAuditRegTests.NodeFacts.genericRoot
  unless genericRootCount == 1 do throw <| IO.userError "root.generic_count"
  let sealReadout ← accept "literal seal" <| Contract.NodeFacts.sealFacts view
    (mkConst `Reg.Catalogs.IffRegistrations.SealedCatalog.facts_0) {
      owner := `Reg.Catalogs.IffRegistrations.SealedCatalog
      declaration := `Reg.Catalogs.IffRegistrations.SealedCatalog.view_0
      part := .value
      path := [.function, .argument] }
  unless sealReadout.size == 1 do
    throw <| IO.userError "seal.unit_membership"
  let some (.defnInfo cover) := view.find `LeanInformationAuditRegTests.NodeFacts.proofCoverage
    | throw <| IO.userError "coverage.definition"
  let location : NodeCoordinate := {
    owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.keepsProof,
    part := .value, path := [] }
  let walked ← accept "complete raw coverage" <| Contract.NodeFacts.coverage view #[location] cover.value
  IO.println s!"READOUT coverage_nodes={walked} root_rows={rootCount} seal_units={sealReadout.size}"
  let tainted : Contract.NodeFacts.View := {
    view with
    external := fun n => n == ``Eq || view.external n }
  reject "proof proposition retained" "contract.node_binding:closure_unsafe:Eq"
    (Contract.NodeFacts.coverage tainted #[location] cover.value)
  let some (.defnInfo discarded) := view.find `LeanInformationAuditRegTests.NodeFacts.discardedCoverage
    | throw <| IO.userError "discarded.definition"
  let dataTainted : Contract.NodeFacts.View := {
    view with
    external := fun n => n == `LeanInformationAuditRegTests.NodeFacts.dataValue || view.external n }
  let discardedLocation : NodeCoordinate := {
    owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.discardedInput, part := .value, path := [] }
  reject "discarded argument retained" "contract.node_binding:closure_unsafe"
    (Contract.NodeFacts.coverage dataTainted #[discardedLocation] discarded.value)
  reject "omitted root" "contract.node_binding:coverage_roots"
    (Contract.NodeFacts.coverage view #[] cover.value)
  reject "wrong owner" "contract.node_binding:owner"
    (Contract.NodeFacts.locate view { location with owner := `Other })
  reject "wrong edge" "contract.node_binding:edge_shape"
    (Contract.NodeFacts.locate view { location with path := [.argument] })
  let stale : Contract.NodeFacts.View := {
    view with
    find := fun n =>
      if n == `LeanInformationAuditRegTests.NodeFacts.firstBool then
        (view.find n).map (fun info => match info with
          | .defnInfo d => .defnInfo { d with value := mkConst ``Bool.false }
          | other => other)
      else view.find n }
  reject "stale bound operand" "contract.node_binding:operand"
    (Contract.NodeFacts.fact stale `LeanInformationAuditRegTests.NodeFacts.decisionEquality)

end LeanInformationAuditRegTests.NodeFacts

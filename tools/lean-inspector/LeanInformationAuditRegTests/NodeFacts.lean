import LeanInformationAudit.Contract.NodeFacts
import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms
import Reg.Support.DependentFamily
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
import Reg.Catalogs.IffRegistrations.SealedCatalog

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

def twoValues : Fin 2 → Nat := fun i => i.val
def tableEvidence : FiniteTable twoValues where
  entries := [
    { position := 0, within := by decide, item := 0, correct := rfl },
    { position := 1, within := by decide, item := 1, correct := rfl }]
  complete := rfl

def identityPartition : FinitePartition Bool Eq where
  rows := [{ item := false, classId := 0 }, { item := true, classId := 1 }]
  nodup := by decide +kernel
  complete := by decide +kernel
  classes := by decide +kernel

def shiftedPartition : FinitePartition Bool Eq where
  rows := [{ item := false, classId := 1 }, { item := true, classId := 2 }]
  nodup := by decide +kernel
  complete := by decide +kernel
  classes := by decide +kernel

def discards : Nat → Nat := fun _ => 0
def discardedInput : Nat := discards dataValue
def discardedCoverage : NodeCoverage where
  roots := [{
    owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.discardedInput, part := .value, path := [] }]
  facts := []

theorem genericIdentity.{u} {T : Sort u} (x : T) : x = x := rfl

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

def falseClaim : Prop := False
def rejection : Prop := ¬ falseClaim
theorem aliasedResult : rejection := by intro h; exact h
def aliasedRefutation : UtilityRefutation falseClaim aliasedResult := {}

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
    `LeanInformationAuditRegTests.NodeFacts.exactTypeFact,
    `LeanInformationAuditRegTests.NodeFacts.exactOtherTypeFact]
  let closure ← IO.mkRef ({} : LeanInformationAudit.CompiledAxioms.AxiomClosureState)
  for name in facts do
    let axioms ← LeanInformationAudit.CompiledAxioms.collectAxiomsShared view.find closure name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError s!"fact.axioms:{name}"
    let _ ← accept s!"compiled fact {name}" (Contract.NodeFacts.fact view name)
  let _ ← accept "positive conversion apartness" <| Contract.NodeFacts.inductiveApart view
    `LeanInformationAuditRegTests.NodeFacts.exactTypeFact `LeanInformationAuditRegTests.NodeFacts.exactOtherTypeFact
  reject "absent definitional evidence" "contract.node_binding:exact_evidence_required"
    (Contract.NodeFacts.fact view `LeanInformationAuditRegTests.NodeFacts.unknownExact)
  let _ ← accept "statement exclusion" <| Contract.NodeFacts.exclusion view
    `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.exclusion
  let _ ← accept "finite family lift" <| Contract.NodeFacts.finiteLift view
    `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.finiteLiftFacts
    `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
    `Reg.Support.LegacyRelations.System.arena
    `Reg.Support.LegacyRelations.System.fromLegacy `Reg.Support.LegacyRelations.System.toLegacy
  let _ ← accept "utility refutation" <| Contract.NodeFacts.utility view
    `Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.refutation
    `CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.claim
    `CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.result
    `D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
    `D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
  let _ ← accept "aliased utility refutation" <| Contract.NodeFacts.utility view
    `LeanInformationAuditRegTests.NodeFacts.aliasedRefutation
    `LeanInformationAuditRegTests.NodeFacts.falseClaim `LeanInformationAuditRegTests.NodeFacts.aliasedResult
    `LeanInformationAuditRegTests.NodeFacts `LeanInformationAuditRegTests.NodeFacts
  let allEvidence := #[
    `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.exclusion,
    `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.finiteLiftFacts,
    `Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.refutation,
    `Reg.Catalogs.IffRegistrations.SealedCatalog.LiteralEvidence.facts]
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
  let some (.defnInfo partition) := view.find `LeanInformationAuditRegTests.NodeFacts.identityPartition
    | throw <| IO.userError "partition.definition"
  let ids ← accept "canonical partition labels" <| Contract.NodeFacts.partition view partition.value
  unless ids == #[0,1] do throw <| IO.userError "partition.labels"
  let some (.defnInfo shifted) := view.find `LeanInformationAuditRegTests.NodeFacts.shiftedPartition
    | throw <| IO.userError "partition.shifted_definition"
  reject "noncanonical partition labels" "contract.node_binding:partition_numbering"
    (Contract.NodeFacts.partition view shifted.value)
  let rootCount ← accept "root catalog" <| Contract.NodeFacts.root view
    `Reg.Catalogs.IffRegistrations.SealedCatalog.rootCatalog
  unless rootCount == 2 do throw <| IO.userError "root.count"
  let genericRootCount ← accept "root with explicit universe instance" <| Contract.NodeFacts.root view
    `LeanInformationAuditRegTests.NodeFacts.genericRoot
  unless genericRootCount == 1 do throw <| IO.userError "root.generic_count"
  let sealReadout ← accept "literal seal" <| Contract.NodeFacts.sealFacts view
    `Reg.Catalogs.IffRegistrations.SealedCatalog.LiteralEvidence.facts {
      owner := `Reg.Catalogs.IffRegistrations.SealedCatalog
      declaration := `Reg.Catalogs.IffRegistrations.SealedCatalog.seal
      part := .value
      path := [.function, .argument, .argument, .function, .argument] }
  unless sealReadout.units == 1 && sealReadout.rows.size == 1 && sealReadout.rows[0]!.1 == 8 &&
      sealReadout.rows[0]!.2.1 == 12 && sealReadout.rows[0]!.2.2.1 == #[0,0,0,0,0,0,0,8,0,0,0,0,0,0,0] &&
      sealReadout.rows[0]!.2.2.2.1 == #[0,1,1,0] && sealReadout.rows[0]!.2.2.2.2.size == 2 do
    throw <| IO.userError s!"seal.readout:{repr sealReadout}"
  let some (.defnInfo cover) := view.find `LeanInformationAuditRegTests.NodeFacts.proofCoverage
    | throw <| IO.userError "coverage.definition"
  let location : NodeCoordinate := {
    owner := `LeanInformationAuditRegTests.NodeFacts,
    declaration := `LeanInformationAuditRegTests.NodeFacts.keepsProof,
    part := .value, path := [] }
  let walked ← accept "complete raw coverage" <| Contract.NodeFacts.coverage view #[location] cover.value
  IO.println s!"READOUT coverage_nodes={walked} root_rows={rootCount} seal_rows={sealReadout.rows.size}"
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
  reject "wrong utility result" "contract.node_binding:utility_indices" <| Contract.NodeFacts.utility view
    `Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.refutation
    `CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.claim ``True.intro
    `D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
    `D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation

end LeanInformationAuditRegTests.NodeFacts

import LeanInformationAudit.ReadoutProvenance
import LeanInformationAuditAnalysis.Tests.ExternalAllowlistTypes
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Basic
import Mathlib.Algebra.Field.ZMod

open Lean LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape
namespace AllowlistBoundaries

theorem appliedTarget (x : Bool) : x = x := rfl
theorem appliedCompanion.__information_unit (x : Bool) : x = x := rfl
theorem subsetTarget : ({true} : Finset Bool) ⊆ {true} := by intro x hx; exact hx
theorem existentialTarget : ∃ b : Bool, b = b := ⟨true, rfl⟩
theorem target : (137 : Nat) = 137 := rfl
theorem letTarget : (let n : Nat := 137; n = n) := rfl
def computedStatement : Prop := (136 + 1 : Nat) = 136 + 1
theorem computedTarget : (136 + 1 : Nat) = 136 + 1 := rfl
theorem computedAliasTarget : computedStatement := rfl
theorem harmless : (2 : Nat) ∣ 4 := by norm_num
structure PropositionCarrier where
  statement : Prop
def propositionCarrier : PropositionCarrier := ⟨(137 : Nat) = 137⟩
theorem projectedTarget : propositionCarrier.statement := rfl
def aliasedStatement : Prop := (137 : Nat) = 137
theorem aliasTarget : aliasedStatement := rfl
def aliasedNumber : Nat := 137
theorem aliasedProof : aliasedNumber = aliasedNumber := rfl
theorem alternative : (2 : Nat) ∣ 4 := ⟨2, rfl⟩
def keep {p : Prop} (_ : p) (x : Bool) : Bool := x
def plain (_ : Unit) (state : Bool) : Bool := state
def proofArgument (_ : Unit) (state : Bool) : Bool := keep harmless state
def aliasedArgument (_ : Unit) (state : Bool) : Bool := keep aliasedProof state
def alternativeArgument (_ : Unit) (state : Bool) : Bool := keep alternative state
structure CertifiedBit where
  bit : Bool
  certificate : (2 : Nat) ∣ 4
def proofField (_ : Unit) (state : Bool) : Bool := (CertifiedBit.mk state harmless).bit
def forbiddenArgument (_ : Unit) (state : Bool) : Bool := keep target state
set_option linter.style.nameCheck false in
theorem companion.__information_unit : True := True.intro
theorem independentTargetImplementation : (2 : Nat) ∣ 4 := let _ := target; harmless
theorem independentCompanionImplementation : (2 : Nat) ∣ 4 :=
  let _ := companion.__information_unit
  harmless
def internalTargetRead (_ : Unit) (state : Bool) : Bool := keep independentTargetImplementation state
def internalCompanionRead (_ : Unit) (state : Bool) : Bool := keep independentCompanionImplementation state
def forbiddenCompanion (_ : Unit) (state : Bool) : Bool := keep companion.__information_unit state
structure Hidden where
  bit : Bool
  certificate : (137 : Nat) = 137
def hiddenPayload (_ : Unit) (state : Bool) : Bool := (Hidden.mk state rfl).bit
class Unknown where
  bit : Bool
def unfamiliar : Unknown := ⟨true⟩
def unknownRead (_ : Unit) (state : Bool) : Bool := cond unfamiliar.bit state false
noncomputable def classicalRead (_ : Unit) (state : Bool) : Bool :=
  @decide (state = true) (Classical.propDecidable _)
noncomputable def erasedScalar : Bool := Classical.choice (show Nonempty Bool from ⟨true⟩)
def erasedPredicateRead (_ : Unit) (state : Bool) : Bool :=
  let _ : Decidable (erasedScalar = erasedScalar) := .isTrue rfl
  state
theorem erasedPredicateTarget : erasedScalar = erasedScalar := rfl

def arenaCardRead (_ : Unit) (state : Bool) : Bool :=
  let _ := (Arena.ofFintype Bool).card
  state
def catalogIndexCard {arena : Arena.{0}} (catalog : Catalog.{0,0,0} arena) : Nat :=
  letI := catalog.indexFintype
  Fintype.card catalog.Index
def catalogCarrierRead (_ : Unit) (state : Bool) : Bool :=
  let _ := @catalogIndexCard
  state
def bundleIndexCard (bundle : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{0,0} Bool) : Nat :=
  letI := bundle.indexFintype
  Fintype.card bundle.Index
def bundleCarrierRead (_ : Unit) (state : Bool) : Bool :=
  let _ := bundleIndexCard
  state
def hiddenArena : Arena where
  State := PLift ((137 : Nat) = 137)
  stateFintype := ⟨{⟨rfl⟩}, by intro ⟨h⟩; simp⟩
  stateDecidableEq := fun a b => .isTrue (Subsingleton.elim a b)
def hiddenArenaRead (_ : Unit) (state : Bool) : Bool :=
  let _ := hiddenArena.card
  state

def nestedScalarRead (_ : Unit) (state : Bool) : Bool :=
  if Fintype.card ((Bool × Bool) ⊕ (Bool ⊕ Unit)) = 7 then state else false

def subtypeScalarRead (_ : Unit) (state : Bool) : Bool :=
  if Fintype.card {b : Bool // b = true} = 1 then state else false
def nativeSubtypePayload (_ : Unit) (state : Bool) : Bool :=
  (BoundarySubtypeFixtures.payload state).val
def subsetMetadataRead (_ : Unit) (state : Bool) : Bool :=
  if Fintype.card Bool = 2 then state else false

def commutativeRingRead (_ : Unit) (state : Bool) : Bool :=
  let _ : NonUnitalNonAssocCommRing (ZMod 2) := inferInstance
  let _ : NonUnitalCommRing (ZMod 2) := inferInstance
  let _ : NonUnitalNonAssocCommSemiring (ZMod 2) := inferInstance
  let _ : NonUnitalCommSemiring (ZMod 2) := inferInstance
  state
def hiddenFunctionInterface : DFunLike (PLift ((137 : Nat) = 137)) Unit (fun _ => Bool) where
  coe _ _ := true
  coe_injective := by intro a b _; cases a; cases b; rfl
def hiddenFunctionInterfaceRead (_ : Unit) (state : Bool) : Bool :=
  let _ := hiddenFunctionInterface
  state
def hiddenEquivalenceInterface : EquivLike (PLift ((137 : Nat) = 137)) Bool Bool where
  coe _ b := b
  inv _ b := b
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  coe_injective' := by intro a b _ _; cases a; cases b; rfl
def hiddenEquivalenceInterfaceRead (_ : Unit) (state : Bool) : Bool :=
  let _ := hiddenEquivalenceInterface
  state
def equivalenceInterfaceRead (_ : Unit) (state : Bool) : Bool :=
  let _ : EquivLike (Bool ≃ Bool) Bool Bool := inferInstance
  state
def functionInterfaceRead (_ : Unit) (state : Bool) : Bool :=
  let _ : DFunLike (ZMod 2 →+* ZMod 2) (ZMod 2) (fun _ => ZMod 2) := inferInstance
  state
def fieldRead (_ : Unit) (state : Bool) : Bool :=
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Field (ZMod 2) := inferInstance
  state
def boundedNatRead (_ : Unit) (state : Bool) : Bool :=
  let _ : Nat.AtLeastTwo 2 := inferInstance
  state
def orderRead (_ : Unit) (state : Bool) : Bool :=
  let _ : LinearOrder Nat := inferInstance
  state
def rangeRead (_ : Unit) (state : Bool) : Bool :=
  @decide ((fun _ : Unit => state) ∈ Set.range (fun _ : Unit => fun _ : Unit => state))
    (Fintype.decidableMemRangeFintype _ _)
def appliedRead (_ : Unit) (state : Bool) : Bool := keep (appliedTarget state) state
def appliedCompanionRead (_ : Unit) (state : Bool) : Bool :=
  keep (appliedCompanion.__information_unit state) state
def firstMonoid : AddCommMonoid Nat := inferInstance
def secondMonoid : AddCommMonoid Nat := inferInstance
def monoidRead (_ : Unit) (state : Bool) : Bool :=
  let _ : AddCommMonoid Nat := firstMonoid
  let _ : AddCommMonoid Nat := secondMonoid
  state
def ringRead (_ : Unit) (state : Bool) : Bool :=
  let _ : AddMonoidWithOne Nat := inferInstance
  let _ : Semiring Nat := inferInstance
  let _ : Distrib Nat := inferInstance
  state
def appendRead (_ : Unit) (state : Bool) : Bool :=
  (([state] : List Bool) ++ [false]).headD false
def unionRead (_ : Unit) (state : Bool) : Bool :=
  decide (state ∈ (({true} : Finset Bool) ∪ {false}))
def localProfile (n : Nat) : Nat := n + 1
def localRead (_ : Unit) (state : Bool) : Bool := if localProfile (if state then 4 else 3) = 5 then state else false

def signature : PrimitiveSignature.{0,0,0} Bool where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by intro; decide
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def template : PrimitiveRealization signature := ⟨plain, Fin.elim0⟩
private def query (label : String) (readout : Name) : CoreM (Option String) := do
  let some (.defnInfo info) := (← getEnv).find? ``template | throwError "template missing"
  let holder := `AllowlistBoundaries |>.str label
  addDecl <| .defnDecl {
    name := holder, levelParams := [], type := info.type
    value := info.value.replace fun e => if e == mkConst ``plain then some (mkConst readout) else none
    hints := .abbrev, safety := .safe }
  let theoremName := if readout == ``subsetMetadataRead then ``subsetTarget
    else if #[``rangeRead, ``fieldRead, ``equivalenceInterfaceRead, ``functionInterfaceRead, ``commutativeRingRead, ``nestedScalarRead, ``subtypeScalarRead].contains readout
      then ``existentialTarget else ``target
  provenanceErrorCurrent (← getEnv).header.mainModule `catalog theoremName holder

-- Independent proof implementations have identical executable meaning. The
-- target proof, generated companion, and nominal statement payload remain barred.
private def assertQuery (label : String) (readout : Name) (reason : String) : CoreM Unit := do
  let actual ← query label readout
  let ok := if reason == "clean" then actual.isNone
    else if reason == "reject" then actual.isSome
    else actual.any (·.contains s!"reason={reason}")
  let exactSite := label != "UnknownClassSite" || actual.any (fun message =>
    message.contains "\"first\":\"AllowlistBoundaries.Unknown.bit\"" &&
    message.contains "\"site\":\"AllowlistBoundaries.unknownRead\"")
  if ok && exactSite then logInfo m!"[PASS] {label}: {actual}"
  else logError m!"[FAIL] {label}: expected {reason}; actual={actual}"

run_cmd Elab.Command.liftCoreM <| assertQuery "InternalTargetProofErased" ``internalTargetRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "InternalCompanionProofErased" ``internalCompanionRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "ProofArgumentBoundary" ``proofArgument "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "AlternativeProofBoundary" ``alternativeArgument "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "ProofFieldBoundary" ``proofField "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "NumericAliasProofBoundary" ``aliasedArgument "reject"
run_cmd Elab.Command.liftCoreM <| assertQuery "TargetProofBoundary" ``forbiddenArgument "forbidden_dependency"
run_cmd Elab.Command.liftCoreM <| assertQuery "CompanionProofBoundary" ``forbiddenCompanion "forbidden_dependency"
run_cmd Elab.Command.liftCoreM <| assertQuery "HiddenStatementBoundary" ``hiddenPayload "reject"
run_cmd Elab.Command.liftCoreM <| assertQuery "ArenaProjectedCarrier" ``arenaCardRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "CatalogProjectedCarrier" ``catalogCarrierRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "BundleProjectedCarrier" ``bundleCarrierRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "ArenaProjectedStatementPayload" ``hiddenArenaRead "reject"
run_cmd Elab.Command.liftCoreM <| assertQuery "NestedScalarCarrier" ``nestedScalarRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "SubtypeScalarCarrier" ``subtypeScalarRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "NativeSubtypePayload" ``nativeSubtypePayload "reject"
run_cmd Elab.Command.liftCoreM <| assertQuery "SubsetMetadataBoundary" ``subsetMetadataRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "ErasedPredicateBoundary" ``erasedPredicateRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "UniformCommutativeRingHeads" ``commutativeRingRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "FunctionInterfacePayload" ``hiddenFunctionInterfaceRead "reject"
run_cmd Elab.Command.liftCoreM <| assertQuery "EquivalenceInterfaceHead" ``equivalenceInterfaceRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "EquivalenceInterfacePayload" ``hiddenEquivalenceInterfaceRead "reject"
run_cmd Elab.Command.liftCoreM <| assertQuery "FunctionInterfaceHead" ``functionInterfaceRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "UniformFieldHeads" ``fieldRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "BoundedNatInterfaceHead" ``boundedNatRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "UniformOrderHeads" ``orderRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "FiniteFunctionRange" ``rangeRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "AppliedCompanionIdentity" ``appliedCompanionRead "forbidden_dependency"
run_cmd Elab.Command.liftCoreM <| assertQuery "UniformMonoidHeads" ``monoidRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "UniformRingHeads" ``ringRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "LocalDefinitionType" ``localRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "UnknownClassSite" ``unknownRead "unclassified_form"
run_cmd Elab.Command.liftCoreM <| assertQuery "ExecutableClassicalChoice" ``classicalRead "unclassified_form"
run_cmd Elab.Command.liftCoreM <| assertQuery "CollectionAppendHeads" ``appendRead "clean"
run_cmd Elab.Command.liftCoreM <| assertQuery "CollectionUnionHead" ``unionRead "clean"

run_cmd Elab.Command.liftCoreM do
  for (label, statement) in [("RegisteredLetAlias", ``letTarget),
      ("RegisteredComputedEquality", ``computedTarget),
      ("RegisteredComputedAlias", ``computedAliasTarget)] do
    let result ← readoutClosure (← getEnv) statement (mkConst ``forbiddenArgument)
    if result.1 then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: {result}"

-- Supported statement spellings also need positive readout controls: replacing
-- recognition with an unclassified stop preserves negative controls but loses
-- a legitimate admission.
run_cmd Elab.Command.liftCoreM do
  for (label, statement) in [("RegisteredLetClean", ``letTarget),
      ("ProjectedStatementClean", ``projectedTarget)] do
    let result ← readoutClosure (← getEnv) statement (mkConst ``plain)
    if !result.1 && result.2.isSome then logInfo m!"[PASS] {label}: {result}"
    else logError m!"[FAIL] {label}: expected witnessed admission; actual={result}"

run_cmd Elab.Command.liftCoreM do
  let actual ← withOptions (·.set `provenanceDefEqLimit (0 : Nat)) <| query "exhausted" ``plain
  let closure ← withOptions (·.set `provenanceDefEqLimit (0 : Nat)) <|
    readoutClosure (← getEnv) ``target (mkConst ``plain)
  if actual.any (·.contains "reason=incomplete_closure provenance=null") && closure == (false, none) then
    logInfo m!"[PASS] NativeExhaustionRouting: {actual}"
  else logError m!"[FAIL] NativeExhaustionRouting: {actual}; closure={closure}"

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let samePredicate ← readoutClosure env ``erasedPredicateTarget (mkConst ``erasedPredicateRead)
  if samePredicate.1 then logInfo "[PASS] ErasedPredicateTarget"
  else logError m!"[FAIL] ErasedPredicateTarget: {samePredicate}"
  let projected ← readoutClosure env ``projectedTarget (mkConst ``forbiddenArgument)
  if projected.1 then logInfo "[PASS] ProjectedStatementAlias"
  else logError m!"[FAIL] ProjectedStatementAlias: {projected}"
  let aliasResult ← readoutClosure env ``aliasTarget (mkConst ``forbiddenArgument)
  if aliasResult.1 then logInfo "[PASS] RegisteredStatementAlias"
  else logError m!"[FAIL] RegisteredStatementAlias: {aliasResult}"
  let (_, first) ← readoutClosure env ``target (mkConst ``proofArgument)
  let (_, second) ← readoutClosure env ``target (mkConst ``alternativeArgument)
  let eraseRoot := fun names => names.filter fun n =>
    n != toString ``proofArgument && n != toString ``alternativeArgument
  if first.map eraseRoot == second.map eraseRoot && first.isSome then
    logInfo "[PASS] ProofImplementationInvariance"
  else logError m!"[FAIL] ProofImplementationInvariance: {first}; {second}"

run_cmd Elab.Command.liftCoreM do
  let mut body := mkConst ``Bool.true
  for _ in [:256] do
    body := .letE `retained (mkConst ``Bool) (mkConst ``Bool.false) body true
  let value := mkLambda `index .default (mkConst ``Unit)
    (mkLambda `state .default (mkConst ``Bool) body)
  let start := (← getTraces).size
  let actual ← withOptions (fun o => (o.set `provenanceDefEqLimit (1 : Nat)).set
      `trace.InformationProvenance.check true) <| readoutClosure (← getEnv) ``target value
  let mut site := false
  for entry in (← getTraces).toArray[start:] do
    let message ← entry.msg.toString
    if message.contains "cause=heartbeat_exhaustion" && message.contains "operation=infer_type" &&
        message.contains "first=readout site=readout" then site := true
  if actual == (false, none) && site then logInfo "[PASS] ActualHeartbeatOperationSite"
  else logError m!"[FAIL] ActualHeartbeatOperationSite: {actual}; site={site}"

run_cmd Elab.Command.liftCoreM do
  let result ← readoutClosure (← getEnv) ``appliedTarget (mkConst ``appliedRead)
  if result.1 then logInfo "[PASS] AppliedTargetIdentity"
  else logError m!"[FAIL] AppliedTargetIdentity: {result}"

-- Inspect elaborated references in the classifier module. String literals,
-- comments, counters and unrelated modules are outside this admission API guard.
-- Native inference internals are not traversed: the owner permits bounded inference.
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames.filter fun name =>
    name == `LeanInformationAudit.ReadoutProvenance ||
      name.toString.startsWith "LeanInformationAudit.ReadoutProvenance."
  if modules.isEmpty then throwError "[FAIL] NoSemanticNormalization: missing classifier module"
  let forbidden := #[`Lean.Meta.isDefEq, `Lean.Meta.whnf,
    `Lean.Meta.unfoldDefinition?, `Lean.MVarId.cases]
  let mut found := false
  for moduleName in modules do
    let some index := env.getModuleIdx? moduleName
      | throwError "[FAIL] NoSemanticNormalization: missing classifier module"
    for name in env.header.moduleData[index]!.constNames do
      let some info := env.find? name | continue
      let some value := info.value? (allowOpaque := true) | continue
      for dependency in value.getUsedConstants do
        if forbidden.contains dependency then
          found := true
          logError m!"[FAIL] NoSemanticNormalization: {name} references {dependency}"
  unless found do logInfo "[PASS] NoSemanticNormalization"
end AllowlistBoundaries

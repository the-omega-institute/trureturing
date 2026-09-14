import LeanInformationAudit.ReadoutProvenance
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Nat

open Lean LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape
namespace AllowlistBoundaries

theorem target : (137 : Nat) = 137 := rfl
theorem harmless : (2 : Nat) ∣ 4 := by norm_num
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
  provenanceErrorCurrent (← getEnv).header.mainModule `catalog ``target holder

-- Independent proof implementations have identical executable meaning. The
-- target proof, generated companion, and nominal statement payload remain barred.
run_cmd Elab.Command.liftCoreM do
  for (label, readout, reason) in [
      ("ProofArgumentBoundary", ``proofArgument, "clean"),
      ("AlternativeProofBoundary", ``alternativeArgument, "clean"),
      ("ProofFieldBoundary", ``proofField, "clean"),
      ("NumericAliasProofBoundary", ``aliasedArgument, "reject"),
      ("TargetProofBoundary", ``forbiddenArgument, "forbidden_dependency"),
      ("CompanionProofBoundary", ``forbiddenCompanion, "forbidden_dependency"),
      ("HiddenStatementBoundary", ``hiddenPayload, "reject"),
      ("UniformMonoidHeads", ``monoidRead, "clean"),
      ("UniformRingHeads", ``ringRead, "clean"),
      ("LocalDefinitionType", ``localRead, "clean"),
      ("UnknownClassSite", ``unknownRead, "unclassified_form"),
      ("ExecutableClassicalChoice", ``classicalRead, "unclassified_form")] do
    let actual ← query label readout
    let ok := if reason == "clean" then actual.isNone
      else if reason == "reject" then actual.isSome
      else actual.any (·.contains s!"reason={reason}")
    if ok then logInfo m!"[PASS] {label}: {actual}"
    else logError m!"[FAIL] {label}: expected {reason}; actual={actual}"

run_cmd Elab.Command.liftCoreM do
  let actual ← withOptions (·.set `provenanceDefEqLimit (0 : Nat)) <| query "exhausted" ``plain
  let closure ← withOptions (·.set `provenanceDefEqLimit (0 : Nat)) <|
    readoutClosure (← getEnv) ``target (mkConst ``plain)
  if actual.any (·.contains "reason=incomplete_closure provenance=null") && closure == (false, none) then
    logInfo m!"[PASS] NativeExhaustionRouting: {actual}"
  else logError m!"[FAIL] NativeExhaustionRouting: {actual}; closure={closure}"

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
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

-- Inspect elaborated references in the classifier module. String literals,
-- comments, counters and unrelated modules are outside this admission API guard.
-- Native inference internals are not traversed: the owner permits bounded inference.
run_cmd do
  let env := (← getEnv).setExporting false
  let some index := env.getModuleIdx? `LeanInformationAudit.ReadoutProvenance
    | throwError "[FAIL] NoSemanticNormalization: missing classifier module"
  let forbidden := #[`Lean.Meta.isDefEq, `Lean.Meta.whnf,
    `Lean.Meta.unfoldDefinition?, `Lean.MVarId.cases]
  let mut found := false
  for name in env.header.moduleData[index]!.constNames do
    let some info := env.find? name | continue
    let some value := info.value? (allowOpaque := true) | continue
    for dependency in value.getUsedConstants do
      if forbidden.contains dependency then
        found := true
        logError m!"[FAIL] NoSemanticNormalization: {name} references {dependency}"
  unless found do logInfo "[PASS] NoSemanticNormalization"
end AllowlistBoundaries

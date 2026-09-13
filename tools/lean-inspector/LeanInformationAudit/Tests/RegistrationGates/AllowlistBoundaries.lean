import LeanInformationAudit.ReadoutProvenance
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Nat

open Lean LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape
namespace AllowlistBoundaries

theorem target : (137 : Nat) = 137 := rfl
theorem harmless : (2 : Nat) ∣ 4 := by norm_num
theorem alternative : (2 : Nat) ∣ 4 := ⟨2, rfl⟩
def keep {p : Prop} (_ : p) (x : Bool) : Bool := x
def plain (_ : Unit) (state : Bool) : Bool := state
def proofArgument (_ : Unit) (state : Bool) : Bool := keep harmless state
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

-- This guard is intentionally scoped to the production classifier. Bounded
-- native inference may implement reduction internally; admission must never
-- invoke semantic comparison or normalization as a separate decision procedure.
run_cmd do
  let source ← IO.FS.readFile "tools/lean-inspector/LeanInformationAudit/ReadoutProvenance.lean"
  for operation in ["Meta.isDefEq", "Meta.whnf", "Meta.unfoldDefinition?", ".mvarId!.cases"] do
    if source.contains operation then logError m!"[FAIL] NoSemanticNormalization: {operation}"
  if !["Meta.isDefEq", "Meta.whnf", "Meta.unfoldDefinition?", ".mvarId!.cases"].any (fun operation => source.contains operation) then
    logInfo "[PASS] NoSemanticNormalization"
end AllowlistBoundaries

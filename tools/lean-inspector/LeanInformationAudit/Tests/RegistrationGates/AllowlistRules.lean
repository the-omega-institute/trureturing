import LeanInformationAudit.ReadoutProvenance
import LeanInformationAudit.SealCommand
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Logic.Equiv.Defs

open Lean LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape

namespace AllowlistRules

def signature : PrimitiveSignature.{0, 0, 0} Bool where
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

def cleanRead (_ : Unit) (x : Bool) : Bool := x
def template : PrimitiveRealization signature := ⟨cleanRead, Fin.elim0⟩
theorem target : (137 : Nat) = 137 := rfl
theorem independentProof : (137 : Nat) = 137 := rfl
theorem otherTarget : (139 : Nat) = 139 := rfl
def keepProof {p : Prop} (_ : p) (x : Bool) : Bool := x
def theoremRead (_ : Unit) (x : Bool) : Bool := keepProof target x
def independentProofRead (_ : Unit) (x : Bool) : Bool := keepProof independentProof x
def binderRead (_ : Unit) (x : Bool) : Bool := let _ : (137 : Nat) = 137 := rfl; x
def ctorRead (_ : Unit) (x : Bool) : Bool :=
  if @decide ((137 : Nat) = 137) (.isTrue rfl) then x else false

set_option linter.style.nameCheck false in
def generated.__information_unit : Bool := true
def generatedRead (_ : Unit) (x : Bool) : Bool := cond generated.__information_unit x false

def payloadProjectionRead (_ : Unit) (x : Bool) : Bool :=
  let _ := fun payload : LeanInformationAudit.SealedOccurrenceState => payload.theoremName
  x

noncomputable def classicalRead (_ : Unit) (x : Bool) : Bool :=
  if @decide (x = true) (Classical.propDecidable _) then x else false
noncomputable def payloadRead := classicalRead
noncomputable def typeBeforeClassicalRead (_ : Unit) (x : Bool) : Bool :=
  let _ : Classical.propDecidable = Classical.propDecidable := rfl
  if @decide (x = true) (Classical.propDecidable _) then x else false
noncomputable def bothRead (_ : Unit) (x : Bool) : Bool :=
  let _ := Classical.propDecidable
  keepProof target x

def unlistedRead (_ : Unit) (x : Bool) : Bool :=
  let d : DecidableEq Bool :=
    Function.Injective.decidableEq (f := fun b : Bool => b) (fun _ _ h => h)
  if @decide (x = true) (d x true) then x else false
def equivRead (_ : Unit) (x : Bool) : Bool :=
  if @decide (x = true) ((Equiv.refl Bool).decidableEq x true) then x else false

def subtermRead (_ : Unit) (x : Bool) : Bool :=
  let _ : Option (PLift ((137 : Nat) = 137)) := none
  x
def mentioningTypeRead (_ : Unit) (x : Bool) : Bool :=
  let _ : Option (Option (PLift ((137 : Nat) = 137))) := none
  x
def closedProp : Prop := (138 : Nat) = 138
def closedDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide closedProp (inferInstanceAs (Decidable ((138 : Nat) = 138))) then x else false
def closedBinderRead (_ : Unit) (x : Bool) : Bool := let _ : closedProp := rfl; x

def closedTypeRead (_ : Unit) (x : Bool) : Bool :=
  let _ : DecidableEq signature.Index := inferInstanceAs (DecidableEq Unit)
  x
def predicate (a b : Bool) : Prop := a = b
def predicateRead (_ : Unit) (x : Bool) : Bool :=
  let _ := predicate
  let _ := predicate true
  x
def externalPropRead (_ : Unit) (x : Bool) : Bool :=
  if decide ((0 : Nat) < 24) then x else false
inductive Direction where | left | right
def constructorPropRead (_ : Unit) (x : Bool) : Bool :=
  if @decide (Direction.left = Direction.left) (.isTrue rfl) then x else false

def memoRelay (_ : Unit) (x : Bool) : Bool := keepProof target x
def memoFirst (_ : Unit) (x : Bool) : Bool := memoRelay () x
def memoSecond (_ : Unit) (x : Bool) : Bool := memoRelay () x

-- A separate compilation unit keeps one rejected fixture from hiding other
-- mutation results behind a failed import. The registration integration
-- fixtures exercise the finite and structural command paths separately.
private def check (label : String) (readout theoremName : Name) (reason : String)
    (formClass : String := "") : CoreM Unit := do
  let env ← getEnv
  let some (.defnInfo info) := env.find? ``template | throwError "template missing"
  let holder := readout.str "fixtureRealization"
  addDecl <| .defnDecl {
    name := holder, levelParams := [], type := info.type
    value := info.value.replace fun e => if e == mkConst ``cleanRead then some (mkConst readout) else none
    hints := .abbrev, safety := .safe }
  let actual ← provenanceErrorCurrent env.header.mainModule `catalog theoremName holder
  if reason == "clean" then
    unless actual.isNone do throwError "expected clean, got {actual}"
  else
    let some message := actual | throwError "missing {reason} diagnostic"
    let tokens := message.splitOn " "
    unless tokens.length == 6 && tokens[0]! == "IE-C050" &&
        tokens[1]! == "ClosedTruthReadout" && tokens[2]!.startsWith "key=" &&
        tokens[3]! == s!"readout={readout}" && tokens[4]! == s!"reason={reason}" &&
        tokens[5]!.startsWith "provenance=" do
      throwError "expected six tokens and reason={reason}, got {message}"
    let .ok payload := Json.parse ((message.splitOn " provenance=").getLast!)
      | throwError "invalid JSON"
    if reason == "unclassified_form" then
      let .obj fields := payload | throwError "expected an object"
      unless (fields.toList.map Prod.fst).toArray == #["class", "first", "namespace", "site", "walked"] do
        throwError "wrong payload keys"
      unless formClass.isEmpty || payload.getObjValAs? String "class" == .ok formClass do
        throwError "wrong class: {payload}"
      let .ok names := payload.getObjValAs? (Array String) "walked" | throwError "invalid walked names"
      unless names == names.qsort (· < ·) && names.toList.eraseDups.length == names.size do
        throwError "noncanonical walked names"
    else if reason == "forbidden_dependency" then
      let .ok names := fromJson? (α := Array String) payload | throwError "expected an array"
      unless names == names.qsort (· < ·) && names.toList.eraseDups.length == names.size do
        throwError "noncanonical closure"
    else unless payload == Json.null do throwError "incomplete payload must be null"
  logInfo m!"[PASS] {label}"

run_cmd Elab.Command.liftCoreM do
  let cases : Array (String × Name × String × String) := #[
    ("CleanReadout", ``cleanRead, "clean", ""),
    ("TheoremTruth", ``theoremRead, "forbidden_dependency", ""),
    ("IndependentProofConstant", ``independentProofRead, "forbidden_dependency", ""),
    ("ClosedStatementInhabitant", ``binderRead, "forbidden_dependency", ""),
    ("CtorDecisionOfStatement", ``ctorRead, "forbidden_dependency", ""),
    ("JudgeGeneratedCompanions", ``generatedRead, "forbidden_dependency", ""),
    ("JudgePayloadParameterProjection", ``payloadProjectionRead, "forbidden_dependency", ""),
    ("ClassicalDirect", ``classicalRead, "unclassified_form", "classical_choice"),
    ("TypeBeforeClassicalData", ``typeBeforeClassicalRead, "unclassified_form", "classical_choice"),
    ("UnclassifiedPayloadParses", ``payloadRead, "unclassified_form", "classical_choice"),
    ("ForbiddenWinsOverUnclassified", ``bothRead, "forbidden_dependency", ""),
    ("UnlistedProducer", ``unlistedRead, "unclassified_form", "unlisted_decision_producer"),
    ("EquivDecidableEqAdmitted", ``equivRead, "clean", ""),
    ("StatementSubterm", ``subtermRead, "unclassified_form", ""),
    ("StatementMentioningType", ``mentioningTypeRead, "unclassified_form", ""),
    ("ClosedDecisionProtected", ``closedDecisionRead, "unclassified_form", "closed_decision"),
    ("ClosedDecisionBinderProtected", ``closedBinderRead, "unclassified_form", "closed_decision"),
    ("ClosedTypeArgumentAdmitted", ``closedTypeRead, "clean", ""),
    ("ClosedPredicateArgumentAdmitted", ``predicateRead, "clean", ""),
    ("ExternalClosedPropAdmitted", ``externalPropRead, "clean", ""),
    ("ConstructorClosedDecisionAdmitted", ``constructorPropRead, "clean", "")]
  for (label, readout, reason, formClass) in cases do
    try check label readout ``target reason formClass
    catch ex => logError m!"[FAIL] {label}: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  let actual ← readoutClosure (← getEnv) ``target (mkConst ``cleanRead)
  unless actual == (false, some #["AllowlistRules.cleanRead", "Bool", "Unit"]) do
    throwError "[FAIL] ExternalLeafNotTraversed: {repr actual}"
  logInfo "[PASS] ExternalLeafNotTraversed"

run_cmd Elab.Command.liftCoreM do
  check "MemoPrimeDifferentStatement" ``memoFirst ``otherTarget "clean"
  try
    check "MemoRechecksStatement" ``memoSecond ``target "forbidden_dependency"
    let counters ← getProvenanceCounters
    unless counters.memoHits > 0 && counters.summarisedConstants <= 1 do
      throwError "no shared summary reuse: {repr counters}"
    logInfo "[PASS] MemoReuseAcrossRegistrations"
  catch ex => logError m!"[FAIL] MemoReuseAcrossRegistrations: {ex.toMessageData}"

-- The public query remains usable without a MetaM interpreter.
example : Environment → Name → Expr → CoreM (Bool × Option (Array String)) := readoutClosure

-- Keep the proof inline: elaborating a source definition can outline it into
-- a proof constant, which lets E2 mask deletion of the E4/E5 shape guards.
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let some targetInfo := env.find? ``target | throwError "target missing"
  let some proof := targetInfo.value? (allowOpaque := true) | throwError "target proof missing"
  let some (.defnInfo templateInfo) := env.find? ``template | throwError "template missing"
  let bodies := #[
    ("InlineClosedStatementInhabitant",
      Expr.letE `evidence targetInfo.type proof (mkConst ``Bool.true) true),
    ("InlineCtorDecisionOfStatement",
      mkAppN (mkConst ``Decidable.decide) #[targetInfo.type,
        mkAppN (mkConst ``Decidable.isTrue) #[targetInfo.type, proof]])]
  for (label, body) in bodies do
    try
      let readout := mkLambda `index .default (mkConst ``Unit)
        (mkLambda `state .default (mkConst ``Bool) body)
      let holder := `AllowlistRules |>.str label
      addDecl <| .defnDecl {
        name := holder, levelParams := [], type := templateInfo.type
        value := templateInfo.value.replace fun e =>
          if e == mkConst ``cleanRead then some readout else none
        hints := .abbrev, safety := .safe }
      let actual ← provenanceErrorCurrent env.header.mainModule `catalog ``target holder
      let some message := actual | throwError "missing forbidden diagnostic"
      unless (message.splitOn " ")[4]? == some "reason=forbidden_dependency" do
        throwError "expected forbidden_dependency, got {message}"
      logInfo m!"[PASS] {label}"
    catch ex => logError m!"[FAIL] {label}: {ex.toMessageData}"

end AllowlistRules

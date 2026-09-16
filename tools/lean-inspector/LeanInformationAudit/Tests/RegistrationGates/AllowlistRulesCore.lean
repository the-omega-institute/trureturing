import LeanInformationAudit.ReadoutProvenance
import LeanInformationAudit.SealCommand
import LeanInformationAudit.StructuralRealization
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Logic.Equiv.Defs
import LeanInformationAuditAnalysis.Tests.AllowlistSources
import LeanInformationAuditAnalysis.Tests.ExternalAllowlistTypes

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
structure StatementBox where
  evidence : PLift ((137 : Nat) = 137)
  bit : Bool
def constructorSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := PLift ((137 : Nat) = 137)
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => StatementBox
def constructorRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ constructorSignature := ⟨StatementBox.mk⟩
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
    (formClass : String := "") (first : String := "") (ns : String := "")
    (site : String := "") : CoreM Unit := do
  let env ← getEnv
  let some (.defnInfo info) := env.find? ``template | throwError "template missing"
  -- Keep each fixture declaration unique even when a readout is exercised by
  -- more than one assertion below.
  let holder := `AllowlistRules |>.str s!"{label}.fixtureRealization"
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
      for (key, expected) in [("first", first), ("namespace", ns), ("site", site)] do
        unless expected.isEmpty || payload.getObjValAs? String key == .ok expected do
          throwError "wrong {key}: expected {expected}, got {payload}"
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
    ("ImportedLibraryPrivateProof", ``ImportedAllowlistSources.proofRead, "forbidden_dependency", ""),
    ("ImportedLibraryCleanData", ``ImportedAllowlistSources.cleanRead, "clean", ""),
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
    ("StatementSubterm", ``subtermRead, "unclassified_form", ""),
    ("StatementMentioningType", ``mentioningTypeRead, "unclassified_form", ""),
    ("ClosedDecisionProtected", ``closedDecisionRead, "unclassified_form", "closed_decision"),
    ("ClosedDecisionBinderProtected", ``closedBinderRead, "unclassified_form", "closed_decision"),
    ("ClosedTypeArgumentAdmitted", ``closedTypeRead, "clean", ""),
    ("ClosedPredicateArgumentAdmitted", ``predicateRead, "clean", "")]
  for (label, readout, reason, formClass) in cases do
    try check label readout ``target reason formClass
    catch ex => logError m!"[FAIL] {label}: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  try
    check "CurrentClosedDecisionPayload" ``closedDecisionRead ``target "unclassified_form"
      "closed_decision" "AllowlistRules.closedProp" "protected:current" "AllowlistRules.closedDecisionRead"
  catch ex => logError m!"[FAIL] CurrentClosedDecisionPayload: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  try
    let env ← getEnv
    let some (.defnInfo templateInfo) := env.find? ``template | throwError "template missing"
    let some (.defnInfo readoutInfo) := env.find? ``classicalRead | throwError "readout missing"
    let holder := `AllowlistRules.inlineClassicalRealization
    addDecl <| .defnDecl {
      name := holder, levelParams := [], type := templateInfo.type
      value := templateInfo.value.replace fun e =>
        if e == mkConst ``cleanRead then some readoutInfo.value else none
      hints := .abbrev, safety := .safe }
    let some message ← provenanceErrorCurrent env.header.mainModule `catalog ``target holder
      | throwError "missing diagnostic"
    let .ok payload := Json.parse ((message.splitOn " provenance=").getLast!)
      | throwError "invalid payload"
    unless (message.splitOn " ")[3]? == some s!"readout={holder}" &&
        payload.getObjValAs? String "first" == .ok "Classical.propDecidable" &&
        payload.getObjValAs? String "namespace" == .ok "external:Classical" &&
        payload.getObjValAs? String "site" == .ok holder.toString do
      throwError "wrong inline payload: {message}"
    logInfo "[PASS] InlineReadoutPayloadAddress"
  catch ex => logError m!"[FAIL] InlineReadoutPayloadAddress: {ex.toMessageData}"

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

run_cmd Elab.Command.liftCoreM do
  let label := "ValuelessConstructorDeclaredType"
  try
    let actual ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
      ``target ``constructorRealization
    let some message := actual | throwError "missing declared-type diagnostic"
    unless (message.splitOn " ")[4]? == some "reason=unclassified_form" do
      throwError "expected unclassified_form, got {message}"
    let .ok payload := Json.parse ((message.splitOn " provenance=").getLast!)
      | throwError "invalid payload"
    unless payload.getObjValAs? String "class" == .ok "statement_mentioning_type" do
      throwError "expected statement_mentioning_type, got {payload}"
    logInfo m!"[PASS] {label}"
  catch ex => logError m!"[FAIL] {label}: {ex.toMessageData}"

class StatementEvidence (p : Prop) : Type where
  proof : p
instance {p : Prop} : Subsingleton (StatementEvidence p) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

def statementAlias : Prop := (137 : Nat) = 137
inductive AliasInstanceBox where
  | mk [StatementEvidence statementAlias] (bit : Bool) : AliasInstanceBox
def aliasSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := StatementEvidence statementAlias
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => AliasInstanceBox
def aliasRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ aliasSignature := ⟨@AliasInstanceBox.mk⟩
def etaReadout (evidence : StatementEvidence ((137 : Nat) = 137))
    (bit : Bool) : AliasInstanceBox := @AliasInstanceBox.mk evidence bit

protected def hiddenStatement : Prop := (137 : Nat) = 137
structure Box where
  evidence : PLift AllowlistRules.hiddenStatement
  bit : Bool
def hiddenSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := PLift AllowlistRules.hiddenStatement
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => Box
def hiddenRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ hiddenSignature := ⟨Box.mk⟩

inductive DecidableAliasBox where
  | mk [Decidable statementAlias] (bit : Bool) : DecidableAliasBox
def decidableAliasSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Decidable statementAlias
  indexFintype := Fintype.ofSubsingleton (.isTrue rfl)
  Output := fun _ => DecidableAliasBox
def decidableAliasRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ decidableAliasSignature := ⟨@DecidableAliasBox.mk⟩

structure EvidenceBox : Type where
  evidence : (137 : Nat) = 137
instance : Subsingleton EvidenceBox := ⟨fun a b => by cases a; cases b; rfl⟩
inductive NestedBox where
  | mk (evidence : EvidenceBox) (bit : Bool) : NestedBox
def nestedSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := EvidenceBox
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => NestedBox
def nestedRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ nestedSignature := ⟨NestedBox.mk⟩

inductive GenericBox (α : Type) where
  | mk (evidence : α) (bit : Bool) : GenericBox α
def genericSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := EvidenceBox
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => GenericBox EvidenceBox
-- Inline specialization: a named readout would expose its instantiated type.
def genericRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ genericSignature := ⟨@GenericBox.mk EvidenceBox⟩

abbrev EvidenceAlias : Type := ULift (PLift statementAlias)
inductive TypeAliasBox where
  | mk (evidence : EvidenceAlias) (bit : Bool) : TypeAliasBox
def typeAliasSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := EvidenceAlias
  indexFintype := Fintype.ofSubsingleton ⟨⟨rfl⟩⟩
  Output := fun _ => TypeAliasBox
def typeAliasRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ typeAliasSignature := ⟨TypeAliasBox.mk⟩

abbrev UnknownAlias : Type := StatementEvidence ((138 : Nat) = 138)
inductive UnknownAliasBox where
  | mk [UnknownAlias] (bit : Bool) : UnknownAliasBox
def unknownAliasSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := UnknownAlias
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => UnknownAliasBox
def unknownAliasRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ unknownAliasSignature := ⟨@UnknownAliasBox.mk⟩

def Ghost : Type := let _ := independentProof; Unit
structure GhostRecord : Type where
  ghost : Ghost
instance : Subsingleton GhostRecord := ⟨fun ⟨a⟩ ⟨b⟩ => by
  have h : a = b := @Subsingleton.elim Unit inferInstance a b
  cases h
  rfl⟩
inductive GhostBox where
  | mk (evidence : GhostRecord) (bit : Bool) : GhostBox
def ghostSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := GhostRecord
  indexFintype := Fintype.ofSubsingleton ⟨()⟩
  Output := fun _ => GhostBox
def ghostRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ ghostSignature := ⟨GhostBox.mk⟩

def externalValuedSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := PLift ((137 : Nat) = 137)
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => Bool
def externalValuedRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ externalValuedSignature := ⟨ExternalAllowlistTypes.typedRead⟩
instance : Subsingleton ExternalAllowlistTypes.PredicateRecord :=
  ⟨fun ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ => rfl⟩
def externalPredicateSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := ExternalAllowlistTypes.PredicateRecord
  indexFintype := Fintype.ofSubsingleton ⟨⟨⟨(), rfl⟩⟩⟩
  Output := fun _ => ExternalAllowlistTypes.PredicateBox
def externalPredicateRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ externalPredicateSignature := ⟨ExternalAllowlistTypes.PredicateBox.mk⟩

def proofIndexedSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ExternalAllowlistTypes.ProofIndexed rfl
def proofIndexedRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ proofIndexedSignature := ⟨ExternalAllowlistTypes.ProofIndexed.mk⟩

def quotientAliasSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Quot ExternalAllowlistTypes.hiddenRelation
  indexFintype := Fintype.ofSubsingleton (Quot.mk _ ())
  Output := fun _ => ExternalAllowlistTypes.QuotientBox
def quotientAliasRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ quotientAliasSignature := ⟨ExternalAllowlistTypes.QuotientBox.mk⟩
def cleanQuotientSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Quot ExternalAllowlistTypes.cleanRelation
  indexFintype := Fintype.ofSubsingleton (Quot.mk _ ())
  Output := fun _ => ExternalAllowlistTypes.CleanQuotientBox
def cleanQuotientRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ cleanQuotientSignature := ⟨ExternalAllowlistTypes.CleanQuotientBox.mk⟩

def nestedProductSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Bool × Bool × Bool
  indexFintype := inferInstance
  Output := fun _ => GenericBox (Bool × Bool × Bool)
def nestedProductRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ nestedProductSignature := ⟨GenericBox.mk⟩

instance : Subsingleton ExternalAllowlistTypes.IndexRecord :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by cases a; cases b; rfl⟩
def hiddenIndexSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := ExternalAllowlistTypes.IndexRecord
  indexFintype := Fintype.ofSubsingleton ⟨.mk⟩
  Output := fun _ => ExternalAllowlistTypes.IndexBox
def hiddenIndexRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ hiddenIndexSignature := ⟨ExternalAllowlistTypes.IndexBox.mk⟩

def specializedProjectionSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ExternalAllowlistTypes.SpecializedProjectionBox
def specializedProjectionRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ specializedProjectionSignature :=
  ⟨ExternalAllowlistTypes.SpecializedProjectionBox.mk (f := ExternalAllowlistTypes.unitCarrier)⟩

-- Matched clean controls for the guards above.  These use the same valueless
-- constructor shape while carrying only listed classes or harmless propositions.
inductive CleanInstanceBox where
  | mk [Inhabited Unit] (bit : Bool) : CleanInstanceBox
instance : Subsingleton (Inhabited Unit) :=
  ⟨fun a b => by cases a; cases b; rfl⟩
def cleanInstanceSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Inhabited Unit
  indexFintype := Fintype.ofSubsingleton inferInstance
  Output := fun _ => CleanInstanceBox
def cleanInstanceRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ cleanInstanceSignature := ⟨@CleanInstanceBox.mk⟩

-- Alias-shaped counterpart for the instance-through-alias guard.  The alias
-- expands to the listed `Inhabited` class and carries no statement evidence.
abbrev CleanInstanceAlias : Type := Inhabited Unit
inductive CleanAliasInstanceBox where
  | mk [CleanInstanceAlias] (bit : Bool) : CleanAliasInstanceBox
def cleanAliasInstanceSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := CleanInstanceAlias
  indexFintype := Fintype.ofSubsingleton inferInstance
  Output := fun _ => CleanAliasInstanceBox
def cleanAliasInstanceRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ cleanAliasInstanceSignature := ⟨@CleanAliasInstanceBox.mk⟩

protected def harmlessStatement : Prop := True
structure HarmlessPLiftBox where
  evidence : PLift AllowlistRules.harmlessStatement
  bit : Bool
def harmlessPLiftSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := PLift AllowlistRules.harmlessStatement
  indexFintype := Fintype.ofSubsingleton ⟨True.intro⟩
  Output := fun _ => HarmlessPLiftBox
def harmlessPLiftRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ harmlessPLiftSignature := ⟨HarmlessPLiftBox.mk⟩

-- Protected proposition alias counterpart for the PLift declared-type guard.
abbrev HarmlessProtectedAlias : Type := PLift True
structure HarmlessProtectedAliasBox where
  evidence : HarmlessProtectedAlias
  bit : Bool
def harmlessProtectedAliasSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := HarmlessProtectedAlias
  indexFintype := Fintype.ofSubsingleton ⟨True.intro⟩
  Output := fun _ => HarmlessProtectedAliasBox
def harmlessProtectedAliasRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ harmlessProtectedAliasSignature := ⟨HarmlessProtectedAliasBox.mk⟩

inductive CleanDecidableBox where
  | mk [Decidable True] (bit : Bool) : CleanDecidableBox
def cleanDecidableSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Decidable True
  indexFintype := Fintype.ofSubsingleton (.isTrue trivial)
  Output := fun _ => CleanDecidableBox
def cleanDecidableRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ cleanDecidableSignature := ⟨@CleanDecidableBox.mk⟩

-- Alias-shaped counterpart for the decidability-through-alias guard.
abbrev CleanDecidableAlias : Type := Decidable True
inductive CleanAliasDecidableBox where
  | mk [CleanDecidableAlias] (bit : Bool) : CleanAliasDecidableBox
def cleanAliasDecidableSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := CleanDecidableAlias
  indexFintype := Fintype.ofSubsingleton (.isTrue trivial)
  Output := fun _ => CleanAliasDecidableBox
def cleanAliasDecidableRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ cleanAliasDecidableSignature := ⟨@CleanAliasDecidableBox.mk⟩

-- A deep type comparison for the positive-budget exhaustion check.
-- The recursive family forces definitional equality to unfold 256 layers;
-- setting a finite heartbeat budget below that work must produce the same
-- fail-closed diagnostic, with Lean's heartbeat exception tag preserved.
def DeepType : Nat → Type
  | 0 => Bool
  | n + 1 => Prod (DeepType n) Bool
def deepValue : (n : Nat) → DeepType n
  | 0 => false
  | n + 1 => (deepValue n, false)
def defeqExhaustionRead (_ : Unit) (x : Bool) : Bool :=
  let _ : DeepType 256 := deepValue 256
  x

elab "raw_payload_name" value:term : term => do
  let value ← Elab.Term.elabTerm value (some (mkConst ``LeanInformationAudit.SealedOccurrenceState))
  let some projection := (← getEnv).getProjectionFnInfo? ``LeanInformationAudit.SealedOccurrenceState.theoremName
    | throwError "missing payload projection"
  return .proj ``LeanInformationAudit.SealedOccurrenceState projection.i value

def tagCarrier (_ : Name) : Type := Unit
structure SyntheticProjectionField : Type where
  tag : ∀ payload : LeanInformationAudit.SealedOccurrenceState, tagCarrier (raw_payload_name payload)
instance : Subsingleton SyntheticProjectionField := ⟨fun ⟨a⟩ ⟨b⟩ => by
  have h : a = b := funext (fun _ => @Subsingleton.elim Unit inferInstance _ _)
  cases h
  rfl⟩
inductive SyntheticProjectionBox where
  | mk (evidence : SyntheticProjectionField) (bit : Bool) : SyntheticProjectionBox
def syntheticProjectionSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := SyntheticProjectionField
  indexFintype := Fintype.ofSubsingleton ⟨fun _ => ()⟩
  Output := fun _ => SyntheticProjectionBox
def syntheticProjectionRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ syntheticProjectionSignature := ⟨SyntheticProjectionBox.mk⟩

structure PlainPayload where
  index : Unit
  bit : Bool
def plainSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => PlainPayload
def plainRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ plainSignature := ⟨PlainPayload.mk⟩
def plainProjectionRead (_ : Unit) (x : Bool) : Bool :=
  let payload : PlainPayload := ⟨(), x⟩
  let aliased := payload
  aliased.bit
noncomputable def classicalTypeOnlyRead (_ : Unit) (x : Bool) : Bool :=
  let _ := fun (_ : Classical.propDecidable = Classical.propDecidable) => x
  x

run_cmd Elab.Command.liftTermElabM do
  let targetType := (← getConstInfo ``target).type
  unless ← Meta.isDefEq (mkConst ``statementAlias) targetType do
    throwError "[FAIL] AliasDeclaredTypeShape: alias differs from statement"
  unless ← Meta.isDefEq (mkConst ``etaReadout) (mkConst ``AliasInstanceBox.mk) do
    throwError "[FAIL] AliasDeclaredTypeShape: eta readout differs from constructor"
  for name in [``AliasInstanceBox.mk, ``Box.mk, ``DecidableAliasBox.mk] do
    unless (← getConstInfo name).value?.isNone do
      throwError "[FAIL] AliasDeclaredTypeShape: {name} has a value"
  logInfo "[PASS] AliasDeclaredTypeShape"
  for (label, holder) in [
      ("InstanceTypeThroughAlias", ``aliasRealization),
      ("ProtectedPLiftDeclaredType", ``hiddenRealization),
      ("DecidableTypeThroughAlias", ``decidableAliasRealization),
      ("NestedValuelessRecordType", ``nestedRealization),
      ("InlineGenericConstructorType", ``genericRealization),
      ("TypeAliasThroughULift", ``typeAliasRealization),
      ("UnknownClassTypeAlias", ``unknownAliasRealization),
      ("NestedTypeAliasProvenance", ``ghostRealization),
      ("ExternalValuedDeclaredType", ``externalValuedRealization),
      ("ExternalPredicateConstructorDomain", ``externalPredicateRealization),
      ("SyntheticProjectionType", ``syntheticProjectionRealization),
      ("ExternalProofIndexType", ``proofIndexedRealization),
      ("SyntheticDeclaredKind", ``hiddenIndexRealization),
      ("SpecializedProjectionReceiver", ``specializedProjectionRealization),
      ("QuotientPredicateAlias", ``quotientAliasRealization)] do
    let actual ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog ``target holder
    match actual with
    | some message =>
      if message.startsWith "IE-C050 ClosedTruthReadout " &&
          #["reason=unclassified_form", "reason=forbidden_dependency"].contains
            ((message.splitOn " ")[4]?.getD "") then
        logInfo m!"[PASS] {label}: {message}"
      else logError m!"[FAIL] {label}: unexpected diagnostic {message}"
    | none => logError m!"[FAIL] {label}: false admission; missing IE-C050"

run_cmd Elab.Command.liftTermElabM do
  -- Preserve ordinary projection-function application in the actual Expr.
  -- No Expr.proj or payload constructor can mask the constant dispatch guard.
  let getter := mkLambda `payload .default (mkConst ``LeanInformationAudit.SealedOccurrenceState)
    (mkApp (mkConst ``LeanInformationAudit.SealedOccurrenceState.theoremName) (.bvar 0))
  let readout := mkLambda `index .default (mkConst ``Unit)
    (mkLambda `state .default (mkConst ``Bool)
      (Expr.letE `getter (← Meta.inferType getter) getter (.bvar 1) true))
  Meta.check readout
  unless (readout.find? (fun e => match e with | .proj .. => true | _ => false)).isNone do
    throwError "[FAIL] ProjectionFunctionShape: unexpected Expr.proj"
  logInfo "[PASS] ProjectionFunctionShape: ordinary const application; well typed"
  let readoutName := `AllowlistRules.explicitProjectionRead
  addDecl <| .defnDecl {
    name := readoutName, levelParams := [], type := ← Meta.inferType readout
    value := readout, hints := .abbrev, safety := .safe }
  try check "JudgeProjectionFunctionApplication" readoutName ``target "forbidden_dependency"
  catch ex => logError m!"[FAIL] JudgeProjectionFunctionApplication: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  let actual ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``target ``plainRealization
  if actual.isNone then logInfo "[PASS] ValuelessCleanCounterpart"
  else logError m!"[FAIL] ValuelessCleanCounterpart: {actual}"
  let product ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``target ``nestedProductRealization
  if product.isNone then logInfo "[PASS] ValuelessNestedProductCounterpart"
  else logError m!"[FAIL] ValuelessNestedProductCounterpart: {product}"
  for (label, readout) in [
      ("ClassicalTypeOnlyCounterpart", ``classicalTypeOnlyRead),
      ("PlainProjectionCounterpart", ``plainProjectionRead)] do
    try check label readout ``target "clean"
    catch ex => logError m!"[FAIL] {label}: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  for (label, realizationName) in [
      ("InstanceTypeCleanCounterpart", ``cleanInstanceRealization),
      ("InstanceTypeAliasCleanCounterpart", ``cleanAliasInstanceRealization),
      ("ProtectedPLiftCleanCounterpart", ``harmlessPLiftRealization),
      ("ProtectedPLiftAliasCleanCounterpart", ``harmlessProtectedAliasRealization),
      ("DecidableTypeAliasCleanCounterpart", ``cleanAliasDecidableRealization),
      ("DecidableTypeCleanCounterpart", ``cleanDecidableRealization)] do
    try
      let actual ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
        ``target realizationName
      unless actual.isNone do
        throwError "expected clean, got {actual}"
      logInfo m!"[PASS] {label}"
    catch ex => logError m!"[FAIL] {label}: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  try
    withOptions (·.set `provenanceDefEqLimit (0 : Nat)) <|
      check "DefeqBudgetExhaustion" ``cleanRead ``target "incomplete_closure"
  catch ex => logError m!"[FAIL] DefeqBudgetExhaustion: {ex.toMessageData}"

run_cmd Elab.Command.liftCoreM do
  try
    withOptions (·.set `provenanceDefEqLimit (1000 : Nat)) <|
      check "ComputedTypeWithoutDefeq" ``defeqExhaustionRead ``target "clean"
  catch ex => logError m!"[FAIL] DefeqBudgetRealExhaustion: {ex.toMessageData}"

-- Pending constants have declaration identity only. Occurrence metadata belongs
-- to the separate type obligations, where it is consumed by diagnostics.
run_cmd Elab.Command.liftTermElabM do
  let info ← getConstInfo ``WalkState.pending
  Meta.forallTelescope info.type fun _ result => do
    let hasName := result.find? (fun e => e == mkConst ``Name) |>.isSome
    let hasOccurrenceMetadata := result.find? (fun e =>
      e == mkConst ``Expr || e == mkConst ``Bool) |>.isSome
    unless hasName && !hasOccurrenceMetadata do
      throwError "[FAIL] PendingConstantNames: queue retains unused occurrence metadata"
  logInfo "[PASS] PendingConstantNames"

end AllowlistRules
namespace AllowlistAttempt8Fixtures
open Lean LeanInformationAudit.RegistrationGates

universe u
inductive UniverseBox where
  | mk (_ : PLift (∀ α : Sort u, α = α)) (_ : Bool) : UniverseBox

theorem universeTarget : ∀ α : Type, α = α := by intro α; rfl

def universeBoxSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := PLift (∀ α : Type, α = α)
  indexFintype := Fintype.ofSubsingleton ⟨by intro α; rfl⟩
  Output := fun _ => UniverseBox.{1}

def universeBoxRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ universeBoxSignature := ⟨UniverseBox.mk⟩

def unknownValuedSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := ExternalAllowlistTypes.UnknownEvidence
  indexFintype := Fintype.ofSubsingleton ⟨rfl⟩
  Output := fun _ => Bool

def unknownValuedRealization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ unknownValuedSignature := ⟨@ExternalAllowlistTypes.valuedUnknown⟩

def hiddenIndexAttempt8Signature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := ExternalAllowlistTypes.IndexRecord
  indexFintype := Fintype.ofSubsingleton ⟨.mk⟩
  Output := fun _ => ExternalAllowlistTypes.IndexBox

def hiddenIndexAttempt8Realization : LeanInformationAudit.StructuralPrimitiveRealization
    ⟨Bool⟩ hiddenIndexAttempt8Signature := ⟨ExternalAllowlistTypes.IndexBox.mk⟩

private def expectDiagnostic (label : String) (theoremName realizationName : Name) : CoreM Unit := do
  let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog theoremName realizationName
  let some message := result | throwError m!"[FAIL] {label}: missing IE-C050 diagnostic"
  unless message.startsWith "IE-C050 ClosedTruthReadout " do
    throwError m!"[FAIL] {label}: unexpected diagnostic {message}"
  logInfo m!"[PASS] {label}: {message}"

run_cmd Elab.Command.liftCoreM do
  expectDiagnostic "UniverseBox.mk.{1}/PLift" ``universeTarget ``universeBoxRealization
  expectDiagnostic "External valued unknown instance class" ``AllowlistRules.target ``unknownValuedRealization
  expectDiagnostic "ExternalAllowlistTypes.HiddenIndex" ``AllowlistRules.target ``hiddenIndexAttempt8Realization

end AllowlistAttempt8Fixtures

-- Executable supplied arguments use the same finite grammar as template bodies.
-- Legacy whole-readout type witnesses do not authorize these computations.
run_meta do
  for (label, name) in #[("ExternalClosedPropRejected", ``AllowlistRules.externalPropRead),
      ("ConstructorClosedDecisionRejected", ``AllowlistRules.constructorPropRead),
      ("UnsupportedDictionaryRejected", ``AllowlistRules.equivRead),
      ("UnsupportedQuotientArgumentRejected", ``AllowlistRules.cleanQuotientRealization)] do
    let .defnInfo info ← Lean.getConstInfo name | throwError "setup: executable argument"
    let result ← LeanInformationAudit.RegistrationGates.templateArgumentsCurrent
      ``AllowlistRules.target #[info.value] 524288
    let rejected := match result with
      | .error reason => reason.startsWith "unclassified_form:E"
      | _ => false
    logInfo m!"[{if rejected then "PASS" else "FAIL"}] {label} result={repr result}"

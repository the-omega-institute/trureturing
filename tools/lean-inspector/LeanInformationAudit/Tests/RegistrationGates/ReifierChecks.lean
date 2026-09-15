import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Syntax
import LeanInformationAudit.Tests.RegistrationGates.ReifierInterrupt
import LeanInformationAudit.Tests.RegistrationGates.Positive

namespace LeanInformationAudit.Tests.ReifierChecks
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates
open RegistrationReifier

/-- Assert both the diagnostic category and transactional absence of an entry. -/
elab "reject_via " label:str " expects " reason:str " in " command:command : command => do
  let before ← getEnv
  let messages := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand command
  let errors := (← get).messages.toList.filter (·.severity == .error)
  modify fun s => { s with messages }
  unless (InformationRegistry.entries (← getEnv)).size == (InformationRegistry.entries before).size do
    throwError "{label.getString}: rejected command inserted an entry"
  let owner ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo command.raw[1]
  let unit := localCompanionName before owner theoremUnitSuffix
  for name in #[unit, localCompanionName before owner primitiveRealizationSuffix,
      unit.str "__variation", unit.str "__sensitivity", unit.str "__nondegenerate",
      RegistrationGates.diagnosticName unit before.header.mainModule] do
    unless before.contains name == (← getEnv).contains name do
      throwError "{label.getString}: rejected command leaked a generated declaration"
  unless errors.length == 1 do throwError "{label.getString}: expected exactly one error, got {errors.length}"
  let actual ← errors[0]!.data.toString
  unless (actual.splitOn reason.getString).length > 1 do throwError "{label.getString}: {actual}"
  logInfo m!"P1_REJECTION {label.getString} {actual}"
  logInfo m!"P1_NEGATIVE {label.getString} {reason.getString} no_entry"

def expectFailure (label reason : String) (action : MetaM Unit) : MetaM Unit := do
  let outcome ← try action; pure none catch e => pure (some (← e.toMessageData.toString))
  let some actual := outcome | throwError "{label}: expected rejection"
  unless (actual.splitOn reason).length > 1 do throwError "{label}: {actual}"
  logInfo m!"P1_REJECTION {label} {actual}"
  logInfo m!"P1_NEGATIVE {label} {reason}"

def eqArena := pointwiseEqArena (Arena.ofFintype Bool) Bool
def neArena := pointwiseNeArena (Arena.ofFintype Bool) Bool
theorem clean (renamed : Bool) : renamed.not.not = renamed := Bool.not_not _
register_information_theorem clean
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem reflexive (x : Bool) : x = x := rfl
reject_via "reflexive_closed_truth" expects "forbidden_dependency" in
register_information_theorem reflexive
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x) (fun x => x)) in eqArena

theorem wrongArena (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "same_carrier_different_law" expects "ArenaMismatch" in
register_information_theorem wrongArena
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in neArena

reject_via "missing_arena" expects "IE-C003" in
register_information_theorem wrongArena
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in absentArena

theorem quantified (_p x : Bool) : x.not.not = x := Bool.not_not _
reject_via "theorem_specialisation" expects "StatementIdentityMismatch" in
register_information_theorem quantified
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem poly.{u} (X : Type u) (x : X) : x = x := rfl
reject_via "rigid_universes" expects "RigidUniverseMismatch" in
register_information_theorem poly
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem retained (x : Bool) : (have y := x.not.not; y) = x := Bool.not_not _
register_information_theorem retained
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => have y := x.not.not; y) (fun x => x)) in eqArena

theorem collapsed (x : Bool) : (have y := x.not.not; y) = x := Bool.not_not _
reject_via "collapsed_let" expects "StatementIdentityMismatch" in
register_information_theorem collapsed
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem unrelatedTrue : True := True.intro
theorem trueBridge : LegacyPrimitiveRealization eqArena True
    (pointwiseEqRealization (fun _ => false) (fun _ => false)) :=
  ⟨⟨fun _ _ => rfl, fun _ => True.intro⟩⟩
reject_via "unrelated_true_bridge" expects "UnsupportedDescriptor" in
register_information_theorem unrelatedTrue via trueBridge in eqArena

theorem hidden (x : Bool) : (have _p := clean; x.not.not) = x := Bool.not_not _
reject_via "provenance_hidden_proof" expects "forbidden_dependency" in
register_information_theorem hidden
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => have _p := clean; x.not.not) (fun x => x)) in eqArena

def singletonArena := pointwiseEqArena (Arena.ofFintype (Fin 1)) Bool
theorem singleton (_x : Fin 1) : false = false := rfl
reject_via "nondegenerate_required" expects "IE-C004" in
register_information_theorem singleton
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun _ : Fin 1 => false) (fun _ => false)) in singletonArena

def trivialOutput := pointwiseEqArena (Arena.ofFintype Bool) Unit
theorem noOutputs (_x : Bool) : Unit.unit = Unit.unit := rfl
reject_via "distinct_outputs_required" expects "MissingEvidence" in
register_information_theorem noOutputs
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun _ : Bool => Unit.unit) (fun _ => Unit.unit)) in trivialOutput

theorem unresolved (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "unresolved_descriptor" expects "UnresolvedMetavariables" in
register_information_theorem unresolved
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun _ : Bool => ?pending) (fun x => x)) in eqArena

theorem exhausted (x : Bool) : x.not.not = x := Bool.not_not _
set_option informationReifier.fuel 0 in
reject_via "forced_exhaustion" expects "IncompleteCheck" in
register_information_theorem exhausted
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

-- Type-only controls isolate the matcher from the Type-0 descriptor restriction.
run_meta do
  let a := mkSort (.param `u)
  unless ← exact a a do throwError "rigid universe positive"
  unless !(← exact a (mkSort (.param `v))) do throwError "rigid universe mismatch accepted"
  let left := mkApp (mkConst ``Fin) (mkNatLit 2)
  let right := mkApp (mkConst ``Fin) (mkNatLit 3)
  let expr := mkApp2 (mkConst ``Sum [Level.zero, Level.zero]) left right
  unless ← exact expr expr do throwError "composite index positive"
  unless !(← exact expr (mkApp2 (mkConst ``Sum [Level.zero, Level.zero]) right left)) do
    throwError "changed composite indices accepted"
  let flags := Expr.forallE `x (mkConst ``Bool) (mkConst ``True) .default
  unless !(← exact flags (.forallE `x (mkConst ``Bool) (mkConst ``True) .implicit)) do
    throwError "binder information erased"
  expectFailure "term_metavariable" "UnresolvedMetavariables" do
    discard <| exact (← mkFreshExprMVar (mkSort .zero)) (mkConst ``True)
  expectFailure "level_metavariable" "UnresolvedMetavariables" do
    discard <| exact (mkSort (← mkFreshLevelMVar)) a

theorem otherRealization : LegacyPrimitiveRealization eqArena (∀ x : Bool, x.not.not = x)
    (pointwiseEqRealization (fun _ => false) (fun _ => false)) :=
  ⟨⟨fun _ _ => rfl, fun _ => Bool.not_not⟩⟩

-- Mutation controls use the SAME valid occurrence and change one input only.
run_meta do
  let some entry := InformationRegistry.find? (← getEnv) ``clean | throwError "missing clean"
  validateDerivedCertificate entry
  let some cert := entry.derivedCertificate | throwError "missing certificate"
  expectFailure "copied_certificate" "CertificateBindingMismatch" do
    validateDerivedCertificate { entry with registrationModuleName := `CopiedModule }
  let rebound := { entry with registrationModuleName := `CopiedModule }
  expectFailure "rebound_certificate" "CertificateBindingMismatch" do
    validateDerivedCertificate { rebound with derivedCertificate := some {
      cert with occurrence := occurrenceBinding rebound } }
  let corrupt := { entry with statementIdentity := "stale", derivedCertificate := some {
    cert with statementIdentity := "stale" } }
  match ← validatePersistedEntry (← getEnv) corrupt with
  | .error reason => unless reason.startsWith "P1.CertificateBindingMismatch" do throwError reason
  | .ok () => throwError "stale statement identity certified"
  let changed := { entry with realizationName := ``otherRealization }
  expectFailure "wrong_bridge_realization" "BridgeBindingMismatch" do
    validateDerivedCertificate { changed with derivedCertificate := some {
      cert with occurrence := occurrenceBinding changed } }
  let arena ← freezeArena ``neArena
  let witness ← mkAppM ``FiniteSlotSensitivity #[arena]
  unless !(← RegistrationGates.checked entry.sensitivityWitness witness) do
    throwError "wrong-arena sensitivity accepted"
  unless !(← RegistrationGates.checked entry.variationWitness (← mkAppM ``FiniteLawVariation #[arena])) do
    throwError "wrong-arena variation accepted"
  let some diagnostic ← RegistrationGates.validateFinite { entry with variationWitness := .anonymous }
    | throwError "missing variation accepted"
  unless diagnostic.endsWith "reason=missing_witness" do throwError diagnostic
  logInfo "P1_WITNESS_CONTROLS checked"

-- Projection arguments and annotations remain observable even when unused by reduction.
run_meta do
  let pair := mkAppN (mkConst ``Prod.mk [.zero, .zero])
    #[mkConst ``Bool, mkConst ``Bool, mkConst ``Bool.false, mkConst ``Bool.true]
  let a := Expr.proj ``Prod 0 pair
  let b := Expr.proj ``Prod 0 (mkAppN pair.getAppFn (pair.getAppArgs.set! 3 (mkConst ``Bool.false)))
  unless ← exact a a do throwError "projection positive"
  expectFailure "projection_path" "path=type.value.arg" do
    requireExact "StatementIdentityMismatch" a b
  expectFailure "annotation_path" "path=type.body.value.arg" do
    requireExact "StatementIdentityMismatch" (mkAnnotation `tag a) (mkAnnotation `tag b)

-- Empty slot sensitivity is vacuous; variation is independently required.
def emptyArena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Fin 0, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law _ := True

def emptyRealization : PrimitiveRealization emptyArena.signature := ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
theorem emptySensitivity : FiniteSlotSensitivity emptyArena := ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
theorem emptySource : True := True.intro
theorem emptyBridge : LegacyPrimitiveRealization emptyArena True emptyRealization := ⟨Iff.rfl⟩
reject_via "empty_slots_derived" expects "UnsupportedDescriptor" in
register_information_theorem emptySource via emptyBridge in emptyArena
register_information_theorem emptySource in emptyArena
  primitives (@PrimitiveRealization.toPrimitiveBundle _ _ emptyArena.stateDecidableEq emptyRealization) realization emptyBridge sensitivity emptySensitivity

run_meta do
  let some entry := InformationRegistry.find? (← getEnv) ``emptySource | throwError "manual behavior changed"
  let some diagnostic ← RegistrationGates.validateFinite entry | throwError "vacuous slots certified"
  unless diagnostic.endsWith "reason=missing_witness" do throwError diagnostic
  unless entry.derivedCertificate.isNone do throwError "manual entry marked derived"
  logInfo "P1_EMPTY_SLOTS C048 missing_witness; manual insertion preserved"


-- Review R1/Q2: construct raw Expr inputs so elaborator reduction cannot mask extraction.
def reviewSource (annotated : Bool) : MetaM (Expr × Expr) := do
  let some e := InformationRegistry.find? (← getEnv) ``clean | throwError "missing clean"
  let some cert := e.derivedCertificate | throwError "missing certificate"
  let bool := mkConst ``Bool
  let inner := Expr.lam `y bool (mkApp (mkConst ``Bool.not)
    (mkApp (mkConst ``Bool.not) (mkBVar 0))) .default
  let lhs := if annotated then mkAnnotation `readout (inner.bindingBody!) else mkApp inner (mkBVar 0)
  let readout := Expr.lam `x bool (if annotated then inner.bindingBody! else lhs) .default
  let descriptor := mkAppN cert.descriptor.getAppFn (cert.descriptor.getAppArgs.set! 5
    (if annotated then mkAnnotation `readout readout else readout))
  let .forallE n t b bi := cert.statement | throwError "expected forall"
  return (descriptor, .forallE n t (mkAppN b.getAppFn (b.getAppArgs.set! 1 lhs)) bi)

elab "review_readout " annotated:ident : term => do
  return (← reviewSource (annotated.getId == `annotated)).1

run_meta do
  let (descriptor, expected) ← reviewSource false
  let (_, actual, _) ← semanticSource descriptor
  unless ← exact actual expected do throwError "raw_nested_source: authored inner beta redex erased"
  logInfo "P1_REVIEW raw_nested_source accepted"

run_meta do
  let (descriptor, expected) ← reviewSource true
  let (_, actual, _) ← semanticSource descriptor
  unless ← exact actual expected do throwError "annotated_source: readout-head metadata erased"
  logInfo "P1_REVIEW annotated_source accepted"

run_meta do
  for (name, annotated) in #[( `LeanInformationAudit.Tests.ReifierChecks.nestedPositive, false),
      (`LeanInformationAudit.Tests.ReifierChecks.annotatedPositive, true)] do
    let (_, type) ← reviewSource annotated
    addDecl (.thmDecl { name, levelParams := [], type, value := mkConst ``clean })
    unless (← getConstInfo name).type.equal type do throwError "raw theorem type not retained"

register_information_theorem nestedPositive via (review_readout nested) in eqArena
register_information_theorem annotatedPositive via (review_readout annotated) in eqArena
run_meta do
  for name in #[``nestedPositive, ``annotatedPositive] do
    unless InformationRegistry.hasTheorem (← getEnv) name do throwError "{name}: positive not registered"
    logInfo m!"P1_REVIEW positive_registered {name}"

theorem nestedNegative (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "nested_beta_in_readout" expects "StatementIdentityMismatch" in
register_information_theorem nestedNegative
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => (fun y : Bool => y.not.not) x) (fun x => x)) in eqArena

run_meta do
  let (descriptor, _) ← reviewSource true
  expectFailure "annotated_negative" "StatementIdentityMismatch" do
    discard <| exactUse ``clean (← freezeArena ``eqArena) descriptor

-- Review R2: persisted occurrence identity is raw, including optional certificate content.
def expectPersistedRejection (label : String) (edit : InformationRegistryEntry → InformationRegistryEntry) : MetaM Unit := do
  let env ← getEnv
  let some entry := InformationRegistry.find? env ``clean | throwError "missing clean"
  match ← validatePersistedEntry env (edit entry) with
  | .error reason =>
    unless reason.startsWith "P1.CertificateBindingMismatch" do throwError "{label}: {reason}"
    logInfo m!"P1_REVIEW {label} {reason}"
  | .ok () => throwError "{label}: expected rejection"

run_meta expectPersistedRejection "certificate_omission" fun e => { e with derivedCertificate := none }

run_meta do
  let env ← getEnv
  let some entry := InformationRegistry.find? env ``clean | throwError "missing clean"
  match ← withOptions (fun o => o.set `informationReifier.fuel (0 : Nat)) (validatePersistedEntry env entry) with
  | .error reason => unless reason.startsWith "P1.IncompleteCheck" do throwError reason
  | .ok () => throwError "original zero fuel accepted"
  withOptions (fun o => o.set `informationReifier.fuel (0 : Nat)) <|
    expectPersistedRejection "certificate_omission_zero_fuel" fun e => { e with derivedCertificate := none }

run_meta expectPersistedRejection "raw_occurrence_identity" fun e =>
  let changed := { e with catalogId := e.effectiveCatalogId }
  { changed with derivedCertificate := e.derivedCertificate.map fun c =>
    { c with occurrence := occurrenceBinding changed } }

-- Review R3: logged errors returning valid terms must roll back all six companions.
theorem loggedError (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "logged_error_rollback" expects "review_logged_error" in
register_information_theorem loggedError
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
  output_evidence (by
    run_tac Lean.logError "review_logged_error"
    exact inferInstance)


-- Q3/Q9: a buggy producer retains required values but wraps one raw type argument.
def reviewRawTypes (changed : Nat) : MetaM Unit := do
  let some original := InformationRegistry.find? (← getEnv) ``clean | throwError "missing clean"
  let some cert := original.derivedCertificate | throwError "missing certificate"
  let unit := original.unitName.str s!"raw{changed}"
  let nd := unit.str "__nondegenerate"
  let e := { original with
    unitName := unit
    sensitivityWitness := unit.str "__sensitivity"
    variationWitness := unit.str "__variation" }
  let ndType ← mkAppM ``Arena.Nondegenerate #[← mkAppM ``PrimitiveLawArena.toArena #[cert.arena]]
  let sens := mkAppN (mkConst ``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.sensitivity)
    (cert.descriptor.getAppArgs.extract 0 5 ++ #[cert.outputEvidence, mkConst nd])
  for i in [:4] do
    let name := #[nd, e.sensitivityWitness, e.variationWitness, unit][i]!
    let value ← match i with
      | 0 => pure ((← getConstInfo cert.nondegenerate).value? (allowOpaque := true)).get!
      | 1 => pure sens
      | 2 => mkAppM ``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.variation #[cert.arena, mkConst ``Bool.false, mkConst e.sensitivityWitness]
      | _ => unitValue e
    let type ← match i with
      | 0 => pure ndType
      | 1 => mkAppM ``FiniteSlotSensitivity #[cert.arena]
      | 2 => mkAppM ``FiniteLawVariation #[cert.arena]
      | _ => inferType value
    let type ← if i == changed then do
        pure <| mkAppN type.getAppFn (type.getAppArgs.set! (type.getAppArgs.size - 1)
          (← mkAppM ``id #[type.getAppArgs.back!]))
      else pure type
    if i == 3 then
      addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    else addDecl (.thmDecl { name, levelParams := [], type, value })
  let e := { e with derivedCertificate := some { cert with nondegenerate := nd, occurrence := occurrenceBinding e } }
  expectFailure s!"raw_type_{changed}" (if changed == 3 then "UnitBindingMismatch" else "WitnessBindingMismatch") <|
    validateDerivedCertificate e

run_meta reviewRawTypes 0
run_meta reviewRawTypes 1
run_meta reviewRawTypes 2
run_meta reviewRawTypes 3

-- Actual recursion-limit exceptions, separately in descriptor and evidence elaboration.
elab "review_exhaustion" : term =>
  withOptions (fun o => o.set `maxRecDepth (1 : Nat)) <|
    MonadRecDepth.withRecDepth 1 <| withIncRecDepth <| pure (mkConst ``Bool.true)
theorem resourceDescriptor (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "descriptor_exhaustion" expects "P1.IncompleteCheck" in
register_information_theorem resourceDescriptor via review_exhaustion in eqArena
theorem resourceEvidence (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "evidence_exhaustion" expects "P1.IncompleteCheck" in
register_information_theorem resourceEvidence
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
  output_evidence review_exhaustion

-- Q4: the consumer trusts correct report production; an empty literal is no scan proof.
run_meta do
  let saved ← getEnv
  try
    let some original := InformationRegistry.find? saved ``clean | throwError "missing clean"
    let some cert := original.derivedCertificate | throwError "missing certificate"
    let descriptor := mkAppN cert.descriptor.getAppFn
      (cert.descriptor.getAppArgs.set! 5 cert.descriptor.getAppArgs[6]!)
    let e ← prepareRegistrationEntry (← getEnv) { original with
      theoremName := ``reflexive
      unitName := original.unitName.str "producerBug"
      realizationName := original.realizationName.str "producerBug"
      statementIdentity := theoremStatementIdentity (← getEnv) ``reflexive
      derivedCertificate := none }
    let e ← derive e (← freezeArena ``eqArena) descriptor
    let some diagnostic ← RegistrationGates.validateFinite e | throwError "boundary: scanner accepted"
    unless (diagnostic.splitOn "forbidden_dependency").length > 1 do throwError diagnostic
    RegistrationGates.publishDiagnostic e.unitName none
    validateDerivedCertificate e
    closedTruthExcluded e
    logInfo "P1_REVIEW producer_report_boundary conditional_on_correct_producer"
  finally setEnv saved

run_meta do
  let some diagnostic ← RegistrationGates.provenanceErrorCurrent `root `catalog ``clean `absentReadout
    | throwError "expected incomplete provenance"
  expectFailure "insertion_incomplete" "P1.IncompleteCheck" <| checkDiagnostic diagnostic

run_meta do
  expectFailure "bounded_runtime" "P1.IncompleteCheck" <| bounded <|
    withOptions (fun o => o.set `maxRecDepth (1 : Nat)) <|
      MonadRecDepth.withRecDepth 1 <| withIncRecDepth <| pure ()


run_meta do
  for name in #[``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise,
      ``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.sensitivity,
      ``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.variation] do
    discard <| checkedProvider name
  let some entry := InformationRegistry.find? (← getEnv) ``clean | throwError "missing real provider registration"
  validateDerivedCertificate entry
  logInfo "P1_PROVIDER real_provider insertion_and_consumer accepted"

-- A5: the producer executes an uncaught internal interrupt after actual derivation.
run_meta do
  let env ← getEnv
  let owner := ``LeanInformationAudit.Tests.ReifierInterrupt.clean
  let producer := `LeanInformationAudit.Tests.RegistrationGates.ReifierInterrupt
  let unit := owner.str theoremUnitSuffix
  let names := #[unit, owner.str primitiveRealizationSuffix,
    unit.str "__nondegenerate", unit.str "__sensitivity", unit.str "__variation",
    RegistrationGates.diagnosticName unit producer]
  let present := names.filter env.contains
  let rows := (InformationRegistry.entries env).filter (·.registrationModuleName == producer)
  logInfo m!"P1_A5 interrupt_publication source_imported={env.isImportedConst owner} rows={rows.size} present_generated={present} checked_names={names.size}"
  unless env.isImportedConst owner && rows.isEmpty && present.isEmpty do
    throwError "interrupt_publication: cancellation published generated content"

def highArena : PrimitiveLawArena.{1,0,0} where
  toArena := Arena.ofFintype (ULift.{1} Bool)
  signature := {
    Index := Fin 0, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law _ := True

run_meta do
  unless (← freezeArena ``eqArena).equal (mkConst ``eqArena) do
    throwError "arena_type0: raw arena changed"
  logInfo "P1_A5 arena_type0 accepted raw_head=preserved"
  expectFailure "arena_universe1" "P1.RigidUniverseMismatch" do
    discard <| freezeArena ``highArena

-- A descriptor that would fail if arena resolution did not reject first.
elab "arena_order_tripwire" : term => throwError "arena_order_tripwire executed"
reject_via "arena_universe1_early" expects "P1.RigidUniverseMismatch" in
register_information_theorem wrongArena via arena_order_tripwire in highArena

-- Full Name identity survives name resolution, but never unfolds a wrapper.
theorem aliasPointwise {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f g : X → Y) : LegacyPrimitiveRealization (pointwiseEqArena (Arena.ofFintype X) Y)
    (∀ x : X, f x = g x) (pointwiseEqRealization f g) :=
  D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise f g
abbrev abbrevPointwise := @D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
@[reducible] def reduciblePointwise := @D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
namespace ProviderAlias
abbrev pointwise := @D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
end ProviderAlias
macro "approved_descriptor" : term =>
  `(D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
    (fun x : Bool => x.not.not) (fun x => x))

elab "accept_via " label:str " in " command:command : command => do
  let saved ← getEnv
  try
    elabCommand command
    let some entry := InformationRegistry.find? (← getEnv) ``wrongArena
      | throwError "{label.getString}: missing positive registration"
    match ← liftTermElabM <| validatePersistedEntry (← getEnv) entry with
    | .error reason => throwError reason
    | .ok () => logInfo m!"P1_A5 {label.getString} insertion_and_consumer accepted"
  finally setEnv saved

open D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates in
accept_via "provider_open_namespace" in
register_information_theorem wrongArena via (pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
accept_via "provider_macro" in
register_information_theorem wrongArena via approved_descriptor in eqArena
reject_via "provider_theorem_alias" expects "P1.UnsupportedDescriptor" in
register_information_theorem wrongArena via (aliasPointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
reject_via "provider_abbrev" expects "P1.UnsupportedDescriptor" in
register_information_theorem wrongArena via (abbrevPointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
reject_via "provider_reducible" expects "P1.UnsupportedDescriptor" in
register_information_theorem wrongArena via (reduciblePointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
reject_via "provider_namespace_alias" expects "P1.UnsupportedDescriptor" in
register_information_theorem wrongArena via (ProviderAlias.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

-- Check the same transaction after insertion, when both extension rows and all
-- six companions exist. Catch at EIO to observe the exact rethrown internal id.
def captureCommandException (action : CommandElabM Unit) : CommandElabM (Option Exception) :=
  fun ctx state => do
    try action ctx state; return none
    catch e => return some e

elab "check_internal_rollback" : command => do
  let initial ← get
  let some source := InformationRegistry.find? initial.env ``clean | throwError "missing source"
  let some cert := source.derivedCertificate | throwError "missing source certificate"
  let owner := ``wrongArena
  let unit := localCompanionName initial.env owner theoremUnitSuffix
  let names := #[unit, localCompanionName initial.env owner primitiveRealizationSuffix,
    unit.str "__nondegenerate", unit.str "__sensitivity", unit.str "__variation",
    RegistrationGates.diagnosticName unit initial.env.header.mainModule]
  let mut observations : Array String := #[]
  for (label, id) in #[("interrupt", interruptExceptionId),
      ("abort_command", abortCommandExceptionId), ("abort_term", abortTermExceptionId),
      ("other_internal", postponeExceptionId)] do
    set initial
    let caught ← captureCommandException <| registrationTransaction do
      let entry ← liftTermElabM do
        let e ← prepareRegistrationEntry (← getEnv) { source with
          theoremName := owner, unitName := unit, realizationName := names[1]!,
          statementIdentity := theoremStatementIdentity (← getEnv) owner, derivedCertificate := none }
        derive e (← freezeArena ``eqArena) cert.descriptor
      registerValidatedEntry entry
      unless names.all (← getEnv).contains &&
          (InformationRegistry.entries (← getEnv)).size == (InformationRegistry.entries initial.env).size + 1 do
        throwError "internal rollback control did not stage all declarations and row"
      throw (.internal id)
    let env ← getEnv
    let rethrown := match caught with
      | some (.internal actual _) => actual == id
      | _ => false
    let present := names.filter env.contains
    let unchanged := (InformationRegistry.entries env).size == (InformationRegistry.entries initial.env).size
    let observation := s!"P1_A5 rollback_{label} rethrown={rethrown} row_unchanged={unchanged} present_generated={present}"
    observations := observations.push observation
    -- Restore the test harness even on a broken production transaction.
    set initial
    unless rethrown && unchanged && present.isEmpty do throwError observation
  for observation in observations do logInfo observation
check_internal_rollback

-- An export is a name-resolution alias of the genuine declaration, not a wrapper.
namespace Exported
export D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates (pointwise)
end Exported

theorem exportedClean (x : Bool) : x.not.not = x := Bool.not_not _
register_information_theorem exportedClean
  via (Exported.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena
run_meta do
  let env ← getEnv
  let some entry := InformationRegistry.find? env ``exportedClean
    | throwError "provider_export: missing registration"
  validateDerivedCertificate entry
  match ← validatePersistedEntry env entry with
  | .error reason => throwError reason
  | .ok () => logInfo "P1_A7 provider_export insertion_and_consumer accepted"

end LeanInformationAudit.Tests.ReifierChecks

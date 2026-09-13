import LeanInformationAudit.Syntax
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
  unless errors.length == 1 do throwError "{label.getString}: expected exactly one error, got {errors.length}"
  let actual ← errors[0]!.data.toString
  unless (actual.splitOn reason.getString).length > 1 do throwError "{label.getString}: {actual}"
  logInfo m!"P1_NEGATIVE {label.getString} {reason.getString} no_entry"

def expectFailure (label reason : String) (action : MetaM Unit) : MetaM Unit := do
  let outcome ← try action; pure none catch e => pure (some (← e.toMessageData.toString))
  let some actual := outcome | throwError "{label}: expected rejection"
  unless (actual.splitOn reason).length > 1 do throwError "{label}: {actual}"
  logInfo m!"P1_NEGATIVE {label} {reason}"

def eqArena := pointwiseEqArena (Arena.ofFintype Bool) Bool
def neArena := pointwiseNeArena (Arena.ofFintype Bool) Bool
theorem clean (renamed : Bool) : renamed.not.not = renamed := Bool.not_not _
register_information_theorem clean
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem reflexive (x : Bool) : x = x := rfl
reject_via "reflexive_closed_truth" expects "forbidden_dependency" in
register_information_theorem reflexive
  via (ReifierTemplates.pointwise (fun x : Bool => x) (fun x => x)) in eqArena

theorem wrongArena (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "same_carrier_different_law" expects "ArenaMismatch" in
register_information_theorem wrongArena
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in neArena

reject_via "missing_arena" expects "IE-C003" in
register_information_theorem wrongArena
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in absentArena

theorem quantified (_p x : Bool) : x.not.not = x := Bool.not_not _
reject_via "theorem_specialisation" expects "StatementIdentityMismatch" in
register_information_theorem quantified
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem poly.{u} (X : Type u) (x : X) : x = x := rfl
reject_via "rigid_universes" expects "RigidUniverseMismatch" in
register_information_theorem poly
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem retained (x : Bool) : (have y := x.not.not; y) = x := Bool.not_not _
register_information_theorem retained
  via (ReifierTemplates.pointwise (fun x : Bool => have y := x.not.not; y) (fun x => x)) in eqArena

theorem collapsed (x : Bool) : (have y := x.not.not; y) = x := Bool.not_not _
reject_via "collapsed_let" expects "StatementIdentityMismatch" in
register_information_theorem collapsed
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

theorem unrelatedTrue : True := True.intro
theorem trueBridge : LegacyPrimitiveRealization eqArena True
    (pointwiseEqRealization (fun _ => false) (fun _ => false)) :=
  ⟨⟨fun _ _ => rfl, fun _ => True.intro⟩⟩
reject_via "unrelated_true_bridge" expects "UnsupportedDescriptor" in
register_information_theorem unrelatedTrue via trueBridge in eqArena

theorem hidden (x : Bool) : (have _p := clean; x.not.not) = x := Bool.not_not _
reject_via "provenance_hidden_proof" expects "forbidden_dependency" in
register_information_theorem hidden
  via (ReifierTemplates.pointwise (fun x : Bool => have _p := clean; x.not.not) (fun x => x)) in eqArena

def singletonArena := pointwiseEqArena (Arena.ofFintype (Fin 1)) Bool
theorem singleton (_x : Fin 1) : false = false := rfl
reject_via "nondegenerate_required" expects "IE-C004" in
register_information_theorem singleton
  via (ReifierTemplates.pointwise (fun _ : Fin 1 => false) (fun _ => false)) in singletonArena

def trivialOutput := pointwiseEqArena (Arena.ofFintype Bool) Unit
theorem noOutputs (_x : Bool) : Unit.unit = Unit.unit := rfl
reject_via "distinct_outputs_required" expects "MissingEvidence" in
register_information_theorem noOutputs
  via (ReifierTemplates.pointwise (fun _ : Bool => Unit.unit) (fun _ => Unit.unit)) in trivialOutput

theorem unresolved (x : Bool) : x.not.not = x := Bool.not_not _
reject_via "unresolved_descriptor" expects "UnresolvedMetavariables" in
register_information_theorem unresolved
  via (ReifierTemplates.pointwise (fun _ : Bool => ?pending) (fun x => x)) in eqArena

theorem exhausted (x : Bool) : x.not.not = x := Bool.not_not _
set_option informationReifier.fuel 0 in
reject_via "forced_exhaustion" expects "IncompleteCheck" in
register_information_theorem exhausted
  via (ReifierTemplates.pointwise (fun x : Bool => x.not.not) (fun x => x)) in eqArena

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
register_information_theorem emptySource in emptyArena
  primitives (@PrimitiveRealization.toPrimitiveBundle _ _ emptyArena.stateDecidableEq emptyRealization) realization emptyBridge sensitivity emptySensitivity

run_meta do
  let some entry := InformationRegistry.find? (← getEnv) ``emptySource | throwError "manual behavior changed"
  let some diagnostic ← RegistrationGates.validateFinite entry | throwError "vacuous slots certified"
  unless diagnostic.endsWith "reason=missing_witness" do throwError diagnostic
  unless entry.derivedCertificate.isNone do throwError "manual entry marked derived"
  logInfo "P1_EMPTY_SLOTS C048 missing_witness; manual insertion preserved"

end LeanInformationAudit.Tests.ReifierChecks

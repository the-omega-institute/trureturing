import Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

open Lean Meta Elab Command LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option trace.InformationRegistration.check true

namespace LeanInformationAuditRegTests.FamilySourceContract

private def target := ``D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation

private def mustReject (label : String) (action : MetaM Unit) : MetaM Unit := do
  let rejected ← try
    action
    pure false
  catch _ => pure true
  unless rejected do throwError "[FAIL] accepted {label}"
  logInfo m!"[PASS] source_rejects_{label}"

private partial def missingClause : Expr → Expr
  | .forallE n d b bi => .forallE n d (missingClause b) bi
  | e => if e.isAppOfArity ``And 2 then e.getAppArgs[0]! else e

private partial def changeDictionary (e : Expr) : Expr :=
  match e with
  | .forallE n d b .instImplicit => .forallE n d b .default
  | .forallE n d b bi => .forallE n d (changeDictionary b) bi
  | e => e

run_meta do
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
    | throwError "original source occurrence missing"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "original source claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated certificate := record.result
    | throwError "[FAIL] full original source registration: {(← TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.isSome && record.escape.continuation.any (·.kind == "open") &&
      record.escape.bridgeKind == "source-equivalence" && certificate.sourceBinding.isSome do
    throwError "[FAIL] incomplete four slots"
  let some selection := claim.escapeInput.sourceSelection | throwError "selection missing"
  let info ← getConstInfo target
  let (scope, _) ← SourceScope.resolve info selection |>.run 524288
  unless scope.telescope.size == 13 && scope.levels.length == 2 &&
      selection.coordinates == #[0, 1, 11] do throwError "[FAIL] full source telescope"
  logInfo "[PASS] original_source_thirteen_binders_all_clauses_rigid_universes"
  let rejectSelection (label : String) (selection : SourceSelection) : MetaM Unit := do
    mustReject label do discard <| (SourceScope.resolve info selection).run 524288
  rejectSelection "wrong_owner" { selection with owner := `D5.Other }
  rejectSelection "coordinate_order" { selection with coordinates := #[1, 0, 11] }
  rejectSelection "coordinate_dependency" { selection with coordinates := #[1, 8, 11] }
  rejectSelection "dictionary_coordinate" { selection with coordinates := #[0, 1, 2, 11] }
  rejectSelection "proof_coordinate" { selection with coordinates := #[0, 1, 9, 11] }
  rejectSelection "absent_path" { selection with readouts := #[{ path := #["fn"], stateBinder := 16 }] }
  rejectSelection "duplicate_occurrence" { selection with readouts := selection.readouts ++ selection.readouts }
  rejectSelection "wrong_state_scope" { selection with readouts := selection.readouts.map (fun r => { r with stateBinder := 12 }) }
  mustReject "missing_conjunct" do
    discard <| (SourceScope.reconstruct info.type (missingClause info.type)).run 524288
  mustReject "dictionary_binder_info" do
    discard <| (SourceScope.reconstruct info.type (changeDictionary info.type)).run 524288
  mustReject "nested_dictionary_binder_info" do
    let nested := mkApp2 (mkConst ``And) info.type (mkConst ``True)
    let changed := mkApp2 (mkConst ``And) (changeDictionary info.type) (mkConst ``True)
    discard <| (SourceScope.reconstruct nested changed).run 524288
  let rejectClaim (label : String) (event : TemplateOccurrenceEvent) (claim : TemplateBindingClaim) : MetaM Unit := do
    let result ← TemplateBinding.assess event (some claim)
    if result.result matches .declaredValidated _ then throwError "[FAIL] accepted {label}"
    logInfo m!"[PASS] source_rejects_{label}"
  rejectClaim "universe_permutation" { event with levelParams := event.levelParams.reverse } claim
  rejectClaim "cross_occurrence_claim" { event with key := { event.key with catalog := `Other } } claim
  mustReject "stale_source_event" do
    TemplateBinding.validateEvent { event with registrationSourceIdentity := "stale" }
  mustReject "wrong_origin_event" do
    TemplateBinding.validateEvent { event with key := { event.key with registrationModule := `Reg.Wrong } }
  rejectClaim "mismatched_residual" event { claim with escapeInput := {
    claim.escapeInput with openContinuation := false, continuation := some (mkConst ``True.intro) } }
  rejectClaim "absent_source_binding" event { claim with escapeInput := {
    claim.escapeInput with sourceSelection := none } }
  let signature := mkConst ``D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.signature
    (event.levelParams.map Level.param)
  let altered := mkConst ``D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.rejected
    (event.levelParams.map Level.param)
  mustReject "altered_actual_readout" do
    discard <| (SourceScope.validateFields scope signature altered).run 524288
  mustReject "target_hidden_in_discarded_data" do
    let discarded := mkApp (.lam `ignored (mkSort .zero) (mkConst ``Unit.unit) .default) info.type
    discard <| SourceOperands.check target #[discarded] 524288
  let some descriptor := claim.descriptor | throwError "descriptor missing"
  let name := `LeanInformationAuditRegTests.FamilySourceContract.contaminatedTemplate
  addDecl <| .defnDecl {
    name, levelParams := info.levelParams, type := ← inferType descriptor,
    value := mkApp (.lam `ignored (mkSort .zero) descriptor .default) info.type,
    hints := .abbrev, safety := .safe }
  mustReject "target_hidden_in_template_body" do
    discard <| SourceOperands.check target
      #[mkConst name (info.levelParams.map Level.param)] 524288
  mustReject "target_hidden_in_proof_proposition" do
    let discarded := Expr.letE `proof info.type (mkConst target (info.levelParams.map Level.param))
      (mkConst ``Unit.unit) false
    discard <| SourceOperands.check target #[discarded] 524288
  mustReject "target_decision_type" do
    let decision := mkApp (mkConst ``Decidable) info.type
    discard <| SourceOperands.check target #[decision] 524288
  let deep := (List.range 257).foldl (fun body _ => Expr.app (mkConst ``id) body) (mkConst ``Unit.unit)
  unless (TemplateAudit.compactRawIdentity [] deep).toOption.isNone do
    throwError "[FAIL] deep compact source accepted"
  let unique := (List.range 20000).toArray.map fun i => mkNatLit i
  let rec balanced (xs : Array Expr) : Expr := Id.run do
    if xs.size == 1 then return xs[0]!
    if xs.isEmpty then return mkConst ``Unit.unit
    let mid := xs.size / 2
    return .app (balanced (xs.extract 0 mid)) (balanced (xs.extract mid xs.size))
    termination_by xs.size
    decreasing_by all_goals simp_wf; omega
  unless (TemplateAudit.compactRawIdentity [] (balanced unique)).toOption.isNone do
    throwError "[FAIL] oversized unique compact source accepted"
  logInfo "[PASS] compact_source_deep_and_unique_budget_negatives"
  let snapshot ← TemplateBinding.exportSnapshot
  let modules := #[event.key.registrationModule].map fun module =>
    (module, snapshot.originals.filter (·.occurrence.key.registrationModule == module) |>.map (·.occurrence.key))
  let wires ← TemplateBinding.reportJson modules
  IO.FS.createDirAll ".lake/build"
  IO.FS.writeFile ".lake/build/source-family-evidence.json" ((Json.arr wires).compress ++ "\n")
  logInfo m!"[PASS] original_source_declared_validated evidence_ref={certificate.evidenceRef}"

-- A zero-length history cannot vary. This fiber remains in the full source law.
example (J : Type u) (Z : ℕ → Type v)
    (L : _root_.D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.Readout (J := J) (Z := Z) 0 → Prop) :
    ¬ ∃ r r', L r ∧ ¬ L r' :=
  Reg.Support.FiniteHistoryFamily.zero_no_variation J Z L

end LeanInformationAuditRegTests.FamilySourceContract

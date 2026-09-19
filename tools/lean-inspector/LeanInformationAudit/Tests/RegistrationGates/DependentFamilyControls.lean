import LeanInformationAudit.Tests.RegistrationGates.DependentFamily

namespace LeanInformationAudit.Tests.DependentFamilyControls
open Lean Meta Elab Command
open LeanInformationAudit DependentFamily
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

run_meta do
  let source ← getConstInfo ``history_law_conditional_expectation
  let event := (TemplateBinding.inventory (← getEnv)).find? (·.key.mode == .dependentFamily)
  let some event := event | throwError "control setup: missing family event"
  let some scope := event.familyScope | throwError "control setup: missing source scope"
  unless scope.telescope.size == 13 &&
      (scope.telescope.filter (·.info == .instImplicit)).size == 6 &&
      scope.selection.coordinates == #[0, 1, 11] && scope.levels == source.levelParams do
    throwError "control setup: original source telescope changed"
  logInfo "[PASS] original_13_binders_six_dictionaries_rigid_levels"
  let reject (label : String) (candidate : FamilySourceScope) : MetaM Unit := do
    let failure ← try
      discard <| FamilySource.validate source candidate
      pure false
    catch _ => pure true
    unless failure do throwError "[FAIL] {label}"
    logInfo m!"[PASS] {label}"
  reject "source_rigid_universe_swap" { scope with levels := scope.levels.reverse }
  reject "source_dropped_binder" { scope with telescope := scope.telescope.pop }
  reject "source_binder_info" { scope with telescope := scope.telescope.modify 0 (fun b => { b with info := .default }) }
  reject "source_raw_missing_origin" { scope with
    selection := { scope.selection with statePath := #["absent"] } }
  reject "source_captured_coordinate" { scope with stateFiber := mkBVar 0 }
  reject "source_proxy_state" { scope with stateFiber := mkConst ``Bool }
  reject "source_proxy_output" { scope with outputFiber := mkConst ``Bool }
  reject "source_dictionary_coordinate" { scope with
    selection := { scope.selection with coordinates := #[0, 1, 2, 11] } }
  reject "source_proof_coordinate" { scope with
    selection := { scope.selection with coordinates := #[0, 1, 8, 9, 11] } }
  reject "source_reordered_coordinates" { scope with
    selection := { scope.selection with coordinates := #[1, 0, 11] } }
  reject "source_duplicate_coordinate" { scope with
    selection := { scope.selection with coordinates := #[0, 1, 1, 11] } }
  reject "source_occurrence_context" { scope with
    state := { scope.state with context := scope.state.context.pop } }
  let budgetFailure ← try
    discard <| FamilySource.resolve source scope.selection 1
    pure false
  catch error => pure ((← error.toMessageData.toString).startsWith "incomplete_closure:E8.")
  unless budgetFailure do throwError "[FAIL] source_budget"
  logInfo "[PASS] source_budget"
  let nested := Expr.lam `x (mkConst ``Nat) (mkApp (mkBVar 12) (mkBVar 0)) .default
  let .ok (projected, _) := TemplateAudit.PlanTransform.projectCoordinates #[0, 1, 11] 13 nested
    | throwError "[FAIL] nested_projection"
  let .ok (restored, _) := TemplateAudit.PlanTransform.projectCoordinates #[0, 1, 11] 13 projected true
    | throwError "[FAIL] nested_inverse"
  unless restored.equal nested do throwError "[FAIL] nested_capture_avoiding_roundtrip"
  logInfo "[PASS] nested_capture_avoiding_roundtrip"

universe u v
noncomputable def wrongArena : Arena where
  signature := DependentFamily.signature.{u,v}
  Law _ := True

noncomputable def weakenedArena : Arena where
  signature := DependentFamily.signature.{u,v}
  Law r := FullLaw (fun J Z N => r.readout () ⟨J,Z,N⟩) ∨ False

noncomputable def weakenedRegistration : Registration weakenedArena.{u,v} (FullLaw identityFamily) where
  realization := DependentFamily.template DependentFamily.signature (fun _ _ ω => ω.2) Empty.elim
  bridge := Or.inl
  variation := ⟨DependentFamily.template DependentFamily.signature (fun _ _ ω => ω.2) Empty.elim,
    DependentFamily.bad, Or.inl (@history_law_conditional_expectation.{u,v}),
    fun h => h.elim bad_not_law False.elim⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨DependentFamily.template DependentFamily.signature (fun _ _ ω => ω.2) Empty.elim,
        DependentFamily.bad, ?_, rfl, ?_⟩
      · intro j h
        exact False.elim (h (@Subsingleton.elim Unit inferInstance j i))
      · constructor
        · intro _ h
          exact h.elim bad_not_law False.elim
        · intro _
          exact Or.inl (@history_law_conditional_expectation.{u,v})
    · intro i
      exact Empty.elim i

def indexAlias (n : Nat) (i : Fin n) : Nat := i.val

run_meta do
  let some event := (TemplateBinding.inventory (← getEnv)).find?
      (·.key.mode == .dependentFamily) | throwError "missing family"
  let input : EscapeRecordInput := { openContinuation := true }
  let reject (label : String) (candidate : TemplateOccurrenceEvent)
      (input : EscapeRecordInput := input) : MetaM Unit := do
    let rejected ← try
      discard <| FamilyRegistration.validate candidate input
      pure false
    catch _ => pure true
    unless rejected do throwError "[FAIL] {label}"
    logInfo m!"[PASS] {label}"
  reject "family_wrong_full_law" { event with statement := mkConst ``True }
  let weaker := { event with
    realizationName := ``weakenedRegistration
    unitName := ``weakenedRegistration
    key := { event.key with objectArena := ``weakenedArena } }
  let wrongLawRejected ← try
    discard <| FamilyRegistration.validate weaker input
    pure false
  catch error => pure ((← error.toMessageData.toString) ==
    "unclassified_form:family.registration.exact_source_law")
  unless wrongLawRejected do throwError "[FAIL] typed_but_different_law_rejected"
  logInfo "[PASS] typed_but_different_law_rejected"
  reject "family_missing_source_scope" { event with familyScope := none }
  reject "family_wrong_actual_arena" { event with
    key := { event.key with objectArena := ``wrongArena } }
  reject "family_cross_mode_registration" { event with
    key := { event.key with mode := .fixedState } }
  reject "family_closed_continuation" event { openContinuation := false }
  withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLocalDeclD `i (mkApp (mkConst ``Fin) n) fun i => do
      let named := mkApp2 (mkConst ``Fin.val) n i
      let raw := Expr.proj ``Fin 0 i
      for value in #[named, raw] do
        discard <| TemplateAudit.checkExtractionType (mkApp (mkConst ``Fin) value)
          524288 #[] .dependentFamily
      logInfo "[PASS] family_fin_named_and_raw_index"
      for (label, value, typePosition) in #[
          ("family_fin_value_rejected", named, false),
          ("family_fin_proof_field_rejected", Expr.proj ``Fin 1 i, true),
          ("family_fin_alias_rejected", mkApp2 (mkConst ``indexAlias) n i, true)] do
        let rejected ← try
          if typePosition then
            -- The command kernel-checks descriptors before proof erasure.
            checkWithKernel (mkApp (mkConst ``Fin) value)
            discard <| TemplateAudit.checkExtractionType (mkApp (mkConst ``Fin) value)
              524288 #[] .dependentFamily
          else
            discard <| TemplateAudit.checkArguments event.key.theoremName #[value]
              524288 #[] #[] .dependentFamily
          pure false
        catch _ => pure true
        unless rejected do throwError "[FAIL] {label}"
        logInfo m!"[PASS] {label}"

run_meta do
  let nat := mkConst ``Nat
  let sourceType := Expr.forallE `A (mkSort (.succ .zero))
    (.forallE `f (.forallE `n nat (.forallE `n nat nat .default) .default)
      (.forallE `n nat (mkConst ``True) .default) .default) .default
  let source : ConstantInfo := .axiomInfo {
    name := `capturedFixture, levelParams := [], type := sourceType, isUnsafe := false }
  let selection : FamilySourceSelection := {
    coordinates := #[2], statePath := #["body", "domain", "body", "body"],
    outputPath := #["body", "domain", "body", "body"] }
  let rejected ← try
    discard <| FamilySource.resolve source selection
    pure false
  catch error => pure ((← error.toMessageData.toString) ==
    "unclassified_form:family.source.captured_coordinate")
  unless rejected do throwError "[FAIL] same_typed_nested_binder_capture"
  logInfo "[PASS] same_typed_nested_binder_capture"

noncomputable def separateTemplate (s : Signature)
    (readout : ∀ role θ, s.State θ → s.Output role θ)
    (anchor : ∀ (_ : s.Anchor) θ, s.State θ) : Realization s := ⟨readout, anchor⟩

run_cmd do
  let result ← TemplateAudit.enroll ``separateTemplate #[] .fixedState
  unless !result.isOk && !(TemplateAudit.selectedPlan (← getEnv) ``separateTemplate).isOk do
    throwError "[FAIL] family_fixed_mode_rollback"
  logInfo "[PASS] family_fixed_mode_rollback"

set_option informationTemplate.work 1 in
run_cmd do
  let result ← TemplateAudit.enroll ``separateTemplate #[] .dependentFamily
  unless !result.isOk && !(TemplateAudit.selectedPlan (← getEnv) ``separateTemplate).isOk do
    throwError "[FAIL] family_work_budget_rollback"
  logInfo "[PASS] family_work_budget_rollback"

-- The interface does not weaken variation to per-fiber or unused-role witnesses.
example (S : Signature) : ¬ GlobalFamilyVariation ⟨S, fun _ => True⟩ := by
  rintro ⟨_, _, _, h⟩
  exact h trivial

example : ¬ FamilyRoleSensitivity
    (⟨{ Θ := Unit, State := fun _ => Unit, Role := Bool,
        finiteRole := inferInstance, nonemptyRole := inferInstance,
        Output := fun _ _ => Bool, Anchor := Empty, finiteAnchor := inferInstance },
      fun r => r.readout false () () = true⟩ : Arena) := by
  rintro ⟨hs, _⟩
  obtain ⟨g, b, others, _, flip⟩ := hs true
  have eq := congrArg (fun f => f () ()) (others false Bool.false_ne_true)
  have hp : (g.readout false () () = true) ↔ (b.readout false () () = true) := by rw [eq]
  exact iff_not_self (hp.symm.trans flip)

example (J : Type) (Z : ℕ → Type) (L : Readout (J := J) (Z := Z) 0 → Prop) :
    ¬ ∃ x y, L x ∧ ¬ L y := zero_no_variation J Z L

end LeanInformationAudit.Tests.DependentFamilyControls

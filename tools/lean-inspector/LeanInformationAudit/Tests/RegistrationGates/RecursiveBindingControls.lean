import LeanInformationAudit.Tests.RegistrationGates.RecursiveKernelControls

namespace LeanInformationAudit.Tests.RecursiveBindingControls
open Lean Meta TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def template (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization f
register_information_template template constructors 1 [List]

def localAll : List Bool → Bool
  | [] => true
  | x :: xs => Bool.and x (localAll xs)

def recursiveData (b : Bool) : Bool := Bool.and b (localAll [true])
def changedData (b : Bool) : Bool := Bool.and b (localAll [false])

def ignoredInput (_ : Bool) (b : Bool) : Bool := b
def erasedInput (b : Bool) : Bool :=
  ignoredInput (decide ((0 : Nat) < 24)) (recursiveData b)

def recursiveWithProof (_ : ∀ x : Bool, recursiveData x = x.not.not) (b : Bool) : Bool :=
  recursiveData b

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not
instance : DecidableEq arena.State := instDecidableEqBool

information_theorem checked in arena
  readout via (template (fun b => recursiveData b))
  primitives (template (fun b => recursiveData b))
  : ∀ x : Bool, recursiveData x = x.not.not := by intro x; cases x <;> rfl

information_theorem changed in arena
  readout via (template (fun b => changedData b))
  primitives (template (fun b => recursiveData b))
  : ∀ x : Bool, recursiveData x = x.not.not := by intro x; cases x <;> rfl

run_meta do
  for (name, expected) in #[(``checked, true), (``changed, false)] do
    let some row := (TemplateBinding.records (← getEnv)).find?
        (·.occurrence.key.theoremName == name) | throwError "missing recursive occurrence"
    let valid := row.result matches .declaredValidated _
    unless valid == expected do logError m!"[FAIL] recursive_binding {name}"
    if valid == expected then logInfo m!"[PASS] recursive_binding {name}"
    if let .declaredUnresolved diagnostic := row.result then
      logInfo diagnostic
      if !expected && !(diagnostic.contains "dtr.realization_mismatch") then
        logError "[FAIL] changed recursion did not reach raw comparison"
  let low ← try
    discard <| TemplateAudit.checkArguments ``checked #[mkConst ``recursiveData] 1
    pure false
  catch error => pure ((← error.toMessageData.toString).startsWith "incomplete_closure:E8")
  unless low do logError "[FAIL] recursive_lower_only_budget"
  if low then logInfo "[PASS] recursive_lower_only_budget"

-- The public async-declaration view is the same native metadata boundary used
-- by the imported-plan controls. No mutated declaration is committed to the
-- fixture; each branch is restored before the next check.
private def withDefinitionView (info : DefinitionVal) (action : Name → MetaM α) : MetaM α := do
  let saved ← getEnv
  let name := info.name.str "mutationView"
  let group := info.all.map fun n => if n == info.name then name else n
  let info := { info with name := name, all := group }
  let branch ← saved.addConstAsync name .defn
    (checkMayContain := false)
  branch.commitConst saved (info? := some (.defnInfo info))
    (exportedInfo? := some (.defnInfo info))
  branch.commitCheckEnv saved
  withEnv branch.mainEnv do
    let .defnInfo current ← getConstInfo info.name | throwError "missing definition view"
    unless current.all == info.all && current.value == info.value &&
        current.levelParams == info.levelParams do
      throwError "mutation did not reach the declaration lookup boundary"
    action name

private def expectRejected (label : String) (expression : Expr) (rule : String) : MetaM Unit := do
  let result ← RegistrationGates.templateArgumentsCurrent ``checked #[expression] 524288 #[`List]
  let ok := match result with
    | .error reason => reason.contains rule
    | .ok _ => false
  unless ok do throwError "[FAIL] {label}: {repr result}"
  logInfo m!"[PASS] {label} rule={rule}"

local macro "primitivePinCheck" : term =>
  pure (mkIdent ((Name.num `_private.LeanInformationAudit.Registry.Enrollment 0) ++
    `LeanInformationAudit.TemplateAudit.checkPrimitivePin))

local macro "primitivePinState" : term =>
  pure (mkIdent ((Name.num `_private.LeanInformationAudit.Registry.Enrollment 0) ++
    `LeanInformationAudit.TemplateAudit.CompileState.mk))

run_meta do
  let .defnInfo dataInfo ← getConstInfo ``recursiveData | throwError "missing recursive data"
  let source := dataInfo.value
  let .defnInfo original ← getConstInfo ``localAll
    | throwError "missing actual recursive definition"
  let replaceSource := fun name => source.replace fun e =>
    if e.isConstOf original.name then some (mkConst name e.constLevels!) else none
  -- Source-equation bookkeeping is not a substitute for the checked body.
  let metadataOnly ← withDefinitionView { original with all := [] } fun name => do
    RegistrationGates.templateArgumentsCurrent ``checked #[replaceSource name] 524288 #[`List]
  unless metadataOnly.isOk do throwError "[FAIL] kernel_body_authority: {repr metadataOnly}"
  logInfo "[PASS] kernel_body_authority_ignores_empty_equation_metadata"
  withDefinitionView { original with all := [original.name, ``changedData] } fun name => do
    expectRejected "forged_mutual_metadata" (replaceSource name) "E5.recursive_definition"
  let .lam n domain body _ := original.value | throwError "missing recursive binder"
  withDefinitionView { original with value := .lam n domain body .implicit } fun name => do
    expectRejected "changed_recursive_binder" (replaceSource name) "E5.structural_binder"
  withDefinitionView { original with levelParams := [`unexpected] } fun name => do
    -- Native type inference rejects the malformed occurrence before the E5
    -- application judgment can inspect its universe arity.
    expectRejected "changed_recursive_universe" (replaceSource name)
      "incorrect number of universe levels"
  let .defnInfo primitive ← getConstInfo `Nat.bitwise | throwError "missing primitive"
  let boolOperation ← mkArrow (mkConst `Bool) (← mkArrow (mkConst `Bool) (mkConst `Bool))
  let wrongBody := Expr.lam `f boolOperation (.lam `n (mkConst `Nat)
    (.lam `m (mkConst `Nat) (.bvar 1) .default) .default) .default
  unless ← isDefEq (← inferType wrongBody) primitive.type do
    throwError "wrong-body control must have the pinned primitive type"
  -- Exercise the production pin check with the current name, owner, type and
  -- levels but a different, independently type-checked logical body. Imported
  -- constants cannot be shadowed by Lean's async declaration overlay.
  let rejected ← try
    discard <| (primitivePinCheck
      (.defnInfo { primitive with value := wrongBody })).run
      (primitivePinState 524288 none {} 0 #[] #[] {} {} false false #[])
    pure false
  catch error => pure ((← error.toMessageData.toString).contains "E5.structural_identity")
  unless rejected do throwError "[FAIL] same_name_wrong_primitive_body"
  logInfo "[PASS] same_name_wrong_primitive_body"
  let .defnInfo erased ← getConstInfo ``erasedInput | throwError "missing erased input"
  expectRejected "erased_recursive_input" erased.value "E3.closed_decision"
  withLocalDeclD `b (mkConst ``Bool) fun b => do
    let proofBearing ← mkAppM ``recursiveWithProof #[mkConst ``checked, b]
    expectRejected "recursive_target_proof_laundering"
      (← mkLambdaFVars #[b] proofBearing) "forbidden_dependency"

end LeanInformationAudit.Tests.RecursiveBindingControls

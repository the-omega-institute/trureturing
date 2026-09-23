import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredConstructorProjection
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

structure State where
  flag : Bool
  outcome : Bool → Bool
  deriving DecidableEq

instance : Fintype State := Fintype.ofEquiv (Bool × (Bool → Bool)) {
  toFun := fun p => ⟨p.1, p.2⟩
  invFun := fun s => (s.flag, s.outcome)
  left_inv := by intro p; cases p; rfl
  right_inv := by intro s; cases s; rfl }

structure Unenrolled where
  flag : Bool
  outcome : Bool → Bool

structure Parameterized (α : Type) where
  outcome : α → Bool

class ClassState where
  flag : Bool

theorem target : ∀ b : Bool, b = b.not.not := by intro b; exact (Bool.not_not b).symm

def fieldTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => s.outcome s.flag)

noncomputable def recursorTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => State.rec (fun b f => f b) s)

-- Report a failed assertion as a named semantic failure, so mutations cannot
-- count an unrelated elaboration error as a red-side pin.
private def check (label : String) (actual expected : Option String) : MetaM Unit := do
  if actual == expected then logInfo m!"[PASS] {label}"
  else logError m!"[FAIL] {label}: expected={repr expected}; actual={repr actual}"

private def argument (e : Expr) (constructors : Array Name) : MetaM (Option String) := do
  try
    discard <| checkArguments ``target #[e] 524288 constructors
    return none
  catch error => return some (← error.toMessageData.toString)

/-- info: [PASS] enrolled_raw_projection -/
#guard_msgs in
run_meta do
  withLocalDeclD `s (mkConst ``State) fun s => do
    check "enrolled_raw_projection" (← argument (.proj ``State 0 s) #[``State]) none

/-- info: [PASS] enrolled_function_projection -/
#guard_msgs in
run_meta do
  withLocalDeclD `s (mkConst ``State) fun s => do
    check "enrolled_function_projection"
      (← argument (mkApp (mkConst ``State.outcome) s) #[``State]) none

/-- info: [PASS] parameterized_projection_application -/
#guard_msgs in
run_meta do
  withLocalDeclD `s (mkApp (mkConst ``Parameterized) (mkConst ``Bool)) fun s => do
    check "parameterized_projection_application"
      (← argument (mkAppN (mkConst ``Parameterized.outcome)
        #[mkConst ``Bool, s, mkConst ``Bool.true]) #[``Parameterized]) none

/-- info: [PASS] non_enrolled_projection_rejected -/
#guard_msgs in
run_meta do
  withLocalDeclD `s (mkConst ``Unenrolled) fun s => do
    check "non_enrolled_projection_rejected"
      (← argument (.proj ``Unenrolled 1 s) #[]) (some "unclassified_form:E3.projection")

/-- info: [PASS] class_projection_rejected -/
#guard_msgs in
run_meta do
  withLocalDeclD `s (mkConst ``ClassState) fun s => do
    check "class_projection_rejected"
      (← argument (mkApp (mkConst ``ClassState.flag) s) #[``ClassState])
      (some "unclassified_form:E3.projection")

/-- info: [PASS] enrolled_structural_descent_rejected -/
#guard_msgs in
run_cmd do
  let saved ← get
  let result ← enroll ``recursorTemplate #[``State]
  set saved
  liftTermElabM <| check "enrolled_structural_descent_rejected"
    (match result with | .ok () => none | .error reason => some reason)
    (some "unclassified_form:E4c.structural_descent")

register_information_template fieldTemplate constructors 1 [State]

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype State
  signature := cutSignature State Bool
  Law r := ∀ s : State, r.readout () s = (s.outcome s.flag).not.not

instance : DecidableEq arena.State := inferInstanceAs (DecidableEq State)

information_theorem validated in arena
  readout via (fieldTemplate)
  primitives fieldTemplate
  : ∀ s : State, s.outcome s.flag = (s.outcome s.flag).not.not := by
    intro s
    exact (Bool.not_not _).symm

/-- info: [PASS] constructor_field_binding_declared_validated -/
#guard_msgs in
run_meta do
  let some row := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``validated)
    | throwError "setup: missing constructor field binding"
  let actual := match row.result with
    | .declaredValidated _ => none
    | .declaredUnresolved reason => some reason
    | .undeclared => some "undeclared"
  check "constructor_field_binding_declared_validated" actual none

end LeanInformationAudit.Tests.DeclaredConstructorProjection

import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

noncomputable section

namespace LeanInformationAudit.Tests.DeclaredEnumerationDispatch
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

inductive Direction where
  | left | middle | right
  deriving DecidableEq

instance : Fintype Direction where
  elems := {.left, .middle, .right}
  complete := by intro d; cases d <;> simp

structure State where
  direction : Direction
  flag : Bool
  deriving DecidableEq

instance : Fintype State := Fintype.ofEquiv (Direction × Bool) {
  toFun := fun p => ⟨p.1, p.2⟩
  invFun := fun s => (s.direction, s.flag)
  left_inv := by intro p; cases p; rfl
  right_inv := by intro s; cases s; rfl }

structure Pair where
  first : Bool
  second : Bool

structure Holder where
  field : Pair

noncomputable def recRead (s : State) : Bool :=
  Direction.rec false s.flag true s.direction

noncomputable def casesRead (s : State) : Bool :=
  Direction.casesOn s.direction false s.flag true

def matchRead (s : State) : Bool :=
  match s.direction with
  | .left => false
  | .middle => s.flag
  | .right => true

noncomputable def recTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => recRead s)

noncomputable def casesTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => casesRead s)

def matchTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => matchRead s)

noncomputable def slotTemplate (direction : Direction) :
    PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => Direction.rec false s.flag true direction)

noncomputable def pairTemplate : PrimitiveRealization (cutSignature Holder Bool) :=
  cutRealization (fun s => Pair.rec (fun a b => Bool.and a b) s.field)

-- A genuinely dependent motive, with its family supplied as an open parameter.
noncomputable def dependentTemplate (P : Direction → Type)
    (a : P .left) (b : P .middle) (c : P .right) (f : (d : Direction) → P d → Bool) :
    PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => f s.direction (Direction.rec (motive := P) a b c s.direction))

noncomputable def boolTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => Bool.rec false true s.flag)

-- Extra arguments after the major premise must still be checked and retained.
noncomputable def extraTemplate : PrimitiveRealization (cutSignature State Bool) :=
  cutRealization (fun s => Direction.rec (fun b : Bool => b)
    (fun b => b.not) (fun b => Bool.and b s.flag) s.direction s.flag)

theorem target : ∀ b : Bool, b = b.not.not := by
  intro b; exact (Bool.not_not b).symm

private def check (label : String) (actual expected : Option String) : MetaM Unit := do
  if actual == expected then logInfo m!"[PASS] {label}"
  else logError m!"[FAIL] {label}: expected={repr expected}; actual={repr actual}"

private def argument (e : Expr) (constructors : Array Name) : MetaM (Option String) := do
  try
    discard <| checkArguments ``target #[e] 524288 constructors
    return none
  catch error => return some (← error.toMessageData.toString)

run_meta do
  for (name, label) in #[(``recRead, "supplied_rec_dispatch"),
      (``casesRead, "supplied_casesOn_dispatch"), (``matchRead, "supplied_match_dispatch")] do
    withLocalDeclD `s (mkConst ``State) fun s => do
      let e ← mkLambdaFVars #[s] (mkApp (mkConst name) s)
      check label (← argument e #[``Direction, ``State]) none
  -- Only the recursor is tested here: a supplied carrier can be an open type
  -- without granting constructor enrollment to its eliminator.
  withLocalDeclD `d (mkConst ``Direction) fun d => do
    let motive := mkLambda `d .default (mkConst ``Direction) (mkConst ``Bool)
    let e := mkAppN (mkConst ``Direction.rec [Level.one])
      #[motive, mkConst ``Bool.false, mkConst ``Bool.true, mkConst ``Bool.false, d]
    check "unenrolled_enumeration_rejected" (← argument e #[])
      (some "unclassified_form:E4.recursion:LeanInformationAudit.Tests.DeclaredEnumerationDispatch.Direction.rec")

run_cmd do
  let cases : Array (String × Name × Array Name × Option String) := #[
    ("template_rec_dispatch", ``recTemplate, #[``Direction, ``State], none),
    ("template_casesOn_dispatch", ``casesTemplate, #[``Direction, ``State], none),
    ("template_match_dispatch", ``matchTemplate, #[``Direction, ``State], none),
    ("template_slot_dispatch", ``slotTemplate, #[``Direction, ``State], none),
    ("non_enumeration_field_rejected", ``pairTemplate, #[``Pair, ``Holder],
      some "unclassified_form:E4c.structural_descent"),
    ("dependent_motive_rejected", ``dependentTemplate, #[``Direction, ``State],
      some "unclassified_form:E4c.structural_descent"),
    ("bool_rec_control", ``boolTemplate, #[``Direction, ``State], none),
    ("extra_arguments_dispatch", ``extraTemplate, #[``Direction, ``State], none)]
  for (label, name, constructors, expected) in cases do
    let saved ← get
    let result ← enroll name constructors
    set saved
    liftTermElabM <| check label
      (match result with | .ok () => none | .error reason => some reason) expected

register_information_template recTemplate constructors 1 [Direction, State]
register_information_template casesTemplate constructors 1 [Direction, State]
register_information_template matchTemplate constructors 1 [Direction, State]
register_information_template slotTemplate constructors 1 [Direction, State]
register_information_template boolTemplate constructors 1 [Direction, State]

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype State
  signature := cutSignature State Bool
  Law r := ∀ s : State, r.readout () s = (r.readout () s).not.not

instance : DecidableEq arena.State := inferInstanceAs (DecidableEq State)

information_theorem recValidated in arena
  readout via (recTemplate)
  primitives recTemplate
  : ∀ s : State, recRead s = (recRead s).not.not := by
    intro s; exact (Bool.not_not _).symm

information_theorem casesValidated in arena
  readout via (casesTemplate)
  primitives casesTemplate
  : ∀ s : State, casesRead s = (casesRead s).not.not := by
    intro s; exact (Bool.not_not _).symm

information_theorem matchValidated in arena
  readout via (matchTemplate)
  primitives matchTemplate
  : ∀ s : State, matchRead s = (matchRead s).not.not := by
    intro s; exact (Bool.not_not _).symm

information_theorem slotValidated in arena
  readout via (slotTemplate .middle)
  primitives (slotTemplate .middle)
  : ∀ s : State, s.flag = s.flag.not.not := by
    intro s; exact (Bool.not_not _).symm

information_theorem boolValidated in arena
  readout via (boolTemplate)
  primitives boolTemplate
  : ∀ s : State, Bool.rec (motive := fun _ => Bool) false true s.flag =
      (Bool.rec (motive := fun _ => Bool) false true s.flag).not.not := by
    intro s; exact (Bool.not_not _).symm

run_meta do
  for (name, label) in #[(``recValidated, "rec_binding_declared_validated"),
      (``casesValidated, "casesOn_binding_declared_validated"),
      (``matchValidated, "match_binding_declared_validated"),
      (``slotValidated, "slot_binding_declared_validated"),
      (``boolValidated, "bool_binding_declared_validated")] do
    let some row := (TemplateBinding.records (← getEnv)).find?
        (·.occurrence.key.theoremName == name) | throwError "setup: missing binding {name}"
    let actual := match row.result with
      | .declaredValidated _ => none
      | .declaredUnresolved reason => some reason
      | .undeclared => some "undeclared"
    check label actual none

end LeanInformationAudit.Tests.DeclaredEnumerationDispatch

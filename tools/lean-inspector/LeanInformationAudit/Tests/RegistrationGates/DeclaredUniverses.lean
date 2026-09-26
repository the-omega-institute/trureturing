import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredUniverses
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def template.{u, v} (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  let First : Type u := PUnit.{u + 1}
  let Second : Type v := PUnit.{v + 1}
  cutRealization f

register_information_template template

def descriptor.{u, v} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{u, v} (fun x : Bool => x)

def renamed.{a, b} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{a, b} (fun x : Bool => x)

def permuted.{a, b} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{b, a} (fun x : Bool => x)

def short.{a} : PrimitiveRealization (cutSignature Bool Bool) :=
  template.{a, a} (fun x : Bool => x)

-- An explicit, rigid two-universe statement supplies the occurrence context.
-- The assessor fixture changes only the extraction declaration in that context;
-- no synthetic record is inserted into the persistent inventory.
theorem statement.{u, v} : ∀ (_ : PUnit.{u + 1}) (_ : PUnit.{v + 1}) (x : Bool),
    x = x.not.not := by
  intro _ _ x
  exact (Bool.not_not x).symm

private def observe (event : TemplateOccurrenceEvent) (actual : Name)
    (descriptor : Expr) (label : String) (expected : Option String := none) : MetaM Unit := do
  let record ← TemplateBinding.assess { event with realizationName := actual } (some {
    key := event.key, arena := event.arena, descriptor := some descriptor,
    owner := (← getEnv).header.mainModule })
  let ok := match record.result, expected with
    | .declaredValidated certificate, none => !certificate.evidenceRef.isEmpty
    | .declaredUnresolved diagnostic, some rule =>
      (diagnostic.splitOn s!"reason=unclassified_form rule={rule} site=").length == 2
    | _, _ => false
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
  unless ok do
    if let .declaredUnresolved diagnostic := record.result then logInfo diagnostic

run_meta do
  let some source := (TemplateBinding.inventory (← getEnv)).find?
      (·.key.theoremName == `LeanInformationAudit.Tests.DeclaredBindings.validated)
    | throwError "setup: missing source occurrence"
  let statement ← getConstInfo ``statement
  let .defnInfo declared ← getConstInfo ``descriptor | throwError "setup: descriptor"
  unless statement.levelParams == [`u, `v] && declared.levelParams == [`u, `v] do
    throwError "setup: independent rigid universe telescope"
  let .ok (identity, _) := TemplateAudit.rawStatementIdentity statement.levelParams statement.type
    | throwError "setup: statement identity"
  let event := { source with
    key := { source.key with theoremName := statement.name }
    statement := statement.type, levelParams := statement.levelParams, statementIdentity := identity }
  observe event ``descriptor declared.value "same_universe_names_accepted"
  observe event ``renamed declared.value "positional_universe_renaming_accepted"
  observe event ``permuted declared.value "positional_universe_permutation_rejected"
    (some "dtr.realization_mismatch")
  observe event ``short declared.value "positional_universe_arity_rejected"
    (some "dtr.extraction_universes")

noncomputable def polymorphicArena.{u} : PrimitiveLawArena.{u, 0, 0} where
  toArena := {
    State := PUnit.{u + 1}
    stateFintype := inferInstance
    stateDecidableEq := Classical.decEq _ }
  signature := {
    Index := Unit, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law realization := ∀ state, realization.readout () state = false

noncomputable def polymorphicReadout.{u} :
    PrimitiveRealization polymorphicArena.{u}.signature :=
  ⟨fun _ _ => false, Fin.elim0⟩

noncomputable instance : DecidableEq polymorphicArena.{u}.State :=
  polymorphicArena.{u}.toArena.stateDecidableEq

theorem namedStatement.{u} : polymorphicArena.{u}.Law polymorphicReadout.{u} :=
  by intro _; rfl
theorem namedBridge.{u} : LegacyPrimitiveRealization polymorphicArena.{u}
    (polymorphicArena.{u}.Law polymorphicReadout.{u}) polymorphicReadout.{u} :=
  ⟨Iff.rfl⟩

theorem inlineStatement.{u} : polymorphicArena.{u}.Law polymorphicReadout.{u} :=
  by intro _; rfl
register_information_theorem inlineStatement in polymorphicArena
  primitives polymorphicReadout.toPrimitiveBundle
  realization inline (polymorphicReadout) := by exact namedBridge

register_information_theorem namedStatement in polymorphicArena
  primitives polymorphicReadout.toPrimitiveBundle realization namedBridge

noncomputable abbrev polymorphicObjectArena.{u} : Arena.{u} := polymorphicArena.{u}.toArena

theorem inlineOccurrenceStatement.{u} :
    polymorphicArena.{u}.Law polymorphicReadout.{u} := by intro _; rfl
register_information_theorem inlineOccurrenceStatement in polymorphicArena
  object_arena polymorphicObjectArena catalog polymorphicInline
  primitives polymorphicReadout.toPrimitiveBundle
  realization inline (polymorphicReadout) := by exact namedBridge

theorem namedOccurrenceStatement.{u} :
    polymorphicArena.{u}.Law polymorphicReadout.{u} := by intro _; rfl
register_information_theorem namedOccurrenceStatement in polymorphicArena
  object_arena polymorphicObjectArena catalog polymorphicNamed
  primitives polymorphicReadout.toPrimitiveBundle realization namedBridge

theorem reorderedStatement.{u, v} :
    (∀ _ : PUnit.{v + 1}, polymorphicArena.{u}.Law polymorphicReadout.{u}) :=
  fun _ _ => rfl
theorem reorderedBridge.{v, u} : LegacyPrimitiveRealization polymorphicArena.{u}
    (∀ _ : PUnit.{v + 1}, polymorphicArena.{u}.Law polymorphicReadout.{u})
    polymorphicReadout.{u} :=
  ⟨fun h => h PUnit.unit, fun h _ => h⟩

register_information_theorem reorderedStatement in polymorphicArena
  primitives polymorphicReadout.toPrimitiveBundle realization reorderedBridge

theorem reorderedOccurrenceStatement.{u, v} :
    (∀ _ : PUnit.{v + 1}, polymorphicArena.{u}.Law polymorphicReadout.{u}) :=
  fun _ _ => rfl
register_information_theorem reorderedOccurrenceStatement in polymorphicArena
  object_arena polymorphicObjectArena catalog polymorphicReordered
  primitives polymorphicReadout.toPrimitiveBundle realization reorderedBridge

theorem diagonalStatement.{u, v} :
    (∀ _ : PUnit.{v + 1}, polymorphicArena.{u}.Law polymorphicReadout.{u}) :=
  fun _ _ => rfl
theorem diagonalBridge.{u} : LegacyPrimitiveRealization polymorphicArena.{u}
    (∀ _ : PUnit.{u + 1}, polymorphicArena.{u}.Law polymorphicReadout.{u})
    polymorphicReadout.{u} :=
  ⟨fun h => h PUnit.unit, fun h _ => h⟩

/-- error: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.DeclaredUniverses.diagonalStatement -/
#guard_msgs (error) in
register_information_theorem diagonalStatement in polymorphicArena
  primitives polymorphicReadout.toPrimitiveBundle realization diagonalBridge

def finiteReadout : PrimitiveRealization DeclaredBindings.arena.signature :=
  cutRealization (fun x : Bool => x)

noncomputable def statementOnlyDepth : Nat := Classical.choice ⟨0⟩

theorem finiteLaw : DeclaredBindings.arena.Law finiteReadout := by
  intro x
  exact (Bool.not_not x).symm

theorem finiteStatement :
    DeclaredBindings.arena.Law finiteReadout ∧ statementOnlyDepth = statementOnlyDepth :=
  ⟨finiteLaw, rfl⟩
theorem finiteBridge : LegacyPrimitiveRealization DeclaredBindings.arena
    (DeclaredBindings.arena.Law finiteReadout ∧ statementOnlyDepth = statementOnlyDepth)
    finiteReadout :=
  ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

register_information_theorem finiteStatement in DeclaredBindings.arena
  primitives finiteReadout.toPrimitiveBundle realization finiteBridge

run_meta do
  let env ← getEnv
  for (theoremName, expectedNoncomputable) in [
      (``namedStatement, true), (``inlineStatement, true),
      (``namedOccurrenceStatement, true), (``inlineOccurrenceStatement, true),
      (``finiteStatement, false), (``reorderedStatement, true),
      (``reorderedOccurrenceStatement, true)] do
    let some entry := InformationRegistry.find? env theoremName
      | throwError "polymorphic registration missing: {theoremName}"
    let .defnInfo unit ← getConstInfo entry.unitName
      | throwError "polymorphic theorem unit missing: {theoremName}"
    let expectedLevels := if theoremName == ``reorderedStatement ||
        theoremName == ``reorderedOccurrenceStatement then [`u, `v]
      else if expectedNoncomputable then [`u] else []
    unless unit.levelParams == expectedLevels do
      throwError "polymorphic theorem unit lost its universe: {theoremName}"
    if theoremName == ``reorderedStatement ||
        theoremName == ``reorderedOccurrenceStatement then
      unless unit.value.getAppArgs.any
          (· == Lean.mkConst theoremName [Level.param `u, Level.param `v]) &&
          unit.value.getAppArgs.any
          (· == Lean.mkConst entry.realizationName [Level.param `v, Level.param `u]) do
        throwError "reordered theorem unit changed a universe application: {theoremName}"
    unless isNoncomputable env entry.unitName == expectedNoncomputable do
      throwError "theorem unit has the wrong computability: {theoremName}"
    checkWithKernel (mkConst entry.unitName (unit.levelParams.map Level.param))
    let axioms ← collectAxioms entry.unitName
    unless axioms.all (fun ax => ax == ``propext || ax == ``Classical.choice ||
        ax == ``Quot.sound) do
      throwError "polymorphic theorem unit has nonstandard axioms: {theoremName}: {axioms}"

end LeanInformationAudit.Tests.DeclaredUniverses

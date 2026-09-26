import Reg.Support.DependentFamily

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.ExplicitSourceOperands

def readout (n : Nat) := n
def predicate (n : Nat) : Prop := n = 0
instance (n : Nat) : Decidable (predicate n) := inferInstanceAs (Decidable (n = 0))
theorem injective : Function.Injective readout := fun _ _ h => h
theorem admitted : predicate 0 ∧ True := ⟨rfl, True.intro⟩
def dependent (n : Nat) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
def typeInput (_ : Type) : Nat := 0
def proofInput (_ : True) : Nat := 0
theorem dependentUse : dependent 0 = dependent 0 := rfl
theorem typeUse : typeInput Nat = 0 := rfl
theorem proofUse : proofInput True.intro = 0 := rfl

private def rejects (rule : String) (action : SourceScope.M Unit) : MetaM Unit := do
  let result ← try discard <| action.run 524288; pure "accepted"
    catch error => error.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"

run_meta do
  let info ← getConstInfo ``injective
  let selection : SourceSelection := {
    owner := `LeanInformationAuditRegTests.ExplicitSourceOperands
    coordinates := #[]
    readouts := #[{path := #["arg"], functionOperand := true}] }
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some first := scope.readouts[0]? | throwError "missing readout"
  unless scope.readouts.size == 1 && first.rawContext.isEmpty do
    throwError "function source lost original empty scope"
  let ((_, observation), _) ← (SourceScope.atPath info.type #["arg"]).run 524288
  unless first.rawObservation.equal observation do
    throwError "function source lost exact original operand"
  rejects "source.operand_mode" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #["arg"], functionOperand := true, stateBinder := 1}]}
  rejects "source.function_operand" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #[], functionOperand := true}]}
  rejects "source.owner" <| discard <| SourceScope.resolve info {selection with owner := `Wrong}
  for name in #[``dependentUse, ``typeUse, ``proofUse] do
    rejects "source.function_operand" <| discard <| SourceScope.resolve (← getConstInfo name)
      {selection with readouts := #[{path := #["fn", "arg", "fn"], functionOperand := true}]}
  let info ← getConstInfo ``admitted
  let selection : SourceSelection := {
    owner := selection.owner
    coordinates := #[]
    readouts := #[{path := #["fn", "arg"], stateOperand := some #["arg"], booleanPredicate := true}] }
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let predicate := mkApp (mkConst ``predicate) (mkNatLit 0)
  let expected := mkApp2 (mkConst ``And) (← mkEq (← mkDecide predicate) (mkConst ``Bool.true)) (mkConst ``True)
  discard <| (SourceScope.reconstruct scope.expanded expected).run 524288
  rejects "source.statement_reconstruction" <| SourceScope.reconstruct scope.expanded (mkConst ``False)
  rejects "source.state_operand_path" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #["fn", "arg"], stateOperand := some #[], booleanPredicate := true}]}
  rejects "source.observation_data" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #["fn", "arg"], stateOperand := some #["arg"]}]}
  logInfo "[PASS] exact function and Boolean predicate operands; nine rejection boundaries"

end LeanInformationAuditRegTests.ExplicitSourceOperands

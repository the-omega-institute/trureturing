module
public import Lean
public import Init.Data.Erased
import all Init.Data.Erased

/-! A singleton predicate and an explicitly constructed erased value carry their own witness. -/

open Lean
namespace OmegaChecks.InitPort.SingletonSelection

@[expose] public noncomputable def epsilon {α : Sort u} (x : α) : α :=
  @Classical.epsilon α ⟨x⟩ (fun y => y = x)

@[expose] public noncomputable def erased {α : Sort u} (x : α) : α :=
  (Erased.mk x).out

public def witness {α : Sort u} (x : α) : α := x

public theorem epsilonAgreement : @epsilon.{u} = @witness.{u} := by
  funext α x
  exact Classical.epsilon_spec (p := fun y => y = x) ⟨x, rfl⟩

public theorem erasedAgreement : @erased.{u} = @witness.{u} := by
  funext α x
  have h := congrFun (Classical.choose_spec (Erased.mk x).property) x
  exact cast h.symm (Eq.refl x)

/-- Recover the singleton's visible witness. Kernel conversion with the original call
also checks the predicate, its carrier and every remaining argument. -/
public def specialize? (helper : Name) (sub : Expr) : MetaM (Option Expr) := do
  let witness? := do
    if sub.getAppFn.isConstOf ``Erased.out then
      let #[α, erased] := sub.getAppArgs | none
      guard (erased.getAppFn.isConstOf ``Erased.mk)
      let #[_, x] := erased.getAppArgs | none
      return (α, x)
    let #[α, _, predicate] := sub.getAppArgs | none
    let .lam _ _ body _ := predicate | none
    let some (_, bound, x) := body.eq? | none
    guard (bound == .bvar 0 && !x.hasLooseBVars)
    return (α, x)
  let some (α, x) := witness? | return none
  let .const _ levels := sub.getAppFn | return none
  let call := mkApp2 (.const helper levels) α x
  if ← Meta.isDefEq call sub then return some call else return none

end OmegaChecks.InitPort.SingletonSelection

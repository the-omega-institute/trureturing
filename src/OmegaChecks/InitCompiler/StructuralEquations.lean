module

public import Lean

/-! Check a recursive equation at every constructor of a structural argument. -/

open Lean
namespace OmegaChecks.InitCompiler

private def forallConstructors (type : Expr) (check : Expr → MetaM Bool) : MetaM Bool := do
  let type ← Meta.whnf type
  let .const family us := type.getAppFn | return false
  let .inductInfo ind ← getConstInfo family | return false
  unless ind.numIndices == 0 && ind.numParams == type.getAppNumArgs do return false
  for tag in ind.ctors do
    let ctor := mkAppN (mkConst tag us) type.getAppArgs
    unless ← Meta.forallTelescope (← Meta.inferType ctor) (fun fields _ => check (mkAppN ctor fields)) do
      return false
  return true

/-- A bounded index has one constructor. Its natural field is either zero or a successor.
For an empty bound, the proof field itself supplies a kernel-checked contradiction. -/
private def checkFinEquations (fn body : Expr) (args : Array Expr) (index : Expr) : MetaM Bool := do
  let ty ← Meta.whnf (← Meta.inferType index)
  unless ty.isAppOfArity `Omega.Fin 1 do return false
  let env ← getEnv
  let some (.inductInfo fin) := env.find? `Omega.Fin | return false
  unless fin.ctors == [`Omega.Fin.mk] do return false
  let ctor := mkApp (mkConst `Omega.Fin.mk) ty.getAppArgs[0]!
  forallConstructors (mkConst `Nat) fun val => do
    let partialCtor := mkApp ctor val
    Meta.forallTelescope (← Meta.inferType partialCtor) fun proofs _ => do
      let #[h] := proofs | return false
      let full := args.push (mkApp partialCtor h)
      let actual := mkAppN fn full
      let expected := mkAppN body full
      let ctx ← getLCtx
      if Kernel.isDefEqGuarded env ctx actual expected then return true
      let t ← Meta.inferType actual
      let u ← Meta.getLevel t
      let goal := mkApp3 (mkConst `Eq [u]) t actual expected
      let impossible := mkApp2 (mkConst `Omega.Nat.not_succ_le_zero) val h
      let derivation := mkApp2 (mkConst `Omega.False.elim [.zero]) goal impossible
      return (Kernel.check env ctx derivation).toOption.any (Kernel.isDefEqGuarded env ctx goal)

/-- Compare the official one-step equation with the strict function at each constructor.
Specializing the structural argument before the remaining binders preserves dependent indices. -/
public def checkConstructorEquations (name : Name) (levelParams : List Name) (type body : Expr)
    (structural : Nat) : MetaM Unit := do
  let levels := levelParams.map Level.param
  Meta.forallBoundedTelescope type (some structural) fun before rest => do
    unless before.size == structural && rest.isForall do throwError "missing structural argument"
    let family ← Meta.whnf rest.bindingDomain!
    let .const indName us := family.getAppFn | throwError "expected an inductive parameter"
    let .inductInfo ind ← getConstInfo indName | throwError "expected an inductive parameter"
    unless ind.numIndices == 0 && family.getAppNumArgs == ind.numParams && !ind.ctors.isEmpty do
      throwError "expected a nonempty unindexed inductive family"
    for ctorName in ind.ctors do
      let ctor := mkAppN (mkConst ctorName us) family.getAppArgs
      let ctorType ← Meta.inferType ctor
      let checkArg := fun (arg : Expr) => do
        let fn := mkConst name levels
        let args := before.push arg
        let remaining := rest.bindingBody!.instantiate1 arg
        let compare := fun (xs : Array Expr) => do
          return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) (mkAppN fn xs) (mkAppN body xs)
        Meta.forallTelescope remaining fun suffix _ => do
          if ← compare (args ++ suffix) then return true
          if let #[index] := suffix then
            if ← checkFinEquations fn body args index then return true
          if remaining.isForall then
            return ← forallConstructors remaining.bindingDomain! fun val =>
              Meta.forallTelescope (remaining.bindingBody!.instantiate1 val) fun tail _ =>
                compare ((args.push val) ++ tail)
          return false
      if ← Meta.forallTelescope ctorType fun fields _ => checkArg (mkAppN ctor fields) then continue
      -- A nested pattern can inspect a constructor field, such as the name at the head of a list.
      -- Rebuild the dependent suffix for each constructor of that field before comparing the results.
      let mut matchesField := false
      for i in [:ctorType.getForallArity] do
        if ← Meta.forallBoundedTelescope ctorType (some i) fun priorFields next => do
          unless next.isForall do return false
          return ← forallConstructors next.bindingDomain! fun value =>
            Meta.forallTelescope (next.bindingBody!.instantiate1 value) fun suffix _ =>
              checkArg (mkAppN ctor (priorFields.push value ++ suffix)) then
          matchesField := true
          break
      unless matchesField do throwError "recursive equation does not match {name} at {ctorName}"

end OmegaChecks.InitCompiler

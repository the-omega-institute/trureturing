module
public import Lean
public import Init.Data.Array.Lemmas
import all Init.Data.Array.Basic

open Lean
namespace OmegaChecks.InitPort.ArrayModify

/-- The temporary value is written and overwritten at the same valid index. -/
@[expose] public def temporary {α : Type u} {m : Type u → Type v} [Monad m]
    (xs : Array α) (i : Nat) (f : α → m α) (replace : α → α) : m (Array α) := do
  if h : i < xs.size then
    let x := xs[i]
    let scratch := xs.set i (replace x)
    let y ← f x
    pure (scratch.set i y (Nat.lt_of_lt_of_eq h (Array.size_set ..).symm))
  else
    pure xs

public theorem overwritten {α : Type u} {m : Type u → Type v} [Monad m]
    (xs : Array α) (i : Nat) (f : α → m α) (replace : α → α) :
    temporary xs i f replace = xs.modifyM i f := by
  unfold temporary Array.modifyM
  split
  · apply congrArg (Bind.bind (f _))
    funext y
    exact congrArg pure (Array.set_set _ _)
  · rfl

/-- Match the native body to the computation covered by the theorem, including the
exact erased placeholder. The safe image only calls the pinned logical reference. -/
public def check (env : Environment) (native : DefinitionVal) (candidate : Expr) : IO Unit := do
  let levels := native.levelParams.map Level.param
  let some (.defnInfo reference) := env.find? `Array.modifyM | throw <| IO.userError "missing Array.modifyM"
  let some (.thmInfo _) := env.find? ``overwritten | throw <| IO.userError "missing array overwrite theorem"
  let axioms ← (collectAxioms ``overwritten : CoreM _).toIO'
    {fileName := "<array overwrite>", fileMap := default} {env}
  unless axioms.all (#[`propext, `Quot.sound, `Classical.choice].contains ·) do
    throw <| IO.userError s!"unexpected axiom in the array overwrite theorem: {axioms}"
  unless native.name == `Array.modifyMUnsafe && native.safety == .unsafe && reference.safety == .safe &&
      Compiler.getImplementedBy? env reference.name == some native.name &&
      env.getModuleIdxFor? native.name == env.getModuleIdx? `Init.Data.Array.Basic &&
      env.getModuleIdxFor? reference.name == env.getModuleIdxFor? native.name &&
      candidate.equal (.const reference.name levels) do
    throw <| IO.userError "invalid native array modification reference"
  let verify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let #[α, _, _, _, _, _] := args | throwError "unexpected modification inputs"
    let functionType ← mkArrow α α
    Meta.withLocalDeclD `replace functionType fun replace => do
      let model := mkAppN (mkConst ``temporary levels) args
      let unit := mkConst `Unit
      let junk ← Meta.mkAppOptM `unsafeCast #[some unit, some α, some (mkConst `Unit.unit)]
      let fill := Expr.lam `old α junk .default
      let actual ← Meta.mkLambdaFVars args (mkApp model fill)
      unless Kernel.isDefEqGuarded env {} actual native.value do
        throwError "native update differs from the certified two writes"
      let claim ← Meta.mkEq (mkApp model replace) (mkAppN candidate args)
      let inputs := args.push replace
      let claim ← Meta.mkForallFVars inputs claim
      let proof := mkConst ``overwritten levels
      let .ok inferred := Kernel.check env {} proof | throwError "missing array overwrite theorem"
      unless Kernel.isDefEqGuarded env {} claim inferred do
        throwError "array overwrite theorem does not cover the native computation"
  verify.run' |>.toIO' {fileName := "<array overwrite>", fileMap := default} {env}

end OmegaChecks.InitPort.ArrayModify

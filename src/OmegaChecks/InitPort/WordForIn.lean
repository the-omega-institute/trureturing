module
public import Lean
public import OmegaChecks.InitPort.Alternatives.WordForIn
public import Init.Data.UInt.Lemmas
import all OmegaChecks.InitPort.Alternatives.WordForIn
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.FloatArray.Basic

namespace OmegaChecks.InitPort.WordForIn

open OmegaChecks.InitPort.Alternatives (forInStep wordForIn)

private structure Equations {β : Type v} {m : Type v → Type w} [Monad m] (size : Nat) (limit : USize)
    (action : (i : USize) → i.toNat < size → β → m (ForInStep β)) (loop : USize → β → m β) : Prop where
  stop (b : β) : loop limit b = pure b
  step (i : USize) (b : β) (h : i.toNat < size) :
    loop i b = forInStep i limit b (fun _ => action i h b) (fun c => loop (i+1) c)

private theorem simulate {β : Type v} {m : Type v → Type w} [Monad m] (size : Nat) (limit : USize)
    (action : (i : USize) → i.toNat < size → β → m (ForInStep β)) (loop : USize → β → m β)
    (eqs : Equations size limit action loop) (fuel j : Nat) (b : β) (distance : j + fuel = limit.toNat)
    (bound : limit.toNat ≤ size) :
    wordForIn size limit action fuel (.ofNat j) b = loop (.ofNat j) b := by
  induction fuel generalizing j b with
  | zero =>
    have e : j = limit.toNat := distance
    subst j
    rw [USize.ofNat_toNat]
    exact (eqs.stop b).symm
  | succ n ih =>
    have valid : (USize.ofNat j).toNat < size := by
      exact Nat.lt_of_le_of_lt (Nat.mod_le j USize.size) (by omega)
    have next (c : β) := ih (j+1) c (by omega)
    simp only [USize.ofNat_add] at next
    rw [eqs.step _ _ valid]
    simp only [wordForIn, valid, ↓reduceDIte]
    exact congrArg (forInStep (USize.ofNat j) limit b (fun _ => action _ valid b)) (funext next)

private theorem allInputs {β : Type v} {m : Type v → Type w} [Monad m] (size : Nat)
    (action : (i : USize) → i.toNat < size → β → m (ForInStep β)) (b : β) (loop : USize → β → m β)
    (eqs : Equations size (.ofNat size) action loop) :
    wordForIn size (.ofNat size) action (USize.ofNat size).toNat 0 b = loop 0 b :=
  simulate _ _ _ _ eqs _ 0 b (Nat.zero_add _) (Nat.mod_le size _)

open Lean

public def supported (n : Name) : Bool :=
  [`Array.forIn'Unsafe, `ByteArray.forInUnsafe, `FloatArray.forInUnsafe].contains n

public def check (env : Environment) (native : DefinitionVal) (candidate : Expr) : IO Unit := do
  let family := native.name.getPrefix
  let owner := env.getModuleIdx? (`Init.Data ++ family ++ `Basic)
  let reference := family ++ (if family == `Array then `forIn' else `forIn)
  let some helper := native.value.getUsedConstants.find? (fun n => privateToUserName n == native.name ++ `loop)
    | throw <| IO.userError s!"missing native traversal loop at {native.name}"
  let some (.defnInfo raw) := env.find? helper | throw <| IO.userError s!"missing native traversal loop {helper}"
  unless supported native.name && native.safety == .unsafe && raw.safety == .unsafe && owner.isSome &&
      [native.name, helper, reference].all (fun n => env.getModuleIdxFor? n == owner) &&
      Compiler.getImplementedBy? env reference == some native.name do
    throw <| IO.userError s!"invalid native traversal binding {native.name}"
  let verify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let (param, args') := if family == `Array then (#[args[0]!], args.extract 1 args.size) else (#[], args)
    let #[β, m, inst, xs, b, f] := args' | throwError "unexpected traversal inputs"
    let witness := fun (locals : Array Expr) (a b : Expr) => do
      let a ← Meta.mkLambdaFVars locals a
      let b ← Meta.mkLambdaFVars locals b
      unless Kernel.isDefEqGuarded env {} a b do throwError "native traversal differs from the bounded model at {native.name}"
    let apply (name : Name) (xs : Array Expr) := Meta.mkAppOptM name (xs.map some)
    let size ← apply (family ++ `size) (param.push xs)
    let limit ← apply (family ++ `usize) (param.push xs)
    let get ← apply (family ++ `uget) (param.push xs)
    let u := mkConst `USize
    let action ← Meta.withLocalDeclD `i u fun i => do
      let .forallE _ bound _ _ ← Meta.whnf (← Meta.inferType (mkApp get i)) | throwError "missing read bound"
      Meta.withLocalDeclD `h bound fun h => do
        let elem := mkApp2 get i h
        let visit := mkApp f elem
        let visit ← if family != `Array then pure visit else
          pure (mkApp visit (← apply `Array.getElem_mem (param ++ #[xs, mkApp (mkConst `USize.toNat) i, h])))
        Meta.mkLambdaFVars #[i, h] visit
    let params := param ++ #[β, m, inst, xs, f, limit]
    let levels := native.levelParams.map Level.param
    let recursion := mkAppN (mkConst helper levels) params
    let loopType ← Meta.inferType recursion
    Meta.withLocalDeclD `loop loopType fun loop => do
      let symbolic := fun (e : Expr) => e.replace fun sub => if sub == recursion then some loop else none
      let nativeEntry := symbolic (← Meta.zetaReduce (native.value.beta args))
      let conditions ← apply ``Equations #[β, m, inst, size, limit, action, loop]
      let claim ← Meta.mkEq (mkAppN candidate args) nativeEntry
      let proof ← apply ``allInputs #[β, m, inst, size, action, b, loop]
      witness (args.push loop) (← Meta.inferType proof) (← mkArrow conditions claim)
      let closed ← Meta.mkLambdaFVars (args.push loop) proof
      let .ok _ := Kernel.check env {} closed | throwError "invalid bounded traversal simulation"
      Meta.forallTelescope loopType fun indices _ => do
        let #[i, initial] := indices | throwError "unexpected traversal loop inputs"
        let .forallE _ bound _ _ ← Meta.whnf (← Meta.inferType (mkApp action i)) | throwError "missing traversal bound"
        let read := mkApp3 action i (mkApp (mkConst `lcProof) bound) initial
        let update ← Meta.withLocalDeclD `unit (mkConst `Unit) fun unit => Meta.mkLambdaFVars #[unit] read
        let next := mkApp loop (mkApp2 (mkConst `USize.add) i (mkApp (mkConst `USize.ofNat) (mkNatLit 1)))
        let step ← apply ``forInStep #[β, m, inst, i, limit, initial, update, next]
        witness ((args.push loop) ++ indices) (symbolic (raw.value.beta (params ++ indices))) step
  verify.run' |>.toIO' {fileName := "<bounded machine-word traversal>", fileMap := default} {env}

end OmegaChecks.InitPort.WordForIn

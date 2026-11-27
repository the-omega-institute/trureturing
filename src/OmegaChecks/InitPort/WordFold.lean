module
public import Lean
public import OmegaChecks.InitPort.Alternatives.WordFold
public import Init.Data.UInt.Lemmas
import all OmegaChecks.InitPort.Alternatives.WordFold
import all Init.Data.Array.Basic
import all Init.Data.FloatArray.Basic
import all Init.Data.ByteArray.Basic

namespace OmegaChecks.InitPort.WordFold

open OmegaChecks.InitPort.Alternatives (foldEntry foldStep foldLoop wordFold)

private structure Equations {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (size : Nat) (get : (i : USize) → i.toNat < size → α) (f : β → α → m β)
    (loop : USize → USize → β → m β) : Prop where
  stop (i : USize) (b : β) : loop i i b = pure b
  step (i last : USize) (b : β) (h : i.toNat < size) :
    loop i last b = foldStep i last b (fun _ => f b (get i h)) (fun c => loop (i+1) last c)

private theorem simulate {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (size : Nat) (get : (i : USize) → i.toNat < size → α) (f : β → α → m β)
    (loop : USize → USize → β → m β) (eqs : Equations size get f loop)
    (fuel j last : Nat) (b : β) (distance : j + fuel = last) (bound : last ≤ size) :
    foldLoop size get f (.ofNat last) fuel (.ofNat j) b = loop (.ofNat j) (.ofNat last) b := by
  induction fuel generalizing j b with
  | zero =>
    have e : j = last := distance
    subst last
    exact (eqs.stop _ _).symm
  | succ n ih =>
    have valid : (USize.ofNat j).toNat < size := by
      exact Nat.lt_of_le_of_lt (Nat.mod_le j USize.size) (by omega)
    have next (c : β) := ih (j + 1) c (by omega)
    simp only [USize.ofNat_add] at next
    rw [eqs.step _ _ _ valid]
    simp only [foldLoop, valid, ↓reduceDIte]
    exact congrArg (foldStep (USize.ofNat j) (USize.ofNat last) b (fun _ => f b (get _ valid)))
      (funext next)

private theorem allInputs {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (size : Nat) (get : (i : USize) → i.toNat < size → α) (f : β → α → m β)
    (b : β) (start stop : Nat) (loop : USize → USize → β → m β) (eqs : Equations size get f loop) :
    wordFold size get f b start stop =
      foldEntry size start stop b (fun a z => loop (.ofNat a) (.ofNat z)) := by
  unfold wordFold foldEntry
  split
  · next order =>
    split
    · next bound => exact simulate _ _ _ _ eqs _ _ _ _ (Nat.add_sub_of_le (Nat.le_of_lt order)) bound
    · split
      · next bound => exact simulate _ _ _ _ eqs _ _ _ _ (Nat.add_sub_of_le (Nat.le_of_lt bound)) (Nat.le_refl _)
      · rfl
  · rfl

open Lean

public def supported (n : Name) : Bool :=
  [`Array.foldlMUnsafe, `ByteArray.foldlMUnsafe, `FloatArray.foldlMUnsafe].contains n

/-- Compare the actual native entry and recursive body with the two operations of the
simulation, keeping the recursive call free during the entry comparison. -/
public def check (env : Environment) (native : DefinitionVal) (candidate : Expr) : IO Unit := do
  let family := native.name.getPrefix
  let owner := env.getModuleIdx? (`Init.Data ++ family ++ `Basic)
  let some helper := native.value.getUsedConstants.find? (fun n => privateToUserName n == native.name ++ `fold)
    | throw <| IO.userError s!"missing recursive fold call at {native.name}"
  let some (.defnInfo raw) := env.find? helper | throw <| IO.userError s!"missing native fold loop {helper}"
  unless supported native.name && native.safety == .unsafe && raw.safety == .unsafe &&
      owner.isSome && [native.name, helper, family ++ `foldlM].all (fun n => env.getModuleIdxFor? n == owner) &&
      Compiler.getImplementedBy? env (family ++ `foldlM) == some native.name do
    throw <| IO.userError s!"invalid native fold binding {native.name}"
  let verify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let (α, param, args') := if family == `Array then (args[0]!, #[args[0]!], args.extract 1 args.size)
      else (mkConst (if family == `ByteArray then `UInt8 else `Float), #[], args)
    let #[β, m, inst, f, b, xs, start, stop] := args' | throwError "unexpected array fold inputs"
    let witness := fun (locals : Array Expr) (a b : Expr) => do
      let a ← Meta.mkLambdaFVars locals a
      let b ← Meta.mkLambdaFVars locals b
      unless Kernel.isDefEqGuarded env {} a b do throwError "native fold differs from its bounded model at {native.name}"
    let apply (name : Name) (xs : Array Expr) := Meta.mkAppOptM name (xs.map some)
    let size ← apply (family ++ `size) (param.push xs)
    let get ← apply (family ++ `uget) (param.push xs)
    let fields := #[α, β, m, inst, size, get, f]
    let word ← apply ``wordFold (fields ++ #[b, start, stop])
    witness args (mkAppN candidate args) word
    let params := param ++ #[β, m, inst, f, xs]
    let levels := native.levelParams.map Level.param
    let recursion := mkAppN (mkConst helper levels) params
    let loopType ← Meta.inferType recursion
    Meta.withLocalDeclD `loop loopType fun loop => do
      let symbolic := fun (e : Expr) => e.replace fun sub => if sub == recursion then some loop else none
      let nativeEntry := symbolic (native.value.beta args)
      let conditions ← apply ``Equations (fields.push loop)
      let result ← Meta.mkEq (mkAppN candidate args) nativeEntry
      let statement ← mkArrow conditions result
      let proof ← apply ``allInputs (fields ++ #[b, start, stop, loop])
      let theoremType ← Meta.inferType proof
      witness (args.push loop) theoremType statement
      let closed ← Meta.mkLambdaFVars (args.push loop) proof
      let .ok _ := Kernel.check env {} closed | throwError "invalid bounded fold simulation"
      Meta.forallTelescope loopType fun indices _ => do
        let #[i, last, initial] := indices | throwError "unexpected fold loop inputs"
        let getI := mkApp get i
        let .forallE _ bound _ _ ← Meta.whnf (← Meta.inferType getI) | throwError "missing word read bound"
        let read := mkApp getI (mkApp (mkConst `lcProof) bound)
        let next := mkApp2 loop (mkApp2 (mkConst `USize.add) i (mkApp (mkConst `USize.ofNat) (mkNatLit 1))) last
        let update ← Meta.withLocalDeclD `unit (mkConst `Unit) fun unit =>
          Meta.mkLambdaFVars #[unit] (mkApp2 f initial read)
        let step ← apply ``foldStep #[β, m, inst, i, last, initial, update, next]
        let nativeStep := symbolic (raw.value.beta (params ++ indices))
        witness ((args.push loop) ++ indices) nativeStep step
  verify.run' |>.toIO' {fileName := "<bounded machine-word fold>", fileMap := default} {env}

end OmegaChecks.InitPort.WordFold

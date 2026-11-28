module
public import Lean
public import OmegaChecks.InitPort.Alternatives.ArrayWord
import all OmegaChecks.InitPort.Alternatives.ArrayWord
import all Init.Data.Array.Basic

namespace OmegaChecks.InitPort.ArrayWord

open OmegaChecks.InitPort.Alternatives (anyEntry anyStep anyLoop)

/-- The callable equations of a native loop. Every continuing call has a valid read,
including when successive machine addresses cross zero. -/
private structure Equations {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool)
    (xs : Array α) (loop : USize → USize → m Bool) : Prop where
  stop (i : USize) : loop i i = pure false
  step (i last : USize) (h : i.toNat < xs.size) :
    loop i last = anyStep i last (fun _ => p (xs.uget i h)) (fun _ => loop (i+1) last)

private theorem simulate {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool)
    (xs : Array α) (loop : USize → USize → m Bool) (eqs : Equations p xs loop)
    (fuel j last : Nat) (distance : j + fuel = last) (bound : last ≤ xs.size) :
    anyLoop p xs (.ofNat last) fuel (.ofNat j) = loop (.ofNat j) (.ofNat last) := by
  induction fuel generalizing j with
  | zero =>
    have e : j = last := distance
    subst last
    exact (eqs.stop _).symm
  | succ n ih =>
    have valid : (USize.ofNat j).toNat < xs.size := by
      exact Nat.lt_of_le_of_lt (Nat.mod_le j USize.size) (by omega)
    have next := ih (j + 1) (by omega)
    rw [USize.ofNat_add] at next
    rw [eqs.step _ _ valid]
    simp only [anyLoop, valid, ↓reduceDIte]
    exact congrArg (fun result => anyStep (USize.ofNat j) (USize.ofNat last)
      (fun _ => p (xs.uget _ valid)) (fun _ => result)) next

/-- A finite realization of both unfolded native clauses fixes the result on every input. -/
private theorem allInputs {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool)
    (xs : Array α) (start stop : Nat) (loop : USize → USize → m Bool)
    (eqs : Equations p xs loop) :
    Alternatives.Array.anyMUnsafe p xs start stop =
      anyEntry xs.size start stop (fun a b => loop (.ofNat a) (.ofNat b)) := by
  unfold Alternatives.Array.anyMUnsafe anyEntry
  split
  · dsimp only
    split
    · next h => exact simulate p xs loop eqs _ _ _ (Nat.add_sub_of_le (Nat.le_of_lt h)) (Nat.min_le_right ..)
    · rfl
  · rfl

private unsafe def nativeEntry {α : Type u} {m : Type → Type w} [Monad m]
    (p : α → m Bool) (xs : Array α) (start stop : Nat) : m Bool :=
  anyEntry xs.size start stop fun j last =>
    Array.anyMUnsafe.any p xs (.ofNat j) (.ofNat last)

private unsafe def nativeStep {α : Type u} {m : Type → Type w} [Monad m]
    (p : α → m Bool) (xs : Array α) (i last : USize) : m Bool :=
  anyStep i last (fun _ => p (xs.uget i lcProof)) (fun _ => Array.anyMUnsafe.any p xs (i+1) last)

open Lean

/-- Check the two pinned unfoldings and the simulation theorem against the complete
candidate. Only the unchecked proof argument in the upstream read is erased. -/
public def check (env : Environment) (native : DefinitionVal) (candidate : Expr) : IO Unit := do
  let levels := native.levelParams.map Level.param
  let owner := env.getModuleIdx? `Init.Data.Array.Basic
  let helper := ``Array.anyMUnsafe.any
  let some (.defnInfo recursion) := env.find? helper | throw <| IO.userError "missing native array search loop"
  unless owner.isSome && [native.name, helper, `Array.anyM].all (fun n => env.getModuleIdxFor? n == owner) &&
      native.name == `Array.anyMUnsafe && native.safety == .unsafe && recursion.safety == .unsafe &&
      Compiler.getImplementedBy? env `Array.anyM == some native.name do
    throw <| IO.userError "invalid native array search owner or implementation"
  for (declaration, expected) in [(native, ``nativeEntry), (recursion, ``nativeStep)] do
    let some (.defnInfo model) := env.find? expected | throw <| IO.userError s!"missing native model {expected}"
    let body := model.value.instantiateLevelParams model.levelParams (declaration.levelParams.map Level.param)
    unless Kernel.isDefEqGuarded env {} declaration.value body do
      throw <| IO.userError s!"native array search differs from the certified unfolding at {declaration.name}"
  unless Kernel.isDefEqGuarded env {} candidate (mkConst ``Alternatives.Array.anyMUnsafe levels) do
    throw <| IO.userError "array search candidate differs from the bounded word loop"
  let certify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let #[α, m, inst, p, xs, start, stop] := args | throwError "unexpected array search inputs"
    let u := mkConst `USize
    let out ← Meta.inferType (mkAppN candidate args)
    let loopType ← mkArrow u (← mkArrow u out)
    Meta.withLocalDeclD `loop loopType fun loop => do
      let eqs ← Meta.mkAppOptM ``Equations (#[α, m, inst, p, xs, loop].map some)
      let entry ← Meta.withLocalDeclD `i (mkConst `Nat) fun i =>
        Meta.withLocalDeclD `end (mkConst `Nat) fun last => do
          Meta.mkLambdaFVars #[i, last] (mkApp2 loop (mkApp (mkConst `USize.ofNat) i) (mkApp (mkConst `USize.ofNat) last))
      let size ← Meta.mkAppM `Array.size #[xs]
      let result ← Meta.mkAppOptM ``anyEntry (#[m, inst, size, start, stop, entry].map some)
      let claim ← Meta.mkEq (mkAppN candidate args) result
      let statement ← Meta.mkForallFVars (args.push loop) (← mkArrow eqs claim)
      let proof := mkConst ``allInputs levels
      let .ok inferred := Kernel.check env {} proof | throwError "invalid array word loop simulation"
      unless Kernel.isDefEqGuarded env {} statement inferred do throwError "incomplete array word loop simulation"
  certify.run' |>.toIO' {fileName := "<bounded array word loop>", fileMap := default} {env}

end OmegaChecks.InitPort.ArrayWord

module

public import Lean

/-! Translate proof terms from the pinned Init environment into the strict namespace. -/

open Lean
namespace OmegaInitCompiler

private initialize cachedOwner : IO.Ref (Option (Name × Environment)) ← IO.mkRef none

/-- The Lean frontend repeatedly elaborates declarations in the same source module. -/
public def officialEnvironment (owner : Name) : IO Environment := do
  if let some (cached, env) ← cachedOwner.get then
    if cached == owner then return env
  let env ← importModules #[{module := owner}] {}
  cachedOwner.set (some (owner, env))
  return env

/-- Kernel numeral literals denote the official Nat; strict numerals use the Omega constructors. -/
private partial def natTerm (n : Nat) : Expr :=
  if n < 32 then
    n.fold (init := mkConst `Omega.Nat.zero) (fun _ _ x => mkApp (mkConst `Omega.Nat.succ) x)
  else
    let x := mkBVar 0
    let twice := mkApp2 (mkConst `Omega.Nat.add) x x
    .letE `half (mkConst `Omega.Nat) (natTerm (n / 2))
      (if n % 2 == 0 then twice else mkApp (mkConst `Omega.Nat.succ) twice) false

private abbrev Helpers := Std.HashMap Name (List Name × Expr)

/-- Preserve sharing while expanding the private implementation of an official proof. -/
private partial def translateTerm (env : Environment) (visiting : NameSet) (term : Expr) :
    StateT Helpers (Except String) Expr := do
  for n in term.getUsedConstants do
    unless isPrivateName n do continue
    if (← get).contains n then continue
    if visiting.contains n then throw s!"recursive private proof dependency {n}"
    let some info := env.find? n | throw s!"unknown private proof dependency {n}"
    let some idx := env.getModuleIdxFor? n | throw s!"private helper {n} has no official owner"
    unless env.header.moduleNames[idx]!.getRoot == `Init do throw s!"private helper outside Init: {n}"
    if info.isUnsafe || info.isPartial then throw s!"inadmissible private helper {n}"
    let some value := info.value? (allowOpaque := true) | throw s!"no kernel term for private helper {n}"
    let value ← translateTerm env (visiting.insert n) value
    modify (·.insert n (info.levelParams, value))
  if (term.find? (fun e => e matches .lit (.strVal _))).isSome then
    throw "strict string literal encoding is unavailable"
  let helpers ← get
  let rec go (e : Expr) : Expr :=
    e.replace fun
      | .const n us =>
        if let some (params, body) := helpers[n]? then some (body.instantiateLevelParams params us)
        else some (.const (`Omega ++ n) us)
      | .proj n i x => some (.proj (`Omega ++ n) i (go x))
      | .lit (.natVal n) => some (natTerm n)
      | _ => none
  return go term

public def translateProofTerm (env : Environment) (term : Expr) : Except String Expr :=
  (translateTerm env {} term).run' {}

/-- Search the given telescope for an assumption, reflexivity, or the constructor of True.
Every returned term has been independently type-checked against the full interface. -/
public partial def elementaryProof? (env : Environment) (type : Expr) : Option Expr :=
  let rec terms (goal : Expr) (depth : Nat) : List Expr := Id.run do
    let mut candidates := (List.range depth).map mkBVar
    if let .const n us := goal.getAppFn then
      let xs := goal.getAppArgs
      if (n == `Omega.Eq && xs.size == 3) || (n == `Omega.HEq && xs.size == 4) then
        candidates := mkApp2 (mkConst (n ++ `refl) us) xs[0]! xs[1]! :: candidates
      if n == `Omega.Iff && xs.size == 2 then
        candidates := mkApp (mkConst `Omega.Iff.rfl) xs[0]! :: candidates
      if n == `Omega.True then candidates := mkConst `Omega.True.intro :: candidates
    if let .forallE n dom body bi := goal then
      candidates := (terms body (depth + 1)).map (fun b => Expr.lam n dom b bi) ++ candidates
    return candidates
  (terms type 0).find? (fun e =>
    (Kernel.check env {} e).toOption.any (Kernel.isDefEqGuarded env {} type))

end OmegaInitCompiler

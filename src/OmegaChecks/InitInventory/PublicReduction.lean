module
public import Lean

open Lean
namespace OmegaChecks.InitInventory

/-- The pinned Lean evaluator can calculate these on closed natural numbers
even when the public constant has no definition body (notably Nat.gcd). -/
private def officialReduction (env : Environment) (n : Name) : Option String := do
  let info ← env.find? n
  if #[`Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod, `Nat.pow, `Nat.gcd,
       `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight].contains n then
    return "builtin natural-number reduction"
  match info with
  | .defnInfo _ => return "public definition body"
  | .recInfo _ => return "recursor computation rule"
  | .ctorInfo _ => return "constructor computation rule"
  | .inductInfo _ => return "primitive inductive type"
  | _ => none

/-- One shortest implementation-body path to a sealed strict implementation
whose official counterpart has a public computation rule or inductive interface. -/
public def reductionPaths (official strict full : Environment) : NameMap (List Name × String) := Id.run do
  let mut users : NameMap (Array Name) := {}
  let mut paths : NameMap (List Name × String) := {}
  let mut todo := #[]
  for (n, info) in full.constants.toList do
    let some value := info.value? (allowOpaque := true) | continue
    if !(strict.find? n).any (· matches .defnInfo _) then
      if let some rule := officialReduction official (n.replacePrefix `Omega .anonymous) then
        -- Builtin arithmetic still reduces in an ordinary import when its pinned root name is present.
        unless officialReduction strict n == some rule do
          paths := paths.insert n ([n], rule)
          todo := todo.push n
    if info matches .defnInfo _ | .opaqueInfo _ then
      for dep in value.getUsedConstantsAsSet do
        users := users.insert dep ((users.getD dep #[]).push n)
  todo := todo.qsort Name.lt
  let mut i := 0
  while h : i < todo.size do
    let dependency := todo[i]
    i := i + 1
    let some (path, rule) := paths.get? dependency | continue
    for n in (users.getD dependency #[]).qsort Name.lt do
      unless paths.contains n do
        paths := paths.insert n (n :: path, rule)
        todo := todo.push n
  return paths

end OmegaChecks.InitInventory

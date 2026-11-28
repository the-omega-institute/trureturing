module
public import Lean

namespace OmegaChecks.InitCompiler

open Lean

private def sum? (e : Expr) : Option (Expr × Expr) := do
  match e.getAppFn.constName?, e.getAppArgs with
  | some `HAdd.hAdd, #[.const `Nat _, _, _, _, a, b]
  | some `Nat.add, #[a, b] => return (a, b)
  | _, _ => none

private def numeral? (e : Expr) : Option Nat := do
  if e.isAppOfArity `OfNat.ofNat 3 then return ← e.getAppArgs[1]!.rawNatLit?
  e.rawNatLit?

/-- Prove a bound by following a summand through nested natural-number additions. -/
private def bound? (strict : Bool) (a b : Expr) (fuel : Nat) : Option Expr := do
  let fuel + 1 := fuel | none
  if strict && numeral? a == some 0 then
    if let some (n + 1) := numeral? b then return mkApp (mkConst `Nat.succ_pos) (mkRawNatLit n)
  if !strict && a == b then return mkApp (mkConst `Nat.le_refl) a
  if !strict && numeral? a == some 0 then return mkApp (mkConst `Nat.zero_le) b
  let (l, r) ← sum? b
  if strict && a == l then
    if let some h := bound? true (mkRawNatLit 0) r fuel then
      return mkApp3 (mkConst `Nat.lt_add_of_pos_right) r l h
  if strict && a == r then
    if let some h := bound? true (mkRawNatLit 0) l fuel then
      return mkApp3 (mkConst `Nat.lt_add_of_pos_left) l r h
  for (term, other, left) in [(l, r, true), (r, l, false)] do
    if let some h := bound? strict a term fuel then
      let le := mkApp2 (mkConst (if left then `Nat.le_add_right else `Nat.le_add_left)) term other
      return mkApp5 (mkConst (if strict then `Nat.lt_of_lt_of_le else `Nat.le_trans)) a term b h le
  none

/-- Replace uses of a simplifier's propositional equality by a proof of its arithmetic goal.
The caller checks the resulting proof at the unchanged type in the destination kernel. -/
public def natComparison? (goal : Expr) : Option Expr := do
  let name ← goal.getAppFn.constName?
  if name == `Eq then
    let #[.const `Nat _, a, b] := goal.getAppArgs | none
    if a == b then return mkApp2 (mkConst `Eq.refl [.succ .zero]) (mkConst `Nat) a
    let (x, y) ← sum? a
    let (y', x') ← sum? b
    guard (x == x' && y == y')
    return mkApp2 (mkConst `Nat.add_comm) x y
  guard (name == `LT.lt || name == `LE.le)
  let #[.const `Nat _, _, a, b] := goal.getAppArgs | none
  bound? (name == `LT.lt) a b 24

end OmegaChecks.InitCompiler

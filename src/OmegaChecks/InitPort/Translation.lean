module
public import Lean
public import OmegaChecks.InitCompiler.RootNames

open Lean

namespace InitKernelPort

/-- Preserve the private name's lexical prefix even when a later module emits
an equation for a declaration originally defined in a different module. -/
public def portName (n : Name) : Name :=
  if OmegaChecks.InitCompiler.RootNames.usesRoot n then n
  else if let some user := privateToUserName? n then
    if let some lexical := privatePrefix? n then
      if (`_private.Init).isPrefixOf lexical && isPrivatePrefix lexical then
        lexical.replacePrefix `_private.Init `_private.OmegaInit ++ (`Omega ++ user)
      else `Omega ++ n
    else `Omega ++ n
  else `Omega ++ n

/-- Binary expansion avoids allocating a unary term for a huge numeral. -/
public partial def natTerm (n : Nat) : Expr :=
  if n < 32 then
    n.fold (init := mkConst `Omega.Nat.zero) (fun _ _ x => mkApp (mkConst `Omega.Nat.succ) x)
  else
    let x := mkBVar 0
    let two := mkApp (mkConst `Omega.Nat.succ) (mkApp (mkConst `Omega.Nat.succ) (mkConst `Omega.Nat.zero))
    let twice := mkApp2 (mkConst `Omega.Nat.mul) x two
    .letE `half (mkConst `Omega.Nat) (natTerm (n / 2))
      (if n % 2 == 0 then twice else mkApp (mkConst `Omega.Nat.succ) twice) false

private def stringTerm (s : String) : Expr :=
  let char := mkConst `Omega.Char
  let chars := s.toList.foldr (init := mkApp (mkConst `Omega.List.nil [.zero]) char) fun ch tail =>
    mkApp3 (mkConst `Omega.List.cons [.zero]) char (mkApp (mkConst `Omega.Char.ofNat) (natTerm ch.toNat)) tail
  mkApp (mkConst `Omega.String.ofList) chars

/-- Replace recursively inside projection subjects, preserving binder syntax and universe levels. -/
public partial def translate (rename : Name → Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (rename n) ls)
    | .proj owner field target => some (.proj (rename owner) field (translate rename target))
    | .lit (.natVal n) => some (natTerm n)
    | .lit (.strVal s) => some (stringTerm s)
    | _ => none

end InitKernelPort

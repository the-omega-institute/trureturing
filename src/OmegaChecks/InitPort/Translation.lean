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

private def stringTerm (s : String) : Expr :=
  let char := mkConst `Omega.Char
  let chars := s.toList.foldr (init := mkApp (mkConst `Omega.List.nil [.zero]) char) fun ch tail =>
    mkApp3 (mkConst `Omega.List.cons [.zero]) char (mkApp (mkConst `Omega.Char.ofNat) (mkRawNatLit ch.toNat)) tail
  mkApp (mkConst `Omega.String.ofList) chars

/-- Replace recursively inside projection subjects, preserving binder syntax and universe levels. -/
public partial def translate (rename : Name → Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (rename n) ls)
    | .proj owner field target => some (.proj (rename owner) field (translate rename target))
    | .lit (.strVal s) => some (stringTerm s)
    | _ => none

end InitKernelPort

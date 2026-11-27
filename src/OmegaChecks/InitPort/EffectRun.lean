module
public import OmegaChecks.InitPort.Translation
import all OmegaChecks.InitPort.ReferencePut

open Lean
namespace OmegaChecks.InitPort.EffectRun

public def names := [`unsafeBaseIO, `unsafeEIO, `unsafeIO]

private def arg (bi : BinderInfo) (type body : Expr) := Expr.forallE .anonymous type body bi
private def lam (type body : Expr) := Expr.lam .anonymous type body .default
private def type0 := Expr.sort 1
private def except (ε α : Expr) := mkApp2 (mkConst `Except [0, 0]) ε α
private def region := mkConst `IO.RealWorld
private def world := mkApp (mkConst `Void) region
private def nativeWorld := mkApp3 (mkConst `unsafeCast [1, 1]) (mkConst `Unit) world (mkConst `Unit.unit)

/-- The private region package supplies the same value as the indexed allocator of Void. -/
private def initialWorld : Expr :=
  let carrier := lam type0 (.bvar 0)
  let package := mkApp2 (mkConst `Sigma [1, 0]) type0 carrier
  let unit := mkApp4 (mkConst `Sigma.mk [1, 0]) type0 carrier (mkConst `PUnit [1]) (mkConst `PUnit.unit [1])
  let indexed := mkApp2 (mkConst `Lean.opaqueId [2]) (arg .default type0 package) (lam type0 unit)
  mkApp3 (mkConst `Sigma.snd [1, 0]) type0 carrier (mkApp indexed region)

private def abstractArgs (type : Expr) (term : Expr) : Expr :=
  match type with
  | .forallE n domain body bi => .lam n domain (abstractArgs body term) bi
  | _ => term

private def specification (name : Name) (token : Expr) : Option (Expr × Expr) := do
  let α := Expr.bvar 1
  let action := Expr.bvar 0
  let (type, term) ← match name with
    | `unsafeBaseIO =>
      let type := arg .implicit type0 <| arg .default (mkApp (mkConst `BaseIO) (.bvar 0)) α
      let out := mkApp2 (mkConst `ST.Out) region α
      let matcher := mkPrivateNameCore `Init.System.IO `BaseIO.toEIO.match_1
      pure (type, mkApp4 (mkConst matcher [1]) α (lam out (.bvar 2)) (mkApp action token)
        (lam α (lam world (.bvar 1))))
    | `unsafeEIO =>
      let ε := Expr.bvar 2
      let result := except ε α
      let type := arg .implicit type0 <| arg .implicit type0 <|
        arg .default (mkApp2 (mkConst `EIO) (.bvar 1) (.bvar 0)) result
      pure (type, mkApp2 (mkConst `unsafeBaseIO) result (mkApp3 (mkConst `EIO.toBaseIO) ε α action))
    | `unsafeIO =>
      let ε := mkConst `IO.Error
      let type := arg .implicit type0 <| arg .default (mkApp (mkConst `IO) (.bvar 0)) (except ε α)
      pure (type, mkApp3 (mkConst `unsafeEIO) ε α action)
    | _ => none
  return (type, abstractArgs type term)

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let .defnInfo d := ci | return false
  unless d.safety == .unsafe && d.levelParams.isEmpty && d.all == [d.name] do return false
  let rename := if strict then InitKernelPort.portName else id
  let name := if strict then InitKernelPort.originalName d.name else d.name
  let some (type, value) := specification name (if strict then initialWorld else nativeWorld) | return false
  return d.name == rename name && ReferencePut.sameTerm d.type (InitKernelPort.translate rename type) &&
    ReferencePut.sameTerm d.value (InitKernelPort.translate rename value)

/-- Substitute only the world argument of the pinned action. Wrapper bodies stay verbatim. -/
public def withInitialWorld (body : Expr) : Expr :=
  body.replace fun e => if e.eqv nativeWorld then some initialWorld else none

public def checkWorld (env : Kernel.Environment) : IO Unit := do
  let some (.opaqueInfo allocator) := env.find? (InitKernelPort.portName `Void.mk)
    | throw <| IO.userError "missing region-indexed token allocator"
  let .lam _ _ (.lam _ _ body _) _ := allocator.value
    | throw <| IO.userError "unexpected region-indexed token allocator"
  if body.hasLooseBVar 0 then throw <| IO.userError "token depends on an unavailable region witness"
  let token := (body.lowerLooseBVars 1 1).instantiate1 (mkConst (InitKernelPort.portName `IO.RealWorld))
  unless token.eqv (InitKernelPort.translate InitKernelPort.portName initialWorld) do
    throw <| IO.userError "effect runner and region allocator have different initial tokens"

/-- Recheck the complete chain with safe copies before replaying the original unsafe declarations. -/
public def replay (base : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut safe := base
  let mut installed := base
  let add (env : Kernel.Environment) (d : DefinitionVal) := do
    match env.addDeclCore 0 1000 (.defnDecl d) none with
    | .ok next => pure next
    | .error e => throw <| IO.userError s!"kernel rejected {d.name}: {← e.toMessageData {} |>.toString}"
  for name in names do
    let some ci := constants[InitKernelPort.portName name]? | continue
    unless isOriginal ci true do throw <| IO.userError s!"unexpected effect runner {name}"
    if name == `unsafeBaseIO then checkWorld base
    let .defnInfo d := ci | throw <| IO.userError s!"expected effect runner definition {name}"
    safe ← add safe {d with safety := .safe}
    installed ← add installed d
  return installed

end OmegaChecks.InitPort.EffectRun

module
public import OmegaChecks.InitPort.Translation
import Lean.Compiler.BorrowedAnnotation

open Lean
namespace OmegaChecks.InitPort.ReferencePut

private def type0 := Expr.sort 1
private def forallArg (bi : BinderInfo) (domain body : Expr) := Expr.forallE .anonymous domain body bi
private def ref (s a : Nat) := mkApp2 (mkConst `ST.Ref) (.bvar s) (.bvar a)
private def st (s : Nat) := mkApp (mkConst `ST) (.bvar s)
private def unit := mkConst `Unit

private def primitiveType :=
  forallArg .implicit type0 <| forallArg .implicit type0 <|
    forallArg .default (markBorrowed (ref 1 0)) <| forallArg .default (.bvar 1) (mkApp (st 3) unit)

private def primitiveValue :=
  let instanceTerm := mkApp3 (mkConst `instInhabitedST) (.bvar 3) unit (mkConst `instInhabitedPUnit [1])
  mkApp2 (mkConst `Inhabited.default [1]) (mkApp (st 3) unit) instanceTerm

private def liftedType :=
  forallArg .implicit type0 <| forallArg .implicit (forallArg .default type0 type0) <|
    forallArg .instImplicit (mkApp2 (mkConst `MonadLiftT [0, 0, 0]) (st 1) (.bvar 0)) <|
    forallArg .implicit type0 <| forallArg .default (ref 3 0) <|
    forallArg .default (.bvar 1) (mkApp (.bvar 4) unit)

private def liftedValue :=
  let action := mkApp4 (mkConst `ST.Prim.Ref.put) (.bvar 5) (.bvar 2) (.bvar 1) (.bvar 0)
  mkApp5 (mkConst `liftM [0, 0, 0]) (st 5) (.bvar 4) (.bvar 3) unit action

private def lambdaBody (value : Expr) : Expr → Expr
  | .forallE n dom rest bi => .lam n dom.consumeMData (lambdaBody value rest) bi
  | _ => value

/-- Alpha-equivalence retaining binder visibility and all metadata in these signatures. -/
private partial def sameTerm (a b : Expr) : Bool :=
  match a, b with
  | .forallE _ d r bi, .forallE _ d' r' bi' | .lam _ d r bi, .lam _ d' r' bi' =>
    bi == bi' && sameTerm d d' && sameTerm r r'
  | .app f x, .app g y => sameTerm f g && sameTerm x y
  | .mdata md e, .mdata md' e' => md == md' && sameTerm e e'
  | _, _ => a.equal b

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let rename := if strict then InitKernelPort.portName else id
  let tr := InitKernelPort.translate rename
  let check (name : Name) (all : List Name) (value type final : Expr) :=
    ci.name == rename name && all == [ci.name] && ci.levelParams.isEmpty &&
    sameTerm ci.type (tr type) && sameTerm value (tr (lambdaBody final type))
  match ci with
  | .opaqueInfo d =>
    return d.isUnsafe && check `ST.Prim.Ref.put d.all d.value primitiveType primitiveValue
  | .defnInfo d =>
    return d.safety == .unsafe && check `ST.Ref.put d.all d.value liftedType liftedValue
  | _ => return false

/-- Check the lifted term against a separately checked safe copy of the primitive.
The public environment receives the original unsafe dependency chain. -/
public def replay (base : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let prim := constants[InitKernelPort.portName `ST.Prim.Ref.put]?
  let lifted := constants[InitKernelPort.portName `ST.Ref.put]?
  if prim.isNone && lifted.isNone then return base
  let some (.opaqueInfo d) := prim | throw <| IO.userError "missing primitive ref put"
  unless isOriginal (.opaqueInfo d) true do throw <| IO.userError "unexpected primitive ref put"
  let add (env : Kernel.Environment) (decl : Declaration) := do
    match env.addDeclCore 0 1000 decl none with
    | .ok checked => pure checked
    | .error _ => throw <| IO.userError "kernel rejected reference put"
  let checked ← add base (.opaqueDecl {d with isUnsafe := false})
  let installed ← add base (.opaqueDecl d)
  let some info := lifted | return installed
  let .defnInfo wrapper := info | throw <| IO.userError "expected lifted ref put definition"
  unless isOriginal info true do throw <| IO.userError "unexpected lifted ref put"
  discard <| add checked (.defnDecl {wrapper with safety := .safe})
  add installed (.defnDecl wrapper)

end OmegaChecks.InitPort.ReferencePut

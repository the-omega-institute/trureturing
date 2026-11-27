module
public import Lean
import all Init.System.Promise
import Lean.Compiler.IR.CompilerM

open Lean

namespace OmegaChecks.InitPort.LogicalHandle

private noncomputable opaque token : (T : Type) ×' T := ⟨PUnit, PUnit.unit⟩
private def standardCarrier : NonemptyType.{0} := ⟨PUnit, ⟨PUnit.unit⟩⟩
private def carrier : NonemptyType := ⟨token.1, ⟨token.2⟩⟩
private structure Model (α : Type) where
  handle : carrier.type
  support : Nonempty α

private noncomputable def allocate {α : Type} [s : Nonempty α] : BaseIO (Model α) :=
  pure ⟨token.2, s⟩

private structure Reference (σ α : Type) where
  ref : carrier.type
  h : Nonempty α

private noncomputable def allocateRef {σ α : Type} (a : α) : ST σ (Reference σ α) :=
  pure ⟨token.2, ⟨a⟩⟩

public structure API where
  owner : Name
  pointed : Name
  allocator : Name
  logicalToken : Name
  nativeAllocator : String

public def promise : API := ⟨`Init.System.Promise, mkPrivateNameCore `Init.System.Promise `IO.PromisePointed,
  `IO.Promise.new, `IO.Promise.logicalToken, "lean_io_promise_new"⟩
public def referenceCell : API := ⟨`Init.System.ST, `ST.RefPointed, `ST.Prim.mkRef, `ST.Ref.logicalToken,
  "lean_st_mk_ref"⟩

public def API.privateOwner (api : API) := api.owner.replacePrefix `Init `OmegaInit
public def API.tokenName (api : API) := mkPrivateNameCore api.owner api.logicalToken
public def API.strictToken (api : API) := mkPrivateNameCore api.privateOwner (`Omega ++ api.logicalToken)

public def forDecl? (n : Name) := [promise, referenceCell].find? (fun api => n == api.pointed || n == api.allocator)
public def forToken? (n : Name) := [promise, referenceCell].find? (fun api => n == api.strictToken)

private def renameTemplate (api : API) (body : Expr) : Expr :=
  body.replace fun
    | .const n us =>
      let name := if n == ``token then api.tokenName
        else if n == ``carrier then api.pointed
        else if n == ``Model then `IO.Promise
        else if n == ``Model.mk then mkPrivateNameCore api.owner `IO.Promise.mk
        else if n == ``Reference then `ST.Ref
        else if n == ``Reference.mk then `ST.Ref.mk
        else n
      some (.const name us)
    | _ => none

public structure Templates where
  package : OpaqueVal
  family : Expr
  allocation : Expr

public def templates (api : API) (env : Environment) : IO Templates := do
  let some (.opaqueInfo pkg) := env.find? ``token | throw <| IO.userError "missing logical handle token"
  let some (.defnInfo family) := env.find? ``carrier | throw <| IO.userError "missing handle carrier"
  let some (.defnInfo alloc) := env.find? (if api.owner == promise.owner then ``allocate else ``allocateRef) | throw <| IO.userError "missing handle allocation"
  let inlineProof (e : Expr) := e.replace fun sub => do
    let n ← sub.constName?
    let .thmInfo proof ← env.find? n | none
    guard ((privateToUserName n).getRoot == `OmegaChecks)
    return proof.value
  return ⟨{pkg with name := api.tokenName, all := [api.tokenName]}, renameTemplate api (inlineProof family.value),
    renameTemplate api (inlineProof alloc.value)⟩

/-- The private logical witness is a closed term with no executable entry point. -/
public def checkToken (api : API) (strict publicStrict reference : Environment) (renameTerm : Expr → Expr) : IO Unit := do
  let pkg := (← templates api reference).package
  let some (.opaqueInfo actual) := strict.find? api.strictToken | throw <| IO.userError "missing opaque handle token"
  unless !actual.isUnsafe && actual.levelParams == [] && actual.all == [api.strictToken] &&
      (renameTerm actual.type).equal pkg.type && (renameTerm actual.value).equal pkg.value &&
      strict.getModuleIdxFor? api.strictToken == strict.getModuleIdx? api.privateOwner &&
      !publicStrict.contains api.strictToken && isNoncomputable strict api.strictToken &&
      (IR.findEnvDecl strict api.strictToken).isNone do
    throw <| IO.userError "incorrect private representation or executable logical handle token"

public def checkBody (api : API) (strict publicStrict reference : Environment) (name : Name)
    (renameTerm : Expr → Expr) (value : Expr) : IO Unit := do
  let pkg ← templates api reference
  let family := name == api.pointed
  let expected := if family then pkg.family else pkg.allocation
  unless (family || name == api.allocator) && (renameTerm value).equal expected do
    throw <| IO.userError "handle implementation differs from the checked logical model"
  checkToken api strict publicStrict reference renameTerm
  let some (.opaqueInfo original) := reference.find? api.pointed | throw <| IO.userError "missing official handle carrier"
  unless !original.isUnsafe && Kernel.isDefEqGuarded reference {} original.value (mkConst ``standardCarrier) &&
      reference.getModuleIdxFor? name == reference.getModuleIdx? api.owner &&
      reference.getModuleIdxFor? api.pointed == reference.getModuleIdx? api.owner &&
      getExternNameFor reference `c api.allocator == some api.nativeAllocator do
    throw <| IO.userError "unexpected pinned handle representation"

end OmegaChecks.InitPort.LogicalHandle

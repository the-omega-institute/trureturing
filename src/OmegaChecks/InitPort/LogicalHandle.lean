module
public import Lean
import all Init.System.Promise
import all Init.ShareCommon
import Lean.Compiler.IR.CompilerM

open Lean

namespace OmegaChecks.InitPort.LogicalHandle

private noncomputable opaque token : (T : Type) ×' T := ⟨PUnit, PUnit.unit⟩
private def standardCarrier : NonemptyType.{0} := ⟨PUnit, ⟨PUnit.unit⟩⟩
private def carrier : NonemptyType := ⟨token.1, ⟨token.2⟩⟩
private noncomputable opaque shareToken.{u} (_ : ShareCommon.StateFactory) : (T : Type u) ×' T :=
  ⟨PUnit, PUnit.unit⟩
private def shareRepresentative.{u} (_ : ShareCommon.StateFactory) : NonemptyType.{u} :=
  ⟨PUnit, ⟨PUnit.unit⟩⟩
private def shareCarrier.{u} (s : ShareCommon.StateFactory) : NonemptyType.{u} :=
  ⟨(shareToken s).1, ⟨(shareToken s).2⟩⟩
private noncomputable def shareAllocate.{u} (s : ShareCommon.StateFactory) : (shareCarrier.{u} s).type :=
  (shareToken s).2

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

public def shareState : API := ⟨`Init.ShareCommon, `ShareCommon.StatePointed, `ShareCommon.State.mk,
  `ShareCommon.State.logicalToken, "l_ShareCommon_mkStateImpl"⟩
public def apis := [promise, referenceCell, shareState]

public def API.privateOwner (api : API) := api.owner.replacePrefix `Init `OmegaInit
public def API.tokenName (api : API) := mkPrivateNameCore api.owner api.logicalToken
public def API.strictToken (api : API) := mkPrivateNameCore api.privateOwner (`Omega ++ api.logicalToken)

public def forDecl? (n : Name) := apis.find? (fun api => n == api.pointed || n == api.allocator)
public def forToken? (n : Name) := apis.find? (fun api => n == api.strictToken)

private def renameTemplate (api : API) (body : Expr) : Expr :=
  body.replace fun
    | .const n us =>
      let name := if n == ``token || n == ``shareToken then api.tokenName
        else if n == ``carrier || n == ``shareCarrier then api.pointed
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
  let (pkgName, familyName, allocName) :=
    if api.owner == shareState.owner then (``shareToken, ``shareCarrier, ``shareAllocate)
    else (``token, ``carrier, if api.owner == promise.owner then ``allocate else ``allocateRef)
  let some (.opaqueInfo pkg) := env.find? pkgName | throw <| IO.userError "missing logical handle token"
  let some (.defnInfo family) := env.find? familyName | throw <| IO.userError "missing handle carrier"
  let some (.defnInfo alloc) := env.find? allocName | throw <| IO.userError "missing handle allocation"
  let forOfficial (info : DefinitionVal) (name : Name) (e : Expr) := Id.run do
    let some original := env.find? name | return e
    return e.instantiateLevelParams info.levelParams (original.levelParams.map Level.param)
  let inlineProof (e : Expr) := e.replace fun sub => do
    let n ← sub.constName?
    let .thmInfo proof ← env.find? n | none
    guard ((privateToUserName n).getRoot == `OmegaChecks)
    return proof.value
  return ⟨{pkg with name := api.tokenName, all := [api.tokenName]}, renameTemplate api (forOfficial family api.pointed (inlineProof family.value)),
    renameTemplate api (forOfficial alloc api.allocator (inlineProof alloc.value))⟩

/-- The private logical witness is a closed term with no executable entry point. -/
public def checkToken (api : API) (strict publicStrict reference : Environment) (renameTerm : Expr → Expr) : IO Unit := do
  let pkg := (← templates api reference).package
  let some (.opaqueInfo actual) := strict.find? api.strictToken | throw <| IO.userError "missing opaque handle token"
  unless !actual.isUnsafe && actual.levelParams == pkg.levelParams && actual.all == [api.strictToken] &&
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
  let isShare := api.owner == shareState.owner
  let model := if isShare then mkConst ``shareRepresentative (original.levelParams.map Level.param) else mkConst ``standardCarrier
  let nativeMatches := if isShare then Compiler.getImplementedBy? reference api.allocator == some `ShareCommon.mkStateImpl
    else getExternNameFor reference `c api.allocator == some api.nativeAllocator
  unless !original.isUnsafe && Kernel.isDefEqGuarded reference {} original.value model &&
      reference.getModuleIdxFor? name == reference.getModuleIdx? api.owner &&
      reference.getModuleIdxFor? api.pointed == reference.getModuleIdx? api.owner &&
      nativeMatches do
    throw <| IO.userError "unexpected pinned handle representation"

end OmegaChecks.InitPort.LogicalHandle

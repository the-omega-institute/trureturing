module
public import Lean
import all Init.System.Promise
import all Init.ShareCommon
import all Init.Dynamic
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

private noncomputable opaque factoryToken.{u} : (T : Type u) ×' T := ⟨PUnit, PUnit.unit⟩
private def factoryCarrier.{u} : NonemptyType.{u} := ⟨factoryToken.1, ⟨factoryToken.2⟩⟩
private def factoryRepresentative.{u} : NonemptyType.{u} := ⟨PUnit, ⟨PUnit.unit⟩⟩
private noncomputable def makeFactory (_ : ShareCommon.StateFactoryBuilder) : factoryCarrier.{0}.type :=
  factoryToken.2

-- Prelude precedes dependent pairs. A sealed branch selects a pointed carrier using Bool.rec.
private noncomputable opaque methodsTag : Bool := false
private def methodsCarrier : NonemptyType :=
  ⟨Bool.rec PUnit (Nat → Bool) methodsTag,
    ⟨Bool.rec (motive := fun tag => Bool.rec PUnit (Nat → Bool) tag) PUnit.unit (fun _ => false) methodsTag⟩⟩
private noncomputable def makeMethods (_ : Lean.Macro.Methods) : methodsCarrier.type :=
  Bool.rec (motive := fun tag => Bool.rec PUnit (Nat → Bool) tag) PUnit.unit (fun _ => false) methodsTag

private noncomputable opaque dynamicToken : (T : Type) ×' T :=
  ⟨Name × NonScalar, (Name.anonymous, default)⟩
private def dynamicRepresentative : NonemptyType := ⟨Name × NonScalar, inferInstance⟩
private def dynamicCarrier : NonemptyType := ⟨dynamicToken.1, ⟨dynamicToken.2⟩⟩
private noncomputable def makeDynamic {α : Type u} [TypeName α] (_ : α) : dynamicCarrier.type :=
  dynamicToken.2

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
  implementedBy : Option Name := none

public def promise : API := ⟨`Init.System.Promise, mkPrivateNameCore `Init.System.Promise `IO.PromisePointed,
  `IO.Promise.new, `IO.Promise.logicalToken, "lean_io_promise_new", none⟩
public def referenceCell : API := ⟨`Init.System.ST, `ST.RefPointed, `ST.Prim.mkRef, `ST.Ref.logicalToken,
  "lean_st_mk_ref", none⟩

public def shareState : API := ⟨`Init.ShareCommon, `ShareCommon.StatePointed, `ShareCommon.State.mk,
  `ShareCommon.State.logicalToken, "l_ShareCommon_mkStateImpl", some `ShareCommon.mkStateImpl⟩
public def shareFactory : API := ⟨`Init.ShareCommon, `ShareCommon.StateFactoryPointed, `ShareCommon.StateFactory.mk,
  `ShareCommon.StateFactory.logicalToken, "l_ShareCommon_StateFactory_mkImpl", some `ShareCommon.StateFactory.mkImpl⟩
public def macroMethods : API := ⟨`Init.Prelude, `Lean.Macro.MethodsRefPointed, `Lean.Macro.mkMethods,
  `Lean.Macro.MethodsRef.logicalToken, "l_Lean_Macro_mkMethodsImp", some `Lean.Macro.mkMethodsImp⟩
public def dynamicValue : API := ⟨`Init.Dynamic, mkPrivateNameCore `Init.Dynamic `DynamicPointed, `Dynamic.mk,
  `Dynamic.logicalToken, (mkPrivateNameCore `Init.Dynamic `Dynamic.mkImpl).mangle "l_",
  some (mkPrivateNameCore `Init.Dynamic `Dynamic.mkImpl)⟩
public def apis := [promise, referenceCell, shareState, shareFactory, macroMethods, dynamicValue]

public def implementation? (name : Name) := apis.find? (·.implementedBy == some name)

/-- The public allocator runs this very implementation in the pinned runtime. Its checked
strict definition supplies a total term at the implementation's original type. -/
public def checkOpaqueImplementation (owner publicName : Name) (ref : Environment) (impl : DefinitionVal) (body : Expr) : IO Unit := do
  let some (.opaqueInfo entry) := ref.find? publicName | throw <| IO.userError s!"missing pinned operation {publicName}"
  let levels := impl.levelParams.map Level.param
  unless impl.safety == .unsafe && !entry.isUnsafe && Compiler.getImplementedBy? ref publicName == some impl.name &&
      ref.getModuleIdxFor? impl.name == ref.getModuleIdx? owner && ref.getModuleIdxFor? publicName == ref.getModuleIdx? owner &&
      entry.levelParams.length == levels.length && body == mkConst publicName levels &&
      Kernel.isDefEqGuarded ref {} (entry.type.instantiateLevelParams entry.levelParams levels) impl.type do
    throw <| IO.userError s!"incorrect implementation of {publicName} by {impl.name}"

public def checkImplementation (api : API) (ref : Environment) (impl : DefinitionVal) (body : Expr) : IO Unit := do
  unless api.implementedBy == some impl.name && impl.name.mangle (pre := "l_") == api.nativeAllocator do
    throw <| IO.userError s!"incorrect allocator implementation {impl.name}"
  checkOpaqueImplementation api.owner api.allocator ref impl body

public def API.privateOwner (api : API) := api.owner.replacePrefix `Init `OmegaInit
public def API.tokenName (api : API) := mkPrivateNameCore api.owner api.logicalToken
public def API.strictToken (api : API) := mkPrivateNameCore api.privateOwner (`Omega ++ api.logicalToken)

public def forDecl? (n : Name) := apis.find? (fun api => n == api.pointed || n == api.allocator)
public def forToken? (n : Name) := apis.find? (fun api => n == api.strictToken)

private def renameTemplate (api : API) (body : Expr) : Expr :=
  body.replace fun
    | .const n us =>
      let name := if n == ``token || n == ``shareToken || n == ``factoryToken || n == ``methodsTag || n == ``dynamicToken then api.tokenName
        else if n == ``carrier || n == ``shareCarrier || n == ``factoryCarrier || n == ``methodsCarrier || n == ``dynamicCarrier then api.pointed
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
    if api.pointed == dynamicValue.pointed then (``dynamicToken, ``dynamicCarrier, ``makeDynamic)
    else if api.pointed == shareState.pointed then (``shareToken, ``shareCarrier, ``shareAllocate)
    else if api.pointed == shareFactory.pointed then (``factoryToken, ``factoryCarrier, ``makeFactory)
    else if api.pointed == macroMethods.pointed then (``methodsTag, ``methodsCarrier, ``makeMethods)
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
  let indexed := api.pointed == shareState.pointed
  let modelName := if api.pointed == dynamicValue.pointed then ``dynamicRepresentative else if indexed then ``shareRepresentative
    else if api.pointed == shareFactory.pointed then ``factoryRepresentative else ``standardCarrier
  let model := mkConst modelName (original.levelParams.map Level.param)
  let nativeMatches := match api.implementedBy with
    | some impl => Compiler.getImplementedBy? reference api.allocator == some impl && impl.mangle (pre := "l_") == api.nativeAllocator
    | none => getExternNameFor reference `c api.allocator == some api.nativeAllocator
  unless !original.isUnsafe && Kernel.isDefEqGuarded reference {} original.value model &&
      reference.getModuleIdxFor? name == reference.getModuleIdx? api.owner &&
      reference.getModuleIdxFor? api.pointed == reference.getModuleIdx? api.owner &&
      nativeMatches do
    throw <| IO.userError "unexpected pinned handle representation"

end OmegaChecks.InitPort.LogicalHandle

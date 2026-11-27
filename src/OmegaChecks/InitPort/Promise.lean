module
public import Lean
import all Init.System.Promise
import Lean.Compiler.IR.CompilerM

open Lean

namespace OmegaChecks.InitPort.Promise

private noncomputable opaque token : (T : Type) ×' T := ⟨PUnit, PUnit.unit⟩
private def standardCarrier : NonemptyType.{0} := ⟨PUnit, ⟨PUnit.unit⟩⟩
private def carrier : NonemptyType := ⟨token.1, ⟨token.2⟩⟩
private structure Model (α : Type) where
  handle : carrier.type
  support : Nonempty α

private noncomputable def allocate {α : Type} [s : Nonempty α] : BaseIO (Model α) :=
  pure ⟨token.2, s⟩

public def owner := `Init.System.Promise
public def privateOwner := `OmegaInit.System.Promise
public def pointed := mkPrivateNameCore owner `IO.PromisePointed
public def tokenName := mkPrivateNameCore owner `IO.Promise.logicalToken
public def strictToken := mkPrivateNameCore privateOwner `Omega.IO.Promise.logicalToken

private def modelName (n : Name) : Name :=
  if n == ``token then tokenName
  else if n == ``carrier then pointed
  else if n == ``Model then `IO.Promise
  else if n == ``Model.mk then mkPrivateNameCore owner `IO.Promise.mk
  else n

private def renameTemplate (body : Expr) : Expr :=
  body.replace fun
    | .const n us => some (.const (modelName n) us)
    | _ => none

public structure Templates where
  package : OpaqueVal
  family : Expr
  allocation : Expr

public def templates (env : Environment) : IO Templates := do
  let some (.opaqueInfo pkg) := env.find? ``token | throw <| IO.userError "missing logical promise token"
  let some (.defnInfo family) := env.find? ``carrier | throw <| IO.userError "missing promise carrier"
  let some (.defnInfo alloc) := env.find? ``allocate | throw <| IO.userError "missing promise allocation"
  let inlineProof (e : Expr) := e.replace fun sub => do
    let n ← sub.constName?
    let .thmInfo proof ← env.find? n | none
    guard ((privateToUserName n).getRoot == `OmegaChecks)
    return proof.value
  return ⟨{pkg with name := tokenName, all := [tokenName]}, renameTemplate (inlineProof family.value),
    renameTemplate (inlineProof alloc.value)⟩

/-- The private logical witness is a closed term with no executable entry point. -/
public def checkToken (strict publicStrict reference : Environment) (renameTerm : Expr → Expr) : IO Unit := do
  let pkg := (← templates reference).package
  let some (.opaqueInfo actual) := strict.find? strictToken | throw <| IO.userError "missing opaque promise token"
  unless !actual.isUnsafe && actual.levelParams == [] && actual.all == [strictToken] &&
      (renameTerm actual.type).equal pkg.type && (renameTerm actual.value).equal pkg.value &&
      strict.getModuleIdxFor? strictToken == strict.getModuleIdx? privateOwner &&
      !publicStrict.contains strictToken && isNoncomputable strict strictToken &&
      (IR.findEnvDecl strict strictToken).isNone do
    throw <| IO.userError "incorrect private representation or executable logical promise token"

public def checkBody (strict publicStrict reference : Environment) (name : Name)
    (renameTerm : Expr → Expr) (value : Expr) : IO Unit := do
  let pkg ← templates reference
  let family := name == pointed
  let expected := if family then pkg.family else pkg.allocation
  unless (family || name == `IO.Promise.new) && (renameTerm value).equal expected do
    throw <| IO.userError "promise implementation differs from the checked logical model"
  checkToken strict publicStrict reference renameTerm
  let some (.opaqueInfo original) := reference.find? pointed | throw <| IO.userError "missing official promise carrier"
  unless !original.isUnsafe && Kernel.isDefEqGuarded reference {} original.value (mkConst ``standardCarrier) &&
      reference.getModuleIdxFor? name == reference.getModuleIdx? owner &&
      reference.getModuleIdxFor? pointed == reference.getModuleIdx? owner &&
      getExternNameFor reference `c `IO.Promise.new == some "lean_io_promise_new" do
    throw <| IO.userError "unexpected pinned promise representation"

end OmegaChecks.InitPort.Promise

module
public import Lean
public import OmegaChecks.InitPort.ReferenceModify
import all Init.System.CancelToken

open Lean
namespace OmegaChecks.InitPort.CancelFlag

private def isSet (read : IO.Ref Bool → BaseIO (Option Bool)) (tk : IO.CancelToken) : BaseIO Bool :=
  fun world =>
    let out := read (private_decl% IO.CancelToken.setRef tk) world
    ⟨out.val.getD false, out.state⟩

public def consumer := `IO.CancelToken.isSet

public def body (src templates : Environment) (d : DefinitionVal) : IO Expr := do
  let some (.defnInfo candidate) := templates.find? ``isSet | throw <| IO.userError "missing cancellation flag template"
  let read := mkApp2 (mkConst ReferenceModify.support) (mkConst `IO.RealWorld) (mkConst `Bool)
  let body := candidate.value.beta #[read]
  unless d.name == consumer && src.getModuleIdxFor? d.name == src.getModuleIdx? `Init.System.CancelToken &&
      Kernel.isDefEqGuarded src {} (← ReferenceModify.restore templates body) d.value do
    throw <| IO.userError "cancellation flag does not read the pinned mutable field"
  return body

end OmegaChecks.InitPort.CancelFlag

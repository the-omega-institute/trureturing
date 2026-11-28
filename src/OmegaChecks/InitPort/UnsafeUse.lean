module
public import Lean

open Lean
namespace OmegaChecks.InitPort

/-- A safe consumer must fail specifically on this reference. An unsafe consumer can use it. -/
public def checkUnsafeUse (env : Kernel.Environment) (ci : ConstantInfo) : IO Unit := do
  let alias : DefinitionVal := {
    name := ci.name ++ `_checkConsumer, type := ci.type, levelParams := ci.levelParams
    value := mkConst ci.name (ci.levelParams.map Level.param), hints := .opaque, safety := .safe}
  let .error (.other msg) := env.addDeclCore 0 1000 (.defnDecl alias) none
    | throw <| IO.userError s!"safe consumer did not fail on unsafe reference {ci.name}"
  unless msg == s!"invalid declaration, it uses unsafe declaration '{ci.name}'" do
    throw <| IO.userError s!"unexpected safe consumer rejection for {ci.name}: {msg}"
  if let .error e := env.addDeclCore 0 1000 (.defnDecl {alias with safety := .unsafe}) none then
    throw <| IO.userError s!"unsafe consumer of {ci.name}: {← e.toMessageData {} |>.toString}"

end OmegaChecks.InitPort

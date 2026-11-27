module
public import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.LogicalHandle
import OmegaChecks.InitPort.ReferenceModify
import OmegaChecks.InitPort.SyntaxArray
import OmegaChecks.InitPort.UnsafeUse

open Lean

namespace OmegaChecks.InitPort.UnsafeImplementation

private def aliases := [(ReferenceModify.implementation, ReferenceModify.consumer),
  (`Lean.Macro.getMethodsImp, `Lean.Macro.getMethods)] ++
  [LogicalHandle.shareState, LogicalHandle.shareFactory, LogicalHandle.macroMethods].filterMap
    fun api => api.implementedBy.map fun impl => (impl, api.allocator)

private def syntaxNames := [`Lean.TSyntaxArray.mkImpl, `Lean.TSyntaxArray.rawImpl]

public def supported (name : Name) := (aliases.lookup name).isSome || SyntaxArray.supported name

private def syntaxBody (raw : Bool) : Expr :=
  let syntaxType := mkConst `Lean.Syntax
  let typed := fun (k : Nat) => mkApp (mkConst `Lean.TSyntax) (.bvar k)
  let element := fun k => if raw then typed k else syntaxType
  let result := if raw then syntaxType else typed 1
  let input := if raw then mkApp (mkConst `Lean.TSyntaxArray) (.bvar 0) else mkApp (mkConst `Array [0]) syntaxType
  let field := mkApp (mkConst (if raw then `Lean.TSyntax.raw else `Lean.TSyntax.mk)) (.bvar 1)
  let items := mkApp2 (mkConst `Array.toList [0]) (element 1) (.bvar 0)
  let mapped := mkApp4 (mkConst `List.map [0, 0]) (element 1) result field items
  .lam `ks (mkConst `Lean.SyntaxNodeKinds) (.lam `xs input (mkApp2 (mkConst `Array.mk [0]) result mapped) .default) .implicit

/-- Recognize only the previously checked logical reference or elementwise syntax conversion. -/
public def isImplementation (ci : ConstantInfo) : Bool := Id.run do
  let .defnInfo d := ci | return false
  let n := InitKernelPort.originalName d.name
  unless d.name == InitKernelPort.portName n && d.safety == .unsafe && d.all == [d.name] do return false
  if let some api := aliases.lookup n then
    return d.value.equal (mkConst (InitKernelPort.portName api) (d.levelParams.map Level.param))
  unless SyntaxArray.supported n && d.levelParams.isEmpty do return false
  return d.value.eqv (InitKernelPort.translate InitKernelPort.portName (syntaxBody (n == `Lean.TSyntaxArray.rawImpl)))

/-- The terms typecheck under the kernel's safe rules. Clients see the original unsafe declarations. -/
public def replay (base : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut env := base
  for n in aliases.map Prod.fst ++ syntaxNames do
    let some ci := constants[InitKernelPort.portName n]? | continue
    unless isImplementation ci do throw <| IO.userError s!"incorrect unsafe implementation for {n}"
    let .defnInfo d := ci | throw <| IO.userError s!"expected definition {n}"
    unless (env.addDeclCore 0 1000 (.defnDecl {d with safety := .safe}) none).isOk do
      throw <| IO.userError s!"invalid logical body of {n}"
    let .ok next := env.addDeclCore 0 1000 (.defnDecl d) none | throw <| IO.userError s!"invalid unsafe declaration {n}"
    checkUnsafeUse next ci
    env := next
  return env

end OmegaChecks.InitPort.UnsafeImplementation

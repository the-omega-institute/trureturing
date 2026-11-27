module

public import OmegaChecks.InitPort.Translation

open Lean

namespace OmegaChecks.InitPort.DynamicValue

public def operations := [`Dynamic.mk, `Dynamic.typeName, `Dynamic.get?]
public def implementation (n : Name) := mkPrivateNameCore `Init.Dynamic (n.appendAfter "Impl")
public def operation? (n : Name) := operations.find? (fun op => n == op || n == implementation op)

/-- The private native entry refers to the opaque operation at its original unsafe interface. -/
public def isAlias (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let rename := if strict then InitKernelPort.portName else id
  let some op := operations.find? (fun op => ci.name == rename (implementation op)) | return false
  let .defnInfo d := ci | return false
  return d.safety == .unsafe && d.all == [d.name] && d.value == mkConst (rename op) (d.levelParams.map Level.param)

public def replay (base : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut env := base
  for op in operations do
    let some ci := constants[InitKernelPort.portName (implementation op)]? | continue
    let .defnInfo d := ci | throw <| IO.userError s!"invalid dynamic operation {op}"
    unless isAlias ci true && (env.addDeclCore 0 1000 (.defnDecl {d with safety := .safe}) none).isOk do
      throw <| IO.userError s!"ill-typed dynamic operation {op}"
    let .ok next := env.addDeclCore 0 1000 (.defnDecl d) none | throw <| IO.userError s!"invalid unsafe entry for {op}"
    env := next
  return env

end OmegaChecks.InitPort.DynamicValue

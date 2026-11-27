module
public import Lean.Replay
public import OmegaChecks.InitPort.Translation

open Lean

namespace OmegaChecks.InitPort.Persistent

public def upstream := `Runtime.markPersistent
public def name := InitKernelPort.portName upstream

/-- Only the original unsafe return of its BaseIO input can use this native boundary. -/
public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let rename := if strict then InitKernelPort.portName else id
  let .defnInfo d := ci | return false
  unless d.name == rename upstream && d.safety == .unsafe && d.levelParams.isEmpty && d.all == [d.name] do
    return false
  let .forallE _ (.sort (.succ .zero)) (.forallE _ (.bvar 0) out .default) .implicit := d.type | return false
  let .lam _ (.sort (.succ .zero)) (.lam _ (.bvar 0) body .default) .implicit := d.value | return false
  let baseIO := mkConst (rename `BaseIO)
  let monad := mkConst (rename `instMonadBaseIO)
  let applicative := mkApp2 (mkConst (rename `Monad.toApplicative) [0, 0]) baseIO monad
  let pureInstance := mkApp2 (mkConst (rename `Applicative.toPure) [0, 0]) baseIO applicative
  let pureReturn := mkApp4 (mkConst (rename `Pure.pure) [0, 0]) baseIO pureInstance (.bvar 1) (.bvar 0)
  return out == mkApp baseIO (.bvar 1) && body == pureReturn

/-- Lean's replay omits unsafe definitions. Replay the safe library first, check the exact
logical body as a safe declaration, and install its original unsafe interface in the result. -/
public def replay (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let base ← (← mkEmptyEnvironment).toKernelEnv.replay constants
  let some ci := constants[name]? | return base
  unless isOriginal ci true do throw <| IO.userError "invalid unsafe persistent marker"
  let .defnInfo d := ci | throw <| IO.userError "expected the persistent marker definition"
  let check (decl : DefinitionVal) : IO Kernel.Environment := do
    match base.addDeclCore 0 1000 (.defnDecl decl) none with
    | .ok checked => pure checked
    | .error _ => throw <| IO.userError "kernel rejected the persistent marker"
  let _ ← check {d with safety := .safe}
  check d

end OmegaChecks.InitPort.Persistent

module

public import OmegaChecks.InitPort.Persistent
import Lean.Compiler.BorrowedAnnotation

open Lean

namespace OmegaChecks.InitPort.UnsafeRuntime

private def defaultBody (value : Expr) : Expr → Expr
  | .forallE binder domain body bi => .lam binder domain.consumeMData (defaultBody value body) bi
  | _ => value

/-- Check the complete pinned opaque declaration, including its default instance and borrowing annotations. -/
public def matchesDefaultOpaque (ci : ConstantInfo) (upstream : Name) (strict : Bool)
    (levels : List Name) (prototype : Expr) (result instanceName : Name) : Bool := Id.run do
  let .opaqueInfo d := ci | return false
  let rename := if strict then InitKernelPort.portName else id
  let type := InitKernelPort.translate rename prototype
  let value := mkApp2 (mkConst (rename `Inhabited.default) [1]) (mkConst (rename result)) (mkConst (rename instanceName))
  return d.name == rename upstream && d.isUnsafe && d.all == [d.name] && d.levelParams == levels &&
    d.type.equal type && d.value.equal (defaultBody value type)

public def isExclusive (ci : ConstantInfo) (strict : Bool) : Bool :=
  let type := .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (markBorrowed (.bvar 0)) (mkConst `Bool) .default) .implicit
  matchesDefaultOpaque ci `isExclusiveUnsafe strict [`u] type `Bool `instInhabitedBool

public def exclusiveABI (env : Environment) (strict : Bool) : Bool := Id.run do
  let name := if strict then InitKernelPort.portName `isExclusiveUnsafe else `isExclusiveUnsafe
  let expected := if strict then (`isExclusiveUnsafe).mangle "omega_word_" else "lean_is_exclusive_obj"
  let some (.extern _ args .uint8 ⟨[.standard `all entry]⟩) := IR.findEnvDecl env name | return false
  return entry == expected && args.map (fun p => (p.ty, p.borrow)) == #[(.erased, false), (.tobject, true)]

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool :=
  Persistent.isOriginal ci strict || isExclusive ci strict

/-- Replay the checked library before installing the exact pinned opaque as unsafe. -/
public def replay (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let base ← Persistent.replay constants
  let some ci := constants[InitKernelPort.portName `isExclusiveUnsafe]? | return base
  unless isExclusive ci true do throw <| IO.userError "invalid unsafe exclusivity observation"
  let .opaqueInfo d := ci | throw <| IO.userError "expected the opaque exclusivity observation"
  let check (decl : OpaqueVal) : IO Kernel.Environment := do
    match base.addDeclCore 0 1000 (.opaqueDecl decl) none with
    | .ok checked => pure checked
    | .error _ => throw <| IO.userError "kernel rejected the exclusivity observation"
  discard <| check {d with isUnsafe := false}
  check d

end OmegaChecks.InitPort.UnsafeRuntime

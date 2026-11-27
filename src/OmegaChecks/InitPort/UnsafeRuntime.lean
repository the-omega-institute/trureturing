module

public import OmegaChecks.InitPort.Persistent
public import OmegaChecks.InitPort.ReferencePut
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

public def isShareCommonObject (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let upstream := if strict then InitKernelPort.originalName ci.name else ci.name
  let object := markBorrowed (mkConst `ShareCommon.Object)
  let arg (binder : Name) (type : Expr) := Expr.forallE binder object type .default
  match upstream with
  | `ShareCommon.Object.eq =>
    return matchesDefaultOpaque ci upstream strict [] (arg `a (arg `b (mkConst `Bool))) `Bool `instInhabitedBool
  | `ShareCommon.Object.hash =>
    return matchesDefaultOpaque ci upstream strict [] (arg `a (mkConst `UInt64)) `UInt64 `instInhabitedUInt64
  | _ => return false

/-- Return the pinned runtime symbol after checking both the result representation and borrowing. -/
public def observerSymbol? (env : Environment) (owner name : Name) (strict : Bool) : Option String := do
  if owner == `Init.Util && name == `isExclusiveUnsafe then
    guard (exclusiveABI env strict)
    return "lean_is_exclusive_obj"
  guard (owner == `Init.ShareCommon)
  let isEq := name == `ShareCommon.Object.eq
  guard (isEq || name == `ShareCommon.Object.hash)
  let pinned := if isEq then "lean_sharecommon_eq" else "lean_sharecommon_hash"
  let symbol := if strict && !isEq then "omega_share_common_object_hash" else pinned
  let borrowed := (IR.IRType.tobject, true)
  let args := if isEq then #[borrowed, borrowed] else #[borrowed]
  let result := if isEq then .uint8 else if strict then .tobject else IR.IRType.uint64
  let target := if strict then InitKernelPort.portName name else name
  let .extern _ params out ⟨[.standard `all entry]⟩ ← IR.findEnvDecl env target | none
  guard (entry == symbol && out == result && params.map (fun p => (p.ty, p.borrow)) == args)
  return pinned

private def originalOpaque (ci : ConstantInfo) (strict : Bool) : Bool :=
  isExclusive ci strict || isShareCommonObject ci strict

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool :=
  Persistent.isOriginal ci strict || originalOpaque ci strict || ReferencePut.isOriginal ci strict

/-- Replay the checked library before installing each pinned opaque at its original unsafe boundary. -/
public def replay (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut base ← Persistent.replay constants
  for upstream in [`isExclusiveUnsafe, `ShareCommon.Object.eq, `ShareCommon.Object.hash] do
    let some ci := constants[InitKernelPort.portName upstream]? | continue
    unless originalOpaque ci true do throw <| IO.userError s!"invalid pinned unsafe observation {upstream}"
    let .opaqueInfo d := ci | throw <| IO.userError s!"expected opaque observation {upstream}"
    let check (decl : OpaqueVal) : IO Kernel.Environment := do
      match base.addDeclCore 0 1000 (.opaqueDecl decl) none with
      | .ok checked => pure checked
      | .error _ => throw <| IO.userError s!"kernel rejected unsafe observation {upstream}"
    discard <| check {d with isUnsafe := false}
    base ← check d
  ReferencePut.replay base constants

end OmegaChecks.InitPort.UnsafeRuntime

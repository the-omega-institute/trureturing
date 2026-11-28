module

public import OmegaChecks.InitPort.ArraySafety
public import OmegaChecks.InitPort.EffectRun
public import OmegaChecks.InitPort.Persistent
public import OmegaChecks.InitPort.ReferencePut
public import OmegaChecks.InitPort.PointerComparison
public import OmegaChecks.InitPort.TypeName
public import OmegaChecks.InitPort.UnsafeImplementation
public import OmegaChecks.InitPort.DynamicValue
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

public def isAddress (ci : ConstantInfo) (strict : Bool) : Bool :=
  let type := .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (markBorrowed (.bvar 0)) (mkConst `USize) .default) .implicit
  matchesDefaultOpaque ci `ptrAddrUnsafe strict [`u] type `USize `instInhabitedUSize

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
  if owner == `Init.Util && name == `ptrAddrUnsafe then
    let target := if strict then InitKernelPort.portName name else name
    let entry := if strict then name.mangle "omega_word_" else "lean_ptr_addr"
    let .extern _ params result ⟨[.standard `all symbol]⟩ ← IR.findEnvDecl env target | none
    guard (symbol == entry && result == (if strict then .tobject else .usize) &&
      params.map (fun p => (p.ty, p.borrow)) == #[(.erased, false), (.tobject, true)])
    return "lean_ptr_addr"
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
  isExclusive ci strict || isAddress ci strict || isShareCommonObject ci strict

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool :=
  ArraySafety.isOriginal ci strict || (strict && UnsafeImplementation.isImplementation ci) || DynamicValue.isAlias ci strict || TypeName.isUnsafeConversion ci strict || Persistent.isOriginal ci strict || originalOpaque ci strict || PointerComparison.isOriginal ci strict || ReferencePut.isOriginal ci strict || EffectRun.isOriginal ci strict

/-- Replay the checked library before installing each pinned opaque at its original unsafe boundary. -/
public def replay (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut base ← DynamicValue.replay (← TypeName.replay (← Persistent.replay constants) constants) constants
  base ← ArraySafety.replay base constants
  base ← UnsafeImplementation.replay base constants
  let mut checked := base
  for upstream in [`ptrAddrUnsafe, `isExclusiveUnsafe, `ShareCommon.Object.eq, `ShareCommon.Object.hash] do
    let some ci := constants[InitKernelPort.portName upstream]? | continue
    unless originalOpaque ci true do throw <| IO.userError s!"invalid pinned unsafe observation {upstream}"
    let .opaqueInfo d := ci | throw <| IO.userError s!"expected opaque observation {upstream}"
    let check (env : Kernel.Environment) (decl : OpaqueVal) : IO Kernel.Environment := do
      match env.addDeclCore 0 1000 (.opaqueDecl decl) none with
      | .ok checked => pure checked
      | .error _ => throw <| IO.userError s!"kernel rejected unsafe observation {upstream}"
    checked ← check checked {d with isUnsafe := false}
    base ← check base d
  base ← PointerComparison.replay checked base constants
  EffectRun.replay (← ReferencePut.replay base constants) constants

end OmegaChecks.InitPort.UnsafeRuntime

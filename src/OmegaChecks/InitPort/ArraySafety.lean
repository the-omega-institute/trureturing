module
public import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.UnsafeUse

open Lean
namespace OmegaChecks.InitPort.ArraySafety

private def borrowedReads : List Name :=
  [`Array.getInternalBorrowed, `Array.get!InternalBorrowed, `Array.ugetBorrowed]

/-- Array operations with constructive strict bodies and a pinned unsafe interface. -/
public def names : List Name := borrowedReads ++ [
  `Array.mapMUnsafe, `Array.mapFinIdxMUnsafe, `Array.modifyMUnsafe, `Array.anyMUnsafe, `Array.foldlMUnsafe, `Array.foldrMUnsafe, `Array.forIn'Unsafe,
  `ByteArray.foldlMUnsafe, `ByteArray.forInUnsafe, `FloatArray.foldlMUnsafe, `FloatArray.forInUnsafe]

public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool :=
  let n := if strict then InitKernelPort.originalName ci.name else ci.name
  ci.name == (if strict then InitKernelPort.portName n else n) && ci.isUnsafe && names.contains n &&
    match ci with
    | .defnInfo d => d.all == [d.name] && !borrowedReads.contains n
    | .opaqueInfo d => d.all == [d.name] && borrowedReads.contains n
    | _ => false

/-- Check the exact body as safe in a separate environment before installing its public unsafe name. -/
public def verify (env : Kernel.Environment) (decl : Declaration) (limit : USize) :
    Except Kernel.Exception Kernel.Environment := do
  match decl with
  | .defnDecl d => discard <| env.addDeclCore limit 1000 (.defnDecl {d with safety := .safe}) none
  | .opaqueDecl d => discard <| env.addDeclCore limit 1000 (.opaqueDecl {d with isUnsafe := false}) none
  | _ => throw (.other "expected an array definition or opaque declaration")
  env.addDeclCore limit 1000 decl none

public def replay (base : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut env := base
  for n in names do
    let some ci := constants[InitKernelPort.portName n]? | continue
    unless isOriginal ci true do throw <| IO.userError s!"wrong strict array safety or declaration kind: {n}"
    let decl ← match ci with
      | .defnInfo d => pure (.defnDecl d)
      | .opaqueInfo d => pure (.opaqueDecl d)
      | _ => throw <| IO.userError s!"invalid strict array operation: {n}"
    match verify env decl 0 with
    | .ok next =>
      checkUnsafeUse next ci
      env := next
    | .error e => throw <| IO.userError s!"kernel rejected {n}: {← e.toMessageData {} |>.toString}"
  return env

end OmegaChecks.InitPort.ArraySafety

module

public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF

namespace OmegaChecks.InitPort.IONative

private def specs : List (Name × String × IR.IRType) :=
  [(`IO.getNumHeartbeats, "lean_io_get_num_heartbeats", .tobject), (`IO.setNumHeartbeats, "lean_io_set_heartbeats", .tagged),
   (`IO.monoMsNow, "lean_io_mono_ms_now", .tobject), (`IO.monoNanosNow, "lean_io_mono_nanos_now", .tobject),
   (`IO.getTID, "lean_io_get_tid", .uint64), (`IO.initializing, "lean_io_initializing", .uint8),
   (`IO.sleep, "", .tagged), (`Runtime.hold, "lean_runtime_hold", .tagged),
   (`Runtime.forget, "lean_runtime_forget", .tagged), (`Runtime.markMultiThreaded, "lean_runtime_mark_multi_threaded", .tobject)]

public def supported (name : Name) : Bool := specs.any (·.1 == name)

/-- The official BaseIO discards its world parameter. Strict ST.Out returns that same world
beside the result of the pinned operation. -/
public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := InitKernelPort.originalName n
  let some (_, expected, ret) := specs.find? (·.1 == official) | throw <| IO.userError s!"unknown BaseIO operation {n}"
  let some ci := source.find? official | throw <| IO.userError s!"missing upstream BaseIO operation {official}"
  let some target := strict.find? n | throw <| IO.userError s!"missing strict BaseIO operation {n}"
  unless target.type == InitKernelPort.translate InitKernelPort.portName ci.type do throw <| IO.userError s!"different BaseIO types {n}"
  let some original := IR.findEnvDecl source official | throw <| IO.userError s!"missing upstream BaseIO IR {official}"
  let entry ← match original with
    | .extern _ _ _ ⟨[.standard `all e]⟩ => if e == expected then pure e else throw <| IO.userError s!"unexpected BaseIO primitive {e}"
    | .fdecl .. => if official == `IO.sleep then pure (getSymbolStem source official) else throw <| IO.userError s!"expected BaseIO extern {official}"
    | _ => throw <| IO.userError s!"unexpected BaseIO declaration {official}"
  let some (.extern _ actual .object ⟨[.standard `all installed]⟩) := IR.findEnvDecl strict n | throw <| IO.userError s!"missing strict BaseIO ABI {n}"
  let some pair := ctorLayoutExt.find? strict `Omega.ST.Out.mk | throw <| IO.userError "missing strict ST.Out"
  let #[.object 0 _, .object 1 _] := pair.fieldInfo | throw <| IO.userError "invalid ST.Out fields"
  unless pair.ctorInfo.cidx == 0 && pair.ctorInfo.size == 2 && pair.ctorInfo.usize == 0 && pair.ctorInfo.ssize == 0 do
    throw <| IO.userError "unexpected packed ST.Out"
  let runtime := official.getPrefix == `Runtime
  let numeric := official == `IO.setNumHeartbeats || official == `IO.sleep
  let operand := runtime || numeric
  let mut src := if runtime then #[IR.IRType.erased, .tobject] else if numeric then #[if official == `IO.sleep then .uint32 else .tobject] else #[]
  src := src.push .void
  let dest := (if runtime then #[IR.IRType.erased, .tobject] else if numeric then #[.tobject] else #[]).push .tobject
  unless original.resultType == ret && original.params.map (·.ty) == src && actual.map (·.ty) == dest && installed == symbol do
    throw <| IO.userError s!"unexpected BaseIO calling convention at {n}: {actual.map (·.ty)}"
  NativeState.checkNativeNat strict
  if official == `IO.sleep || ret == .uint64 then
    for name in [`Omega.Fin, `Omega.BitVec, if ret == .uint64 then `Omega.UInt64 else `Omega.UInt32] do
      let some (some f) := impureTrivialStructureInfoExt.find? strict name | throw <| IO.userError s!"missing strict word {name}"
      unless f.fieldIdx == 0 do throw <| IO.userError s!"invalid strict word {name}"
  let i := if runtime then 1 else 0
  let srcBorrow := operand && original.params[i]!.borrow
  let dstBorrow := operand && actual[i]!.borrow
  let word := official == `IO.sleep
  let prepare := if operand && !word && !srcBorrow && dstBorrow then "  lean_inc(value);\n" else ""
  let cleanup := if operand && (word || srcBorrow) && !dstBorrow then "  lean_dec(value);\n" else ""
  let world := if actual.back!.borrow then "  lean_inc(world);\n" else ""
  let param := if !operand then "void" else if word then "uint32_t" else "lean_obj_arg"
  let arg := if !operand then "" else if word then "lean_uint32_of_nat(value)" else "value"
  let retTy := if ret == .uint64 then "uint64_t" else if ret == .uint8 then "uint8_t" else "lean_obj_res"
  let call := s!"{entry}({arg})"
  let value := if ret == .uint64 then s!"lean_uint64_to_nat({call})" else if ret == .uint8 then s!"lean_box({call})" else call
  let decl := if entry == "lean_runtime_hold" then "" else s!"extern {retTy} {entry}({param});\n"
  let args := if operand then "lean_obj_arg value, lean_obj_arg world" else "lean_obj_arg world"
  return "\n" ++ decl ++ s!"LEAN_EXPORT lean_obj_res {symbol}({args}) \{\n{prepare}  lean_object *value_out = {value};\n{cleanup}{world}" ++
    "  lean_object *out = lean_alloc_ctor(0, 2, 0);\n  lean_ctor_set(out, 0, value_out);\n  lean_ctor_set(out, 1, world);\n  return out;\n}\n"

end OmegaChecks.InitPort.IONative

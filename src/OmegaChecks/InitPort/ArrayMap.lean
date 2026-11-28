module
public import OmegaChecks.InitPort.Translation
public import OmegaChecks.InitPort.IndexedNative
public import OmegaChecks.InitPort.NativeState
import all Init.Data.Array.Basic
import Lean.Compiler.ImplementedByAttr

open Lean

namespace OmegaChecks.InitPort.ArrayMap

/-- The private loops accept partially rewritten arrays of untyped non-scalars. Their
unchecked casts require the input invariant established by the two public entry points. -/
public def reference? (n : Name) : Option Name :=
  if n == `Array.mapMUnsafe then some `Array.mapM
  else if n == `Array.mapFinIdxMUnsafe then some `Array.mapFinIdxM else none

/-- The compiler directs calls to the public specification to this exact native implementation. -/
public def check (env : Environment) (d : DefinitionVal) (candidate : Expr) : IO Unit := do
  let some api := reference? d.name | throw <| IO.userError s!"unknown array traversal {d.name}"
  let some (.defnInfo spec) := env.find? api | throw <| IO.userError s!"missing {api}"
  let levels := d.levelParams.map Level.param
  unless d.safety == .unsafe && spec.safety == .safe && d.all == [d.name] &&
      env.getModuleIdxFor? d.name == env.getModuleIdx? `Init.Data.Array.Basic &&
      env.getModuleIdxFor? api == env.getModuleIdxFor? d.name &&
      Compiler.getImplementedBy? env api == some d.name && levels.length == spec.levelParams.length &&
      candidate == mkConst api levels &&
      Kernel.isDefEqGuarded env {} (spec.type.instantiateLevelParams spec.levelParams levels) d.type do
    throw <| IO.userError s!"unexpected array traversal implementation {d.name}"

/-- Run the pinned native loop, transporting only the input array and the array delivered to pure. -/
public def wrapper (source strict : Environment) (name : Name) (symbol : String) : IO String := do
  let official := InitKernelPort.originalName name
  let some (.defnInfo upstream) := source.find? official | throw <| IO.userError s!"missing {official}"
  let some (.defnInfo localDecl) := strict.find? name | throw <| IO.userError s!"missing {name}"
  check source upstream (InitKernelPort.translate InitKernelPort.originalName localDecl.value)
  unless localDecl.safety == .unsafe && localDecl.type == InitKernelPort.translate InitKernelPort.portName upstream.type do
    throw <| IO.userError s!"incorrect strict signature for {name}"
  let indexed := official == `Array.mapFinIdxMUnsafe
  let args (array : IR.IRType) := #[(IR.IRType.erased, false), (.erased, false), (.erased, false), (.object, false)] ++
    (if indexed then #[(array, false), (.tobject, false)] else #[(.tobject, false), (array, false)])
  NativeState.verify strict name (args .tobject) .tobject symbol
  let some (.fdecl _ params .tobject ..) := IR.findEnvDecl source official
    | throw <| IO.userError s!"missing pinned native array traversal {official}"
  unless params.map (fun p => (p.ty, p.borrow)) == args .object do
    throw <| IO.userError s!"unexpected pinned native calling convention for {official}"
  IndexedNative.checkDataTypes source strict [`List]
  IndexedNative.checkMonadDictionary source strict
  NativeState.checkErasedField strict `Omega.Array
  let target := getSymbolStem source official
  let order := if indexed then "values, f" else "f, values"
  let formals := if indexed then "lean_obj_arg xs, lean_obj_arg f" else "lean_obj_arg f, lean_obj_arg xs"
  return "\n#include \"array_map_runtime.h\"\n" ++
    s!"extern lean_obj_res {target}(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);\n" ++
    s!"LEAN_EXPORT lean_obj_res {symbol}(lean_obj_arg inst, {formals}) \{\n" ++
    "  lean_object *values;\n  lean_object *adapted = omega_array_map_prepare(inst, xs, &values);\n" ++
    s!"  return {target}(lean_box(0), lean_box(0), lean_box(0), adapted, {order});\n}\n"

end OmegaChecks.InitPort.ArrayMap

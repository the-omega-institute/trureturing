module
public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.IndexedNative
import all Lean.Compiler.LCNF.MonoTypes
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.FloatArrayNative

public def operations := [`FloatArray.mk, `FloatArray.emptyWithCapacity, `FloatArray.push,
  `FloatArray.get!, `FloatArray.set!, `FloatArray.set, `FloatArray.uset,
  `FloatArray.markLinear, `FloatArray.propagateMark]

/-- Keep the public list field in slot zero. A distinct heap cell carries the runtime
identity, capacity, and linearity of each FloatArray, including empty arrays. -/
public def prepareLayout : CoreM Unit := do
  modifyEnv fun env =>
    impureTrivialStructureInfoExt.insert (trivialStructureInfoExt.insert env `Omega.FloatArray none) `Omega.FloatArray none

public def finishLayout : CoreM Unit := do
  let name := `Omega.FloatArray.mk
  let some l := ctorLayoutExt.find? (← getEnv) name | throwError "missing strict FloatArray constructor"
  let #[.object 0 _] := l.fieldInfo | throwError "unexpected strict FloatArray field"
  unless l.ctorInfo.size == 1 && l.ctorInfo.ssize == 0 && l.ctorInfo.usize == 0 && l.ctorInfo.cidx == 0 do
    throwError "unexpected strict FloatArray constructor layout"
  -- The compiler knows the whole allocation footprint when considering constructor reuse.
  modifyEnv fun env => ctorLayoutExt.insert env name {l with ctorInfo := {l.ctorInfo with usize := 2, ssize := 1}}

public def boxed (env : Environment) : Bool :=
  (ctorLayoutExt.find? env `Omega.FloatArray.mk).any fun l =>
    l.ctorInfo.size == 1 && l.ctorInfo.usize == 2 && l.ctorInfo.ssize == 1

public def wrapper (source strict : Environment) (n : Name) (entry : String) : IO String := do
  let name := n.replacePrefix `Omega .anonymous
  let some ci := source.find? name | throw <| IO.userError s!"missing pinned float array entry {name}"
  let some di := strict.find? n | throw <| IO.userError s!"missing strict float array entry {n}"
  unless di.type == InitKernelPort.translate InitKernelPort.portName ci.type do
    throw <| IO.userError s!"different strict float array signature at {n}"
  IndexedNative.checkDataTypes source strict [`List]
  for t in [`Omega.Float, `Omega.Float.Model, `Omega.UInt64, `Omega.BitVec, `Omega.Fin, `Omega.Array] do
    unless (impureTrivialStructureInfoExt.find? strict t).join.any (·.fieldIdx == 0) do
      throw <| IO.userError s!"unexpected float array element representation in {t}"
  let obj := IR.IRType.object
  let nat := IR.IRType.tobject
  let flt := IR.IRType.float
  let (pinned, args, ret, borrows, call) ← match name with
    | `FloatArray.mk => pure ("lean_float_array_mk", #[obj], obj, #[false], "omega_float_array_wrap_list(a0)")
    | `FloatArray.emptyWithCapacity => pure ("lean_mk_empty_float_array", #[nat], obj, #[true], "omega_float_array_empty(a0)")
    | `FloatArray.get! => pure ("lean_float_array_get", #[obj,nat], flt, #[true,true], "omega_float_list_get(lean_ctor_get(a0, 0), a1)")
    | `FloatArray.set! => pure ("lean_float_array_set", #[obj,nat,flt], obj, #[false,true,false], "omega_float_array_set(a0, a1, a2)")
    | `FloatArray.set => pure ("lean_float_array_fset", #[obj,nat,flt,.erased], obj, #[false,true,false,false], "omega_float_array_set(a0, a1, a2)")
    | `FloatArray.uset => pure ("lean_float_array_uset", #[obj,.usize,flt,.erased], obj, #[false,false,false,false], "omega_float_array_uset(a0, a1, a2)")
    | `FloatArray.push => pure ("lean_float_array_push", #[obj,flt], obj, #[false,false], "omega_float_array_push(a0, a1)")
    | `FloatArray.markLinear => pure ("lean_sarray_mark_linear", #[obj], obj, #[false], "omega_float_array_mark(a0)")
    | `FloatArray.propagateMark => pure ("lean_sarray_propagate_mark", #[obj,obj], obj, #[true,false], "omega_float_array_propagate(a0, a1)")
    | _ => throw <| IO.userError s!"unknown float array entry {name}"
  let some (.extern _ upstream actualRet ⟨[.standard `all function]⟩) := IR.findEnvDecl source name
    | throw <| IO.userError s!"missing pinned native float array entry {name}"
  let some (.extern _ actual result ⟨[.standard `all target]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict native float array entry {n}"
  let argTypes := if name == `FloatArray.mk then #[nat] else
    args.map fun t => if t == flt || t == .usize then nat else t
  unless function == pinned && upstream.map (·.ty) == args && upstream.map (·.borrow) == borrows &&
      actualRet == ret && target == entry && actual.map (·.ty) == argTypes &&
      actual.map (·.borrow) == borrows && result == (if ret == flt then nat else ret) do
    throw <| IO.userError s!"float array calling convention mismatch at {n}: {actual.map fun a => (a.ty,a.borrow)}"
  let params := (args.zipIdx.filterMap fun (t, i) => if t == .erased then none else some s!"lean_object *a{i}").toList
  return s!"\n#include \"strict_float_array.h\"\nLEAN_EXPORT lean_obj_res {entry}({String.intercalate ", " params}) \{ return {call}; }\n"

end OmegaChecks.InitPort.FloatArrayNative

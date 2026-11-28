module
public import OmegaChecks.InitPort.ArraySafety
import OmegaChecks.InitPort.IndexedNative
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.BorrowedNative

public def symbol? : Name → Option String
  | `Array.getInternalBorrowed => some "lean_array_fget_borrowed"
  | `Array.get!InternalBorrowed => some "lean_array_get_borrowed"
  | `Array.ugetBorrowed => some "lean_array_uget_borrowed"
  | _ => none

/-- In the strict representation an array erases to its list. Its borrowed element is the
head field of the selected cons cell, with no increment on successful reads. -/
public def wrapper (source strict : Environment) (n : Name) (entry : String) : IO String := do
  let name := InitKernelPort.originalName n
  let some foreign := symbol? name | throw <| IO.userError s!"unknown borrowed read {n}"
  let some original := source.find? name | throw <| IO.userError s!"missing pinned borrowed read {name}"
  let some target := strict.find? n | throw <| IO.userError s!"missing strict borrowed read {n}"
  unless ArraySafety.isOriginal original false && ArraySafety.isOriginal target true &&
      target.type == InitKernelPort.translate InitKernelPort.portName original.type do
    throw <| IO.userError s!"incorrect borrowed read interface {n}"
  let some (.extern _ pinned .tobject ⟨[.standard `all externName]⟩) := IR.findEnvDecl source name
    | throw <| IO.userError s!"missing pinned borrowed read IR {name}"
  let some (.extern _ actual .tobject ⟨[.standard `all installed]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict borrowed read IR {n}"
  let bang := name == `Array.get!InternalBorrowed
  let word := name == `Array.ugetBorrowed
  let pinnedTypes : Array IR.IRType := if bang then #[.erased, .tobject, .object, .tobject]
    else #[.erased, .object, if word then .usize else .tobject, .erased]
  let strictTypes : Array IR.IRType := if bang then #[.erased, .tobject, .tobject, .tobject]
    else #[.erased, .tobject, .tobject, .erased]
  let borrows := if bang then #[false, true, true, true] else #[false, true, !word, false]
  unless externName == foreign && installed == entry && pinned.map (·.ty) == pinnedTypes &&
      actual.map (·.ty) == strictTypes && pinned.map (·.borrow) == borrows && actual.map (·.borrow) == borrows do
    throw <| IO.userError s!"invalid borrowed read ABI {n}: {actual.map fun a => (a.ty, a.borrow)}"
  IndexedNative.checkDataTypes source strict [`List]
  let layouts := [`Omega.Array] ++ (if bang then [`Omega.Inhabited] else []) ++
    (if word then [`Omega.USize, `Omega.BitVec, `Omega.Fin] else [])
  for layout in layouts do
    unless (impureTrivialStructureInfoExt.find? strict layout).join.any (·.fieldIdx == 0) do
      throw <| IO.userError s!"unexpected erased field for {layout}"
  let params := (if bang then "b_lean_obj_arg fallback, " else "") ++
    "b_lean_obj_arg xs, " ++ (if word then "lean_obj_arg i" else "b_lean_obj_arg i")
  let consume := if word then "lean_dec(i);" else ""
  let check := if bang then
    "if (lean_is_scalar(cell)) { lean_inc(fallback); return lean_array_get_panic(fallback); }" else ""
  return s!"\n#include \"strict_array_set.h\"\nLEAN_EXPORT b_lean_obj_res {entry}({params}) \{\n" ++
    s!"  b_lean_obj_arg cell = omega_array_list_at(xs, i);\n  {consume}\n  {check}\n  return lean_ctor_get(cell, 0);\n}\n"

end OmegaChecks.InitPort.BorrowedNative

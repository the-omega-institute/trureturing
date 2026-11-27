module

public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.IndexedNative
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF

namespace OmegaChecks.InitPort.SeparatorNative

/-- Preserve the callback's effects while converting the terminal array underneath arbitrary monads. -/
public def wrapper (source strict : Environment) (n official : Name) (symbol : String) : IO String := do
  let some src := source.find? official | throw <| IO.userError s!"missing separator operation {official}"
  let some dst := strict.find? n | throw <| IO.userError s!"missing strict separator operation {n}"
  unless dst.type == InitKernelPort.translate InitKernelPort.portName src.type do throw <| IO.userError "different separator types"
  let some (.fdecl _ params .tobject ..) := IR.findEnvDecl source official | throw <| IO.userError "missing pinned separator IR"
  let some (.extern _ actual .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError "missing strict separator IR"
  let auxiliary := isPrivateName official
  let suffix := if auxiliary then #[IR.IRType.tobject, .object] else #[]
  let abi := #[IR.IRType.erased, .object, .object, .tobject] ++ suffix
  let strictAbi := #[IR.IRType.erased, .object, .tobject, .tobject] ++ (if auxiliary then #[.tobject, .tobject] else #[])
  unless entry == symbol && params.map (·.ty) == abi && params.all (!·.borrow) && actual.map (·.ty) == strictAbi do
    throw <| IO.userError s!"unexpected separator ABI {n}: {actual.map (·.ty)}"
  IndexedNative.checkMonadDictionary source strict
  let target := getSymbolStem source official
  let operands := #["monad", "values", "callback"] ++ (if auxiliary then #["index", "acc"] else #[])
  let owned := (actual.extract 1 actual.size).zip operands
  let keep := String.join <| owned.toList.filterMap fun (p, a) =>
    if p.borrow && a != "monad" then some s!"  lean_inc({a});\n" else none
  let release := if actual[1]!.borrow then "" else "  lean_dec(monad);\n"
  let proto := String.intercalate ", " (List.replicate abi.size "lean_obj_arg")
  let arguments := String.intercalate ", " (operands.toList.map ("lean_obj_arg " ++ ·))
  let tail := if auxiliary then ", index, lean_array_mk(acc)" else ""
  return "\n#include \"sep_array.h\"\n" ++
    s!"extern lean_obj_res {target}({proto});\nLEAN_EXPORT lean_obj_res {entry}({arguments}) \{\n" ++
    s!"  lean_object *adapted = omega_sep_array_monad(monad);\n{keep}{release}  return {target}(lean_box(0), adapted, lean_array_mk(values), callback{tail});\n}\n"

end OmegaChecks.InitPort.SeparatorNative

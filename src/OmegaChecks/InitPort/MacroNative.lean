module

public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.IndexedNative
import OmegaChecks.InitPort.Translation
import Lean.Compiler.ImplementedByAttr

open Lean

namespace OmegaChecks.InitPort.MacroNative

public def supported (name : Name) : Bool :=
  name.getPrefix == `Lean.Macro && [`getMethods, `expandMacro?, `getCurrNamespace, `hasDecl,
    `resolveNamespace, `resolveGlobalName].contains (name.updatePrefix .anonymous)

/-- These methods project the registered callback and pass its arguments through without
inspecting syntax, strings or names. The callback runs on the caller's own context and state. -/
public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some src := source.find? official | throw <| IO.userError s!"missing source macro method {official}"
  let some dst := strict.find? n | throw <| IO.userError s!"missing strict macro method {n}"
  unless dst.type == InitKernelPort.translate InitKernelPort.portName src.type do
    throw <| IO.userError s!"different macro method types at {n}"
  let override := `Lean.Macro.getMethodsImp
  unless Compiler.getImplementedBy? source `Lean.Macro.getMethods == some override do
    throw <| IO.userError "unexpected MethodsRef reader"
  let name := if official == `Lean.Macro.getMethods then override else official
  let some (.fdecl _ args .object ..) := IR.findEnvDecl source name | throw <| IO.userError s!"missing pinned macro method IR {name}"
  let some (.extern _ actual .object ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict macro method IR {n}"
  let nullary := [`Lean.Macro.getMethods, `Lean.Macro.getCurrNamespace].contains official
  let contextState := #[(IR.IRType.object, true), (.object, false)]
  let expected := if nullary then contextState else #[(.tobject, false)] ++ contextState
  unless entry == symbol && args.map (fun p => (p.ty, p.borrow)) == expected && actual.map (·.ty) == args.map (·.ty) do
    throw <| IO.userError s!"different macro method calling conventions at {n}"
  IndexedNative.checkDataTypes source strict [`Lean.Macro.Context, `Lean.Macro.Methods, `EStateM.Result]
  let target := getSymbolStem source name
  let mut fields := #[]
  let mut decls := #[]
  let mut retain := ""
  let mut release := ""
  for (a,b) in args.zip actual, i in [:args.size] do
    let x := s!"a{i}"
    fields := fields.push x
    decls := decls.push ("lean_object *" ++ x)
    if !a.borrow && b.borrow then retain := retain ++ s!"  lean_inc({x});\n"
    if a.borrow && !b.borrow then release := release ++ s!"  lean_dec({x});\n"
  let signature := String.intercalate ", " decls.toList
  return s!"\nextern lean_obj_res {target}({signature});\nLEAN_EXPORT lean_obj_res {symbol}({signature}) \{\n" ++
    s!"{retain}  lean_obj_res r = {target}({String.intercalate ", " fields.toList});\n{release}  return r;\n}\n"

end OmegaChecks.InitPort.MacroNative

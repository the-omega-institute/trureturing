module
public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.SyntaxPositionNative

public def supported (n : Name) : Bool := [`Lean.Syntax.getHeadInfo?, `Lean.Syntax.getTailInfo?, `Lean.Syntax.getTailPos?].contains n

private def checkCtor (env : Environment) (n : Name) (tag pointers bytes : Nat) : IO Unit := do
  let some layout := ctorLayoutExt.find? env n | throw <| IO.userError s!"missing syntax layout: {n}"
  let c := layout.ctorInfo
  unless c.cidx == tag && c.size == pointers && c.usize == 0 && c.ssize == bytes &&
      layout.fieldInfo.size == pointers + bytes do throw <| IO.userError s!"unexpected syntax constructor: {n}"
  for field in layout.fieldInfo, i in [:layout.fieldInfo.size] do
    if i < pointers then
      let .object j _ := field | throw <| IO.userError s!"expected object field of {n}"
      unless i == j do throw <| IO.userError s!"reordered syntax field in {n}"
    else
      let .scalar 1 0 _ := field | throw <| IO.userError s!"invalid canonical flag in {n}"

public def checkLayout (source strict : Environment) : IO Unit := do
  for (env, p) in [(source, Name.anonymous), (strict, `Omega)] do
    for (name, tag, count, bytes) in [(`Lean.Syntax.missing, 0, 0, 0), (`Lean.Syntax.node, 1, 3, 0),
        (`Lean.Syntax.atom, 2, 2, 0), (`Lean.Syntax.ident, 3, 4, 0), (`Lean.SourceInfo.original, 0, 4, 0),
        (`Lean.SourceInfo.synthetic, 1, 2, 1), (`Lean.SourceInfo.none, 2, 0, 0),
        (`Option.none, 0, 0, 0), (`Option.some, 1, 1, 0)] do checkCtor env (p ++ name) tag count bytes
  checkCtor strict `Omega.List.nil 0 0 0
  checkCtor strict `Omega.List.cons 1 2 0
  for n in [`Omega.Array, `Omega.String.Pos.Raw] do
    let some (some field) := impureTrivialStructureInfoExt.find? strict n | throw <| IO.userError s!"missing erased syntax field: {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"invalid syntax field: {n}"

public def checkTreeLayout (source strict : Environment) : IO Unit := do
  checkLayout source strict
  for (env, p) in [(source, Name.anonymous), (strict, `Omega)] do
    for (name, tag, fields) in [(`Lean.Syntax.Preresolved.namespace, 0, 1),
        (`Lean.Syntax.Preresolved.decl, 1, 2), (`Substring.Raw.mk, 0, 3), (`List.nil, 0, 0), (`List.cons, 1, 2)] do
      checkCtor env (p ++ name) tag fields 0
    for n in [`Lean.TSyntax, `Lean.Syntax.TSepArray, `String.Pos.Raw] do
      let some (some field) := impureTrivialStructureInfoExt.find? env (p ++ n) | throw <| IO.userError s!"missing syntax layout {p ++ n}"
      unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected syntax projection {p ++ n}"

public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let tailPos := official == `Lean.Syntax.getTailPos?
  let some original := source.find? official | throw <| IO.userError s!"missing source query {official}"
  let some installed := strict.find? n | throw <| IO.userError s!"missing strict query {n}"
  unless installed.type == InitKernelPort.translate InitKernelPort.portName original.type do
    throw <| IO.userError s!"incorrect translated query type {n}"
  let some (.fdecl _ upstream .tobject ..) := IR.findEnvDecl source official | throw <| IO.userError s!"missing pinned {official}"
  unless upstream.map (fun p => (p.ty, p.borrow)) == (if tailPos then #[(.tobject, true), (.uint8, false)] else #[(.tobject, true)]) do
    throw <| IO.userError s!"invalid pinned position signature at {n}"
  let some (.extern _ operands .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict position signature: {n}"
  unless operands.map (·.ty) == upstream.map (·.ty) && entry == symbol do throw <| IO.userError s!"invalid strict position ABI: {n}"
  checkLayout source strict
  let target := getSymbolStem source official
  let more := if tailPos then ", uint8_t canonical" else ""
  let arg := if operands[0]!.borrow then "b_lean_obj_arg syntax" else "lean_obj_arg syntax"
  let cleanup := if operands[0]!.borrow then "" else "  lean_dec(syntax);\n"
  let reverse := if official == `Lean.Syntax.getHeadInfo? then "false" else "true"
  let call := if tailPos then s!"omega_syntax_position(syntax, true, canonical, NULL, {target})"
              else s!"omega_syntax_position(syntax, {reverse}, 0, {target}, NULL)"
  return s!"\n#include \"syntax_position.h\"\nextern lean_obj_res {target}(b_lean_obj_arg{more});\n" ++
    s!"LEAN_EXPORT lean_obj_res {symbol}({arg}{more}) \{\n  lean_obj_res result = {call};\n{cleanup}  return result;\n}\n"

end OmegaChecks.InitPort.SyntaxPositionNative

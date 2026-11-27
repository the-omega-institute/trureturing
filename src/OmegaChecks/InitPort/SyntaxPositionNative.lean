module
public import OmegaChecks.InitPort.NativeState
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.SyntaxPositionNative

public def supported (n : Name) : Bool := n == `Lean.Syntax.getHeadInfo? || n == `Lean.Syntax.getTailPos?

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

public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let head := official == `Lean.Syntax.getHeadInfo?
  let some (.fdecl _ upstream .tobject ..) := IR.findEnvDecl source official | throw <| IO.userError s!"missing pinned {official}"
  unless upstream.map (fun p => (p.ty, p.borrow)) == (if head then #[(.tobject, true)] else #[(.tobject, true), (.uint8, false)]) do
    throw <| IO.userError s!"invalid pinned position signature at {n}"
  let some (.extern _ operands .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict position signature: {n}"
  unless operands.map (·.ty) == upstream.map (·.ty) && entry == symbol do throw <| IO.userError s!"invalid strict position ABI: {n}"
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
  let target := getSymbolStem source official
  let more := if head then "" else ", uint8_t canonical"
  let arg := if operands[0]!.borrow then "b_lean_obj_arg syntax" else "lean_obj_arg syntax"
  let cleanup := if operands[0]!.borrow then "" else "  lean_dec(syntax);\n"
  let call := if head then s!"omega_syntax_position(syntax, 0, {target}, NULL)" else s!"omega_syntax_position(syntax, canonical, NULL, {target})"
  return s!"\n#include \"syntax_position.h\"\nextern lean_obj_res {target}(b_lean_obj_arg{more});\n" ++
    s!"LEAN_EXPORT lean_obj_res {symbol}({arg}{more}) \{\n  lean_obj_res result = {call};\n{cleanup}  return result;\n}\n"

end OmegaChecks.InitPort.SyntaxPositionNative

module

public import OmegaChecks.InitPort.NativeState
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.OriginalConstKind

/-! Compile unsigned-word primitives over the strict, Nat-backed Fin representation. -/

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

namespace OmegaChecks.InitPort.WordNative

private def word? : Name → Option (String × IR.IRType)
  | `UInt8 => some ("uint8", .uint8)
  | `UInt16 => some ("uint16", .uint16)
  | `UInt32 => some ("uint32", .uint32)
  | `UInt64 => some ("uint64", .uint64)
  | `USize => some ("usize", .usize)
  | _ => none

public def supported (source : Environment) (owner name : Name) : Bool :=
  let method := name.updatePrefix .anonymous
  let widths := [`toUInt8, `toUInt16, `toUInt32, `toUInt64, `toUSize]
  let ops := [`add, `sub, `mul, `div, `mod, `land, `lor, `xor, `complement, `neg,
              `shiftLeft, `shiftRight, `decLt, `decLe, `decEq, `toNat, `ofNat, `ofNatLT, `ofNat32]
  [`OmegaInit.Prelude, `OmegaInit.Data.UInt.BasicAux, `OmegaInit.Data.UInt.Basic].contains owner &&
    (((word? name.getPrefix).isSome && (ops ++ widths).contains method) ||
     (name.getPrefix == `Bool && widths.contains method)) && isExtern source name

private def symbol (n : Name) := "omega_word_" ++ (n.replacePrefix `Omega .anonymous).toString.replace "." "_"

public def install (names : Array Name) : CoreM Unit := do
  unless names.isEmpty do checkNativeNat (← getEnv)
  for n in names do
    modifyEnv fun e => privateConstKindsExt.insert e n .defn
    modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all (symbol n)]⟩)
    (← compileDeclsRef.get) #[n] {}

private def layout (env : Environment) (name : Name) : IO Unit := do
  for n in [`Omega.Fin, `Omega.BitVec, `Omega ++ name] do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"word argument does not erase to Nat: {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"incorrect word layout: {n}"

/-- Check both sides of the call and generate its ownership conversions from their stored IR. -/
public def wrapper (source strict : Environment) (n : Name) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some ci := source.find? official | throw <| IO.userError s!"unknown word primitive {official}"
  let some (.extern _ params ret ⟨[.standard `all target]⟩) := IR.findEnvDecl source official
    | throw <| IO.userError s!"expected pinned C primitive for {official}"
  let some (.extern _ actual result ⟨[.standard `all adapter]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict C primitive for {n}"
  unless actual.size == params.size && adapter == symbol n do throw <| IO.userError s!"incorrect word ABI: {n}"
  let mut type := ci.type
  let mut decls := #[]
  let mut args := #[]
  let mut cleanup := ""
  for (a, b) in params.zip actual, i in [:params.size] do
    let .forallE _ dom body _ := type | throw <| IO.userError s!"expected argument {i} of {n}"
    type := body
    if a.ty == .erased && b.ty == .erased then continue
    let arg := "a" ++ toString i
    let dom := dom.consumeMData.getAppFn.constName
    if let some (w, t) := word? dom then
      layout strict dom
      unless a.ty == t && b.ty == .tobject do throw <| IO.userError s!"wrong word argument at {n} {i}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push s!"lean_{w}_of_nat({arg})"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Nat && a.ty == .tobject && b.ty == .tobject && a.borrow == b.borrow then
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
    else if dom == `Bool && a.ty == .uint8 && b.ty == .uint8 then
      decls := decls.push ("uint8_t " ++ arg)
      args := args.push arg
    else throw <| IO.userError s!"unsupported argument of {n}: {dom}/{a.ty}/{b.ty}"
  let call := target ++ "(" ++ String.intercalate ", " args.toList ++ ")"
  let dom := type.consumeMData.getAppFn.constName
  let (output, value) ← if let some (w, t) := word? dom then do
    layout strict dom
    unless ret == t && result == .tobject do throw <| IO.userError s!"incorrect word result at {n}"
    pure ("lean_obj_res", s!"lean_{w}_to_nat({call})")
  else if dom == `Nat && (ret == .tobject || ret == .tagged) && result == .tobject then pure ("lean_obj_res", call)
  else if dom == `Decidable && ret == .uint8 && result == .uint8 then pure ("uint8_t", call)
  else throw <| IO.userError s!"unsupported result of {n}: {dom}/{ret}/{result}"
  return s!"\nLEAN_EXPORT {output} {adapter}({String.intercalate ", " decls.toList}) \{\n  {output} r = {value};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.WordNative

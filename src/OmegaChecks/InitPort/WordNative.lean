module

public import OmegaChecks.InitPort.NativeState
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.OriginalConstKind

/-! Compile machine-word primitives over their strict, Nat-backed Fin representation. -/

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

namespace OmegaChecks.InitPort.WordNative

private def bitsType : Name → Name
  | `Int8 => `UInt8
  | `Int16 => `UInt16
  | `Int32 => `UInt32
  | `Int64 => `UInt64
  | `ISize => `USize
  | n => n

private def word? (name : Name) : Option (String × IR.IRType) := match bitsType name with
  | `UInt8 => some ("uint8", .uint8)
  | `UInt16 => some ("uint16", .uint16)
  | `UInt32 => some ("uint32", .uint32)
  | `UInt64 => some ("uint64", .uint64)
  | `USize => some ("usize", .usize)
  | _ => none

public def usesPinnedFunction (n : Name) : Bool :=
  let method := n.updatePrefix .anonymous
  (word? n.getPrefix).isSome && (method == `pow || (method == `ofInt && bitsType n.getPrefix == n.getPrefix))

public def supported (source : Environment) (owner name : Name) : Bool :=
  let method := name.updatePrefix .anonymous
  let widths := [`toUInt8, `toUInt16, `toUInt32, `toUInt64, `toUSize, `toInt8, `toInt16, `toInt32, `toInt64, `toISize]
  let ops := [`add, `sub, `mul, `div, `mod, `land, `lor, `xor, `complement, `neg,
              `shiftLeft, `shiftRight, `log2, `abs, `toInt, `ofInt, `decLt, `decLe, `decEq, `toNat, `ofNat, `ofNatLT, `ofNat32]
  let base := owner == `OmegaInit.Prelude && name == `System.Platform.getNumBits
  let inOwner := [`OmegaInit.Prelude, `OmegaInit.Data.UInt.BasicAux, `OmegaInit.Data.UInt.Basic, `OmegaInit.Data.UInt.Log2,
                  `OmegaInit.Data.SInt.Basic].contains owner
  let primitive := ((word? name.getPrefix).isSome && (ops ++ widths).contains method) ||
    (name.getPrefix == `Bool && widths.contains method)
  ((base || (inOwner && primitive)) && isExtern source name) ||
    ([`OmegaInit.Data.UInt.Basic, `OmegaInit.Data.SInt.Basic].contains owner && usesPinnedFunction name)

private def symbol (n : Name) := "omega_word_" ++ (n.replacePrefix `Omega .anonymous).toString.replace "." "_"

public def install (names : Array Name) : CoreM Unit := do
  unless names.isEmpty do checkNativeNat (← getEnv)
  for n in names do
    modifyEnv fun e => privateConstKindsExt.insert e n .defn
    modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all (symbol n)]⟩)
    (← compileDeclsRef.get) #[n] {}

private def layout (env : Environment) (name : Name) : IO Unit := do
  for n in [`Omega.Fin, `Omega.BitVec, `Omega ++ bitsType name, `Omega ++ name].eraseDups do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"word argument does not erase to Nat: {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"incorrect word layout: {n}"

private def checkIntLayout (strict : Environment) : IO Unit := do
  for (ctor, tag) in [(`Omega.Int.ofNat, 0), (`Omega.Int.negSucc, 1)] do
    let some l := ctorLayoutExt.find? strict ctor | throw <| IO.userError s!"missing {ctor}"
    let #[.object 0 _] := l.fieldInfo | throw <| IO.userError s!"invalid integer field in {ctor}"
    unless l.ctorInfo.cidx == tag && l.ctorInfo.size == 1 && l.ctorInfo.ssize == 0 && l.ctorInfo.usize == 0 do
      throw <| IO.userError s!"unexpected integer constructor layout {ctor}"

/-- Check both sides of the call and generate its ownership conversions from their stored IR. -/
public def wrapper (source strict : Environment) (n : Name) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some ci := source.find? official | throw <| IO.userError s!"unknown word primitive {official}"
  let some impl := IR.findEnvDecl source official | throw <| IO.userError s!"no pinned IR for {official}"
  let params := impl.params
  let ret := impl.resultType
  let target ← match impl with
    | .extern _ _ _ ⟨[.standard `all entry]⟩ => pure entry
    | .fdecl .. =>
      unless usesPinnedFunction official && (getExportNameFor? source official).isNone do
        throw <| IO.userError s!"unexpected compiled word function {official}"
      pure (getSymbolStem source official)
    | _ => throw <| IO.userError s!"expected pinned C primitive for {official}"
  let some (.extern _ actual result ⟨[.standard `all adapter]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict C primitive for {n}"
  unless actual.size == params.size && adapter == symbol n do throw <| IO.userError s!"incorrect word ABI: {n}"
  let mut type := ci.type
  let mut decls := #[]
  let mut args := #[]
  let mut prepare := ""
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
    else if dom == `Unit && a.ty == .tagged && b.ty == .tagged then
      decls := decls.push ("lean_obj_arg " ++ arg)
      args := args.push arg
    else if dom == `Nat && a.ty == .tobject && b.ty == .tobject then
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if b.borrow && !a.borrow then throw <| IO.userError s!"borrowed Nat consumed at {n}"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Int && a.ty == .tobject && b.ty == .object && a.borrow then
      checkIntLayout strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *mag = lean_ctor_get({arg}, 0);\n  lean_inc(mag);\n"
      prepare := prepare ++ s!"  lean_object *value = lean_obj_tag({arg}) == 0 ? lean_nat_to_int(mag) : lean_int_neg_succ_of_nat(mag);\n"
      args := args.push "value"
      cleanup := cleanup ++ "  lean_dec(value);\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
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
  else if dom == `Int then do
    checkIntLayout strict
    unless (ret == .tobject || ret == .tagged) && result == .object do throw <| IO.userError s!"incorrect integer result at {n}"
    prepare := prepare ++ s!"  lean_object *i = {call};\n  uint8_t neg = lean_int_lt(i, lean_box(0));\n"
    prepare := prepare ++ "  lean_object *magnitude = lean_nat_abs(i);\n  lean_dec(i);\n"
    prepare := prepare ++ "  if (neg) { lean_object *p = lean_nat_pred(magnitude); lean_dec(magnitude); magnitude = p; }\n"
    prepare := prepare ++ "  lean_object *integer = lean_alloc_ctor(neg, 1, 0);\n  lean_ctor_set(integer, 0, magnitude);\n"
    pure ("lean_obj_res", "integer")
  else if dom == `Subtype && official == `System.Platform.getNumBits then do
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Subtype
      | throw <| IO.userError "missing platform width subtype layout"
    unless field.fieldIdx == 0 && ret == .tobject && result == .tobject do
      throw <| IO.userError "invalid platform width result ABI"
    pure ("lean_obj_res", call)
  else if dom == `Nat && (ret == .tobject || ret == .tagged) && result == .tobject then pure ("lean_obj_res", call)
  else if dom == `Decidable && ret == .uint8 && result == .uint8 then pure ("uint8_t", call)
  else throw <| IO.userError s!"unsupported result of {n}: {dom}/{ret}/{result}"
  let proto ← if usesPinnedFunction official then do
    let some (width, _) := word? official.getPrefix | throw <| IO.userError "unknown word width"
    let scalar := if width == "usize" then "size_t" else width ++ "_t"
    let inputs := if official.updatePrefix .anonymous == `pow then scalar ++ ", b_lean_obj_arg" else "b_lean_obj_arg"
    pure s!"\nextern {scalar} {target}({inputs});\n"
  else if official == `System.Platform.getNumBits then
    pure "\nextern lean_obj_res lean_system_platform_nbits(lean_obj_arg);\n" else pure ""
  return proto ++ s!"\nLEAN_EXPORT {output} {adapter}({String.intercalate ", " decls.toList}) \{\n{prepare}  {output} r = {value};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.WordNative

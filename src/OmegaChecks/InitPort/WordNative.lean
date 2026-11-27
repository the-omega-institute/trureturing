module

public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.SyntaxPositionNative
import OmegaChecks.InitPort.IndexedNative
import OmegaChecks.InitPort.ByteFoldNative
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.OriginalConstKind
import Lean.Compiler.ImplementedByAttr

/-! Compile scalar primitives over the strict, Nat-backed Fin representation. -/

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
  | `Float.Model => some ("uint64", .uint64)
  | `Float32.Model => some ("uint32", .uint32)
  | `UInt8 => some ("uint8", .uint8)
  | `UInt16 => some ("uint16", .uint16)
  | `UInt32 => some ("uint32", .uint32)
  | `UInt64 => some ("uint64", .uint64)
  | `USize => some ("usize", .usize)
  | _ => none

/-- The strict floating-point model stores IEEE bits in the corresponding unsigned word. -/
private def float? : Name → Option (String × IR.IRType)
  | `Float => some ("float", .float)
  | `Float32 => some ("float32", .float32)
  | _ => none

private def isFloatCall (source : Environment) (owner name : Name) : Bool := Id.run do
  unless [`OmegaInit.Data.Float.Float, `OmegaInit.Data.Float.Float32,
          `OmegaInit.Data.SInt.Float, `OmegaInit.Data.SInt.Float32].contains owner do return false
  let some ci := source.find? name | return false
  unless (ci matches .defnInfo _ | .opaqueInfo _) && isExtern source name do return false
  if (float? name.getPrefix).isSome &&
      [`toModel, `scaleB, `toString, `frExp].contains (name.updatePrefix .anonymous) then return true
  let mut ty := ci.type
  let mut sawFloat := false
  while let .forallE _ dom body _ := ty do
    let head := dom.consumeMData.getAppFn.constName
    unless (word? head).isSome || (float? head).isSome do return false
    sawFloat := sawFloat || (float? head).isSome
    ty := body
  let result := ty.consumeMData.getAppFn.constName
  return (sawFloat || (float? result).isSome) &&
    ((float? result).isSome || (word? result).isSome || [`Decidable, `Bool].contains result)

/-- The model-level operations run the pinned software arithmetic on their IEEE bit fields. -/
private def modelOperation (name : Name) : Bool :=
  [`Float.Model, `Float32.Model].contains name.getPrefix &&
    [`add, `sub, `mul, `div, `sqrt, `fma, `neg, `abs, `le, `lt, `beq, `isFinite, `isInf, `isNaN,
     `ofBits, `ofInt, `ofNat, `ofUInt8, `ofUInt16, `ofUInt32, `ofUInt64, `ofUSize,
     `ofInt8, `ofInt16, `ofInt32, `ofInt64, `ofISize, `toUInt8, `toUInt16, `toUInt32, `toUInt64,
     `toUSize, `toInt8, `toInt16, `toInt32, `toInt64, `toISize, `ofScientific].contains (name.updatePrefix .anonymous)

public def usesPinnedFunction (n : Name) : Bool :=
  let method := n.updatePrefix .anonymous
  let bytes := [`ByteArray.toList.loop, `ByteArray.findIdx?.loop, `ByteArray.findFinIdx?.loop].contains n
  let vector := n.getPrefix == `BitVec &&
    [`abs, `pow, `smod, `replicate, `reverse, `cpop, `cpopNatRec, `ctz, `clz, `clzAuxRec,
     `getLsbD, `getLsb, `getMsbD, `getMsb, `msb, `sdiv, `srem, `smtSDiv, `hash, `ofBoolListLE, `ofBoolListBE].contains method
  modelOperation n || ByteFoldNative.supported n || IndexedNative.supported n || SyntaxPositionNative.supported n || bytes || vector || [`Nat.repr, `Nat.reprFast, `Int.repr].contains n || [`BitVec.toHex, `BitVec.instToString].contains n || n == `Nat.bitwise || ((word? n.getPrefix).isSome && (method == `pow || (method == `ofInt && bitsType n.getPrefix == n.getPrefix))) ||
    (n.getPrefix == `Int && [`negOfNat, `subNatNat, `sign, `toNat, `pow, `fdiv, `fmod, `bdiv, `bmod].contains method)

public def supported (source : Environment) (owner name : Name) : Bool :=
  let method := name.updatePrefix .anonymous
  let widths := [`toUInt8, `toUInt16, `toUInt32, `toUInt64, `toUSize, `toInt8, `toInt16, `toInt32, `toInt64, `toISize]
  let ops := [`add, `sub, `mul, `div, `mod, `land, `lor, `xor, `complement, `neg,
              `shiftLeft, `shiftRight, `log2, `abs, `toInt, `ofInt, `decLt, `decLe, `decEq, `toNat, `ofNat, `ofNatLT, `ofNat32]
  let base := owner == `OmegaInit.Prelude && [`System.Platform.getNumBits, `Lean.Name.beq, `mixHash].contains name
  let inOwner := [`OmegaInit.Prelude, `OmegaInit.Data.UInt.BasicAux, `OmegaInit.Data.UInt.Basic, `OmegaInit.Data.UInt.Log2,
                  `OmegaInit.Data.SInt.Basic].contains owner
  let intOwner := [`OmegaInit.Data.Int.Basic, `OmegaInit.Data.Int.DivMod.Basic].contains owner
  let bitwise := owner == `OmegaInit.Data.Nat.Bitwise.Basic && name.getPrefix == `Nat &&
    [`land, `lor, `xor, `shiftLeft, `shiftRight].contains method
  let logarithm := owner == `OmegaInit.Data.Nat.Log2 && name == `Nat.log2
  let wordRepr := owner == `OmegaInit.Data.Repr && name == `USize.repr
  let byteOp := owner == `OmegaInit.Data.ByteArray.Basic && name.getPrefix == `ByteArray &&
    [`uget, `get, `get!, `uset, `set, `set!, `usize, `copySlice, `beq, `decEq, `hash].contains method
  let platform := owner == `OmegaInit.System.Platform && [`System.Platform.getIsWindows, `System.Platform.getIsOSX,
    `System.Platform.getIsLinux, `System.Platform.getIsEmscripten, `System.Platform.getTarget,
    `System.Platform.Internal.getHardwareConcurrency].contains name
  let modular := (owner == `OmegaInit.Data.Nat.Gcd && name == `Nat.gcd) ||
    (owner == `OmegaInit.Data.Nat.Div.Basic && name == `Nat.divExact) ||
    (owner == `OmegaInit.Data.Nat.PowMod && name == `Nat.powMod)
  let stringOp := owner == `OmegaInit.Data.String.Bootstrap && [`String.Internal.length, `String.Internal.append].contains name
  let textCompare := (owner == `OmegaInit.Data.String.PosRaw && [`String.getUTF8Byte, `String.getUtf8Byte].contains name) ||
    (owner == `OmegaInit.Data.Ord.String && name == `String.compare) ||
    (owner == `OmegaInit.Data.String.Slice && [`String.Slice.hash, `String.Slice.instDecidableLt].contains name) ||
    (owner == `OmegaInit.Data.String.Pattern.Basic && name == `String.Slice.Pattern.Internal.memcmpStr)
  let intPrimitive := intOwner && name.getPrefix == `Int &&
    [`neg, `add, `sub, `mul, `decEq, `decLe, `decLt, `decNonneg, `natAbs, `ediv, `emod, `tdiv, `tmod, `divExact].contains method
  let primitive := ((word? name.getPrefix).isSome && (ops ++ widths).contains method) ||
    (name.getPrefix == `Bool && widths.contains method)
  isFloatCall source owner name ||
    (owner == `OmegaInit.Data.ByteArray.Basic && ByteFoldNative.supported name) ||
    ([`OmegaInit.Data.Nat.Basic, `OmegaInit.Data.Nat.Div.Basic, `OmegaInit.Data.Nat.Lemmas,
    `OmegaInit.Data.Nat.Internal.Linear, `OmegaInit.Data.Fin.Lemmas].contains owner && IndexedNative.supported name) ||
    ([`OmegaInit.Data.Float.Model.Float, `OmegaInit.Data.Float.Model.Float32].contains owner && modelOperation name) ||
    (owner == `OmegaInit.Prelude && SyntaxPositionNative.supported name) ||
    ((base || intPrimitive || platform || byteOp || textCompare || modular || stringOp || wordRepr || bitwise || logarithm || (inOwner && primitive)) && isExtern source name) ||
    ((intOwner || [`OmegaInit.Data.ByteArray.Basic, `OmegaInit.Data.Int.Repr, `OmegaInit.Data.Repr, `OmegaInit.Data.Nat.Bitwise.Basic, `OmegaInit.Data.BitVec.Basic].contains owner || [`OmegaInit.Data.UInt.Basic, `OmegaInit.Data.SInt.Basic].contains owner) && usesPinnedFunction name)

private def symbol (n : Name) := (n.replacePrefix `Omega .anonymous).mangle "omega_word_"

public def install (names : Array Name) : CoreM Unit := do
  unless names.isEmpty do checkNativeNat (← getEnv)
  for n in names do
    modifyEnv fun e => privateConstKindsExt.insert e n .defn
    modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all (symbol n)]⟩)
    (← compileDeclsRef.get) #[n] {}

private def layout (env : Environment) (name : Name) : IO Unit := do
  let storage := if name == `Float.Model then `UInt64 else if name == `Float32.Model then `UInt32 else bitsType name
  for n in [`Omega.Fin, `Omega.BitVec, `Omega ++ storage, `Omega ++ name].eraseDups do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"word argument does not erase to Nat: {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"incorrect word layout: {n}"

private def checkIntLayout (strict : Environment) : IO Unit := do
  for (ctor, tag) in [(`Omega.Int.ofNat, 0), (`Omega.Int.negSucc, 1)] do
    let some l := ctorLayoutExt.find? strict ctor | throw <| IO.userError s!"missing {ctor}"
    let #[.object 0 _] := l.fieldInfo | throw <| IO.userError s!"invalid integer field in {ctor}"
    unless l.ctorInfo.cidx == tag && l.ctorInfo.size == 1 && l.ctorInfo.ssize == 0 && l.ctorInfo.usize == 0 do
      throw <| IO.userError s!"unexpected integer constructor layout {ctor}"

private def checkFloatLayout (env : Environment) (name : Name) : IO Unit := do
  layout env (if name == `Float32 then `UInt32 else `UInt64)
  for n in [`Omega ++ name, `Omega ++ name ++ `Model] do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"floating-point bits have no strict representation in {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected floating-point field in {n}"

/-- Check both sides of the call and generate its ownership conversions from their stored IR. -/
public def wrapper (source strict : Environment) (n : Name) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  if ByteFoldNative.supported official then return ← ByteFoldNative.wrapper source strict n (symbol n)
  if IndexedNative.supported official then return ← IndexedNative.wrapper source strict n (symbol n)
  if SyntaxPositionNative.supported official then return ← SyntaxPositionNative.wrapper source strict n (symbol n)
  let some ci := source.find? official | throw <| IO.userError s!"unknown word primitive {official}"
  let compiled ← if official == `Nat.repr then do
    unless (Compiler.getImplementedBy? source official) == some `Nat.reprFast do throw <| IO.userError "unexpected Nat.repr implementation"
    let some fast := source.find? `Nat.reprFast | throw <| IO.userError "missing pinned Nat.reprFast"
    unless fast.type == ci.type do throw <| IO.userError "Nat.reprFast type differs from Nat.repr"
    pure `Nat.reprFast
  else pure official
  let some impl := IR.findEnvDecl source compiled | throw <| IO.userError s!"no pinned IR for {official}"
  let params := impl.params
  let ret := impl.resultType
  let target ← match impl with
    | .extern _ _ _ ⟨[.standard `all entry]⟩ => pure entry
    | .fdecl .. =>
      unless usesPinnedFunction official && (getExportNameFor? source compiled).isNone do
        throw <| IO.userError s!"unexpected compiled word function {official}"
      pure (getSymbolStem source compiled)
    | _ => throw <| IO.userError s!"expected pinned C primitive for {official}"
  let some (.extern _ actual result ⟨[.standard `all adapter]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict C primitive for {n}"
  unless actual.size == params.size && adapter == symbol n do throw <| IO.userError s!"incorrect word ABI: {n}"
  let mut type := ci.type
  let mut decls := #[]
  let mut args := #[]
  let mut prepare := ""
  let mut cleanup := ""
  let mut hasString := false
  let mut hasName := false
  for (a, b) in params.zip actual, i in [:params.size] do
    let .forallE _ dom body _ := type | throw <| IO.userError s!"expected argument {i} of {n}"
    type := body
    if a.ty == .erased && b.ty == .erased then continue
    let arg := "a" ++ toString i
    let byteSearch := official == `ByteArray.findIdx?.loop || official == `ByteArray.findFinIdx?.loop
    if (official == `Nat.bitwise && i == 0) || (byteSearch && i == 1) then
      let bool := mkConst `Bool
      let .forallE _ left right _ := dom.consumeMData | throw <| IO.userError "invalid predicate"
      if byteSearch then
        layout strict `UInt8
        unless left == mkConst `UInt8 && right == bool do throw <| IO.userError "invalid byte predicate signature"
      else
        let .forallE _ middle out _ := right | throw <| IO.userError "invalid binary boolean predicate"
        unless left == bool && middle == bool && out == bool do throw <| IO.userError "invalid binary bit operation"
      let some strictInfo := strict.find? n | throw <| IO.userError "missing strict bit operation"
      let mut callbackTy := strictInfo.type
      for _ in [:i] do callbackTy := callbackTy.bindingBody!
      let .forallE _ callback _ _ := callbackTy | throw <| IO.userError "invalid strict callback type"
      unless callback == InitKernelPort.translate InitKernelPort.portName dom && a.ty == .object && b.ty == .object do
        throw <| IO.userError "strict callback uses an incompatible representation"
      for (name, tag) in [(`Bool.false, 0), (`Bool.true, 1)] do
        let some l := ctorLayoutExt.find? strict name | throw <| IO.userError s!"missing boolean layout: {name}"
        unless l.ctorInfo.cidx == tag && l.fieldInfo.isEmpty do throw <| IO.userError s!"invalid boolean layout: {name}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if !a.borrow && b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
    if official == `BitVec.ofBoolListLE || official == `BitVec.ofBoolListBE then
      let some strictInfo := strict.find? n | throw <| IO.userError "missing strict Boolean list conversion"
      let .forallE _ strictList _ _ := strictInfo.type | throw <| IO.userError "invalid Boolean list conversion"
      let boolean := mkConst `Bool
      unless dom == mkApp (mkConst `List [.zero]) boolean && strictList == mkApp (mkConst `Omega.List [.zero]) boolean &&
          a.ty == .tobject && b.ty == .tobject && a.borrow do throw <| IO.userError "incorrect Boolean list ABI"
      for (env, list) in [(strict, `Omega.List), (source, `List)] do
        let some nil := ctorLayoutExt.find? env (list ++ `nil) | throw <| IO.userError "missing list nil layout"
        let some cons := ctorLayoutExt.find? env (list ++ `cons) | throw <| IO.userError "missing list cons layout"
        let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect list cons fields"
        unless nil.ctorInfo.cidx == 0 && nil.fieldInfo.isEmpty && cons.ctorInfo.cidx == 1 &&
            cons.ctorInfo.size == 2 && cons.ctorInfo.usize == 0 && cons.ctorInfo.ssize == 0 do
          throw <| IO.userError "incorrect Boolean list layout"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
    let dom := dom.consumeMData
    let dom := if dom.isAppOfArity `optParam 2 then dom.getAppArgs[0]! else dom
    let dom := dom.getAppFn.constName
    if let some (w, t) := word? dom then
      layout strict dom
      unless a.ty == t && b.ty == .tobject do throw <| IO.userError s!"wrong word argument at {n} {i}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push s!"lean_{w}_of_nat({arg})"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if let some (f, t) := float? dom then
      checkFloatLayout strict dom
      unless a.ty == t && b.ty == .tobject do throw <| IO.userError s!"wrong float argument at {n} {i}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push s!"omega_{f}_from_nat_bits({arg})"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Unit && a.ty == .tagged && b.ty == .tagged then
      decls := decls.push ("lean_obj_arg " ++ arg)
      args := args.push arg
    else if dom == `List && official == `ByteArray.toList.loop && a.ty == .tobject && b.ty == .tobject then
      checkStrictString strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if b.borrow && !a.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if [`Nat, `Fin, `BitVec].contains dom && a.ty == .tobject && b.ty == .tobject then
      if dom != `Nat then layout strict dom
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if b.borrow && !a.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Lean.Name && a.ty == .tobject && b.ty == .tobject && a.borrow then
      checkStrictString strict
      unless getExportNameFor? source `Lean.Name.mkStr == some `lean_name_mk_string &&
          getExportNameFor? source `Lean.Name.mkNum == some `lean_name_mk_numeral do
        throw <| IO.userError "unexpected pinned name constructors"
      for (name, tag) in [(`Omega.Lean.Name.anonymous, 0), (`Omega.Lean.Name.str, 1), (`Omega.Lean.Name.num, 2)] do
        let some l := ctorLayoutExt.find? strict name | throw <| IO.userError s!"missing strict name layout: {name}"
        let valid := if tag == 0 then l.fieldInfo.isEmpty else
          match l.fieldInfo with | #[.object 0 _, .object 1 _] => true | _ => false
        unless valid && l.ctorInfo.cidx == tag && l.ctorInfo.size == l.fieldInfo.size &&
            l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do throw <| IO.userError s!"invalid strict name layout: {name}"
      hasName := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *name{i} = omega_name_to_lean({arg});\n"
      args := args.push s!"name{i}"
      cleanup := cleanup ++ s!"  lean_dec(name{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `String.Slice && a.ty == .object && b.ty == .object && a.borrow then
      checkStrictString strict
      for (env, ns) in [(source, Name.anonymous), (strict, `Omega)] do
        for pos in [`String.Pos, `String.Pos.Raw] do
          let some (some f) := impureTrivialStructureInfoExt.find? env (ns ++ pos)
            | throw <| IO.userError s!"missing erased slice position {ns ++ pos}"
          unless f.fieldIdx == 0 do throw <| IO.userError s!"incorrect slice offset field {ns ++ pos}"
        let some l := ctorLayoutExt.find? env (ns ++ `String.Slice.mk) | throw <| IO.userError "missing slice layout"
        let #[.object 0 _, .object 1 _, .object 2 _, .erased] := l.fieldInfo | throw <| IO.userError "unexpected slice fields"
        unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 3 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do
          throw <| IO.userError "unexpected slice constructor"
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *slice{i} = omega_slice_to_lean({arg});\n"
      args := args.push s!"slice{i}"
      cleanup := cleanup ++ s!"  lean_dec(slice{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `String.Pos.Raw && a.ty == .tobject && b.ty == .tobject &&
        (a.borrow || target == "lean_string_get_byte_fast") then
      for (env, pos) in [(source, `String.Pos.Raw), (strict, `Omega.String.Pos.Raw)] do
        let some (some f) := impureTrivialStructureInfoExt.find? env pos | throw <| IO.userError s!"missing position {pos}"
        unless f.fieldIdx == 0 do throw <| IO.userError s!"invalid offset field in {pos}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if [`String, `ByteArray].contains dom && a.ty == .object && b.ty == .tobject then
      checkStrictString strict
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      let convert := if dom == `String then "omega_string_to_lean" else "omega_bytes_to_lean"
      prepare := prepare ++ s!"  lean_object *string{i} = {convert}({arg});\n"
      args := args.push s!"string{i}"
      -- The byte reader's public C primitive borrows both inputs, also for its deprecated alias.
      if a.borrow || target == "lean_string_get_byte_fast" then cleanup := cleanup ++ s!"  lean_dec(string{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Int && a.ty == .tobject && b.ty == .object && a.borrow then
      checkIntLayout strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *mag{i} = lean_ctor_get({arg}, 0);\n  lean_inc(mag{i});\n"
      prepare := prepare ++ s!"  lean_object *value{i} = lean_obj_tag({arg}) == 0 ? lean_nat_to_int(mag{i}) : lean_int_neg_succ_of_nat(mag{i});\n"
      args := args.push s!"value{i}"
      cleanup := cleanup ++ s!"  lean_dec(value{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Bool && a.ty == .uint8 && b.ty == .uint8 then
      decls := decls.push ("uint8_t " ++ arg)
      args := args.push arg
    else throw <| IO.userError s!"unsupported argument of {n}: {dom}/{a.ty}/{b.ty}"
  let call := target ++ "(" ++ String.intercalate ", " args.toList ++ ")"
  let dom := type.consumeMData.getAppFn.constName
  let mut helper := ""
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
  else if let some (f, t) := float? dom then do
    checkFloatLayout strict dom
    unless ret == t && result == .tobject do throw <| IO.userError s!"incorrect float result at {n}"
    pure ("lean_obj_res", s!"omega_{f}_to_nat_bits({call})")
  else if (float? official.getPrefix).isSome && official == official.getPrefix ++ `frExp then do
    let floatType := official.getPrefix
    unless type == mkApp2 (mkConst `Prod [.zero, .zero]) (mkConst floatType) (mkConst `Int) &&
        ret == .object && result == .object do throw <| IO.userError s!"unexpected fraction/exponent result at {n}"
    checkIntLayout strict
    for (env, ctor) in [(source, `Prod.mk), (strict, `Omega.Prod.mk)] do
      let some l := ctorLayoutExt.find? env ctor | throw <| IO.userError s!"missing {ctor}"
      let #[.object 0 _, .object 1 _] := l.fieldInfo | throw <| IO.userError s!"unexpected fields in {ctor}"
      unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 2 && l.ctorInfo.ssize == 0 && l.ctorInfo.usize == 0 do
        throw <| IO.userError s!"unexpected product layout at {ctor}"
    let width := if floatType == `Float32 then "float32" else "float"
    prepare := prepare ++ s!"  lean_object *parts = {call};\n"
    prepare := prepare ++ s!"  lean_object *bits = omega_{width}_to_nat_bits(lean_unbox_{width}(lean_ctor_get(parts, 0)));\n"
    prepare := prepare ++ "  lean_object *exponent = lean_ctor_get(parts, 1);\n  uint8_t neg = lean_int_lt(exponent, lean_box(0));\n"
    prepare := prepare ++ "  lean_object *mag = lean_nat_abs(exponent);\n  if (neg) { lean_object *pred = lean_nat_pred(mag); lean_dec(mag); mag = pred; }\n"
    prepare := prepare ++ "  lean_object *integer = lean_alloc_ctor(neg, 1, 0);\n  lean_ctor_set(integer, 0, mag);\n"
    prepare := prepare ++ "  lean_object *pair = lean_alloc_ctor(0, 2, 0);\n  lean_ctor_set(pair, 0, bits);\n  lean_ctor_set(pair, 1, integer);\n  lean_dec(parts);\n"
    pure ("lean_obj_res", "pair")
  else if dom == `Subtype && official == `System.Platform.getNumBits then do
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Subtype
      | throw <| IO.userError "missing platform width subtype layout"
    unless field.fieldIdx == 0 && ret == .tobject && result == .tobject do
      throw <| IO.userError "invalid platform width result ABI"
    pure ("lean_obj_res", call)
  else if official == `BitVec.instToString && dom == `ToString then do
    checkStrictString strict
    layout strict `BitVec
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.ToString
      | throw <| IO.userError "missing ToString dictionary representation"
    unless field.fieldIdx == 0 && ret == .object && result == .object do throw <| IO.userError "incorrect ToString dictionary ABI"
    hasString := true
    helper := "\nstatic lean_obj_res omega_bitvec_to_string(lean_obj_arg render, lean_obj_arg vector) {\n" ++
      "  lean_object *native = lean_apply_1(render, vector);\n  lean_object *bytes = omega_string_from_lean(native);\n" ++
      "  lean_dec(native);\n  return bytes;\n}\n"
    prepare := prepare ++ "  lean_object *closure = lean_alloc_closure((void *)omega_bitvec_to_string, 2, 1);\n"
    prepare := prepare ++ s!"  lean_closure_set(closure, 0, {call});\n"
    pure ("lean_obj_res", "closure")
  else if [`String, `ByteArray].contains dom then do
    checkStrictString strict
    unless ret == .object && result == .tobject do throw <| IO.userError s!"incorrect string result at {n}"
    prepare := prepare ++ s!"  lean_object *native_string = {call};\n"
    cleanup := cleanup ++ "  lean_dec(native_string);\n"
    let value := if dom == `String then "omega_string_from_lean(native_string)" else
      "omega_bytes_from_data(lean_sarray_cptr(native_string), lean_sarray_size(native_string))"
    pure ("lean_obj_res", value)
  else if dom == `List && official == `ByteArray.toList.loop && ret == .tobject && result == .tobject then do
    checkStrictString strict
    pure ("lean_obj_res", call)
  else if dom == `Option && [`ByteArray.findIdx?.loop, `ByteArray.findFinIdx?.loop].contains official &&
      ret == .tobject && result == .tobject then do
    layout strict `Fin
    for (env, opt) in [(source, `Option), (strict, `Omega.Option)] do
      let some nil := ctorLayoutExt.find? env (opt ++ `none) | throw <| IO.userError "missing optional index layout"
      let some val := ctorLayoutExt.find? env (opt ++ `some) | throw <| IO.userError "missing optional index layout"
      let #[.object 0 _] := val.fieldInfo | throw <| IO.userError "incorrect optional index layout"
      unless nil.ctorInfo.cidx == 0 && nil.fieldInfo.isEmpty && val.ctorInfo.cidx == 1 && val.ctorInfo.size == 1 do
        throw <| IO.userError "incorrect optional index constructor"
    pure ("lean_obj_res", call)
  else if dom == `BitVec && ret == .tobject && result == .tobject then do
    layout strict dom
    pure ("lean_obj_res", call)
  else if dom == `Nat && (ret == .tobject || ret == .tagged) && result == .tobject then pure ("lean_obj_res", call)
  else if dom == `Ordering && ret == .uint8 && result == .uint8 then do
    IndexedNative.checkDataTypes source strict [`Ordering]
    pure ("uint8_t", call)
  else if [`Bool, `Decidable].contains dom && ret == .uint8 && result == .uint8 then pure ("uint8_t", call)
  else throw <| IO.userError s!"unsupported result of {n}: {dom}/{ret}/{result}"
  let proto ← if usesPinnedFunction official then do
    let ctype (t : IR.IRType) : IO String := match t with
      | .uint8 => pure "uint8_t"
      | .uint16 => pure "uint16_t"
      | .uint32 => pure "uint32_t"
      | .uint64 => pure "uint64_t"
      | .usize => pure "size_t"
      | .object | .tobject | .tagged => pure "lean_object *"
      | _ => throw <| IO.userError s!"unexpected C type at {official}: {t}"
    let inputs ← (params.filter (·.ty != .erased)).mapM fun p => ctype p.ty
    pure s!"\nextern {← ctype ret} {target}({String.intercalate ", " inputs.toList});\n"
  else if (float? official.getPrefix).isSome || (float? dom).isSome then do
    let header := "\n#include \"float_bits.h\"\n"
    if target.startsWith "lean_" then pure header else
      let ty := if ret == .float then "double" else "float"
      unless (ret == .float || ret == .float32) && params.all (·.ty == ret) do
        throw <| IO.userError s!"unexpected math library signature {target}"
      pure <| header ++ s!"extern {ty} {target}({String.intercalate ", " (List.replicate params.size ty)});\n"
  else if [`System.Platform.getIsWindows, `System.Platform.getIsOSX, `System.Platform.getIsLinux,
      `System.Platform.getIsEmscripten, `System.Platform.Internal.getHardwareConcurrency].contains official then
    let t := if ret == .uint8 then "uint8_t" else "uint32_t"
    pure s!"\nextern {t} {target}(lean_obj_arg);\n"
  else if official == `ByteArray.copySlice then
    pure "\nextern lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);\n"
  else if official == `System.Platform.getNumBits then
    pure "\nextern lean_obj_res lean_system_platform_nbits(lean_obj_arg);\n" else pure ""
  let header := if hasName then "\n#include \"strict_name.h\"\n" else if hasString || [`String, `ByteArray].contains dom then "\n#include \"strict_string.h\"\n" else ""
  return header ++ proto ++ helper ++ s!"\nLEAN_EXPORT {output} {adapter}({String.intercalate ", " decls.toList}) \{\n{prepare}  {output} r = {value};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.WordNative

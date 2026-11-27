module

public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.MacroNative
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
  | `Char | `Int32 => `UInt32
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

private def defsStringFunction (n : Name) : Bool :=
  [`String.intercalate, `String.Internal.intercalateImpl, `String.pushn, `String.Internal.pushnImpl,
   `String.Slice.getUTF8Byte, `String.Slice.getUTF8Byte!, `String.Slice.Pos.byte].contains n

private def basicStringFunction (n : Name) : Bool :=
  let method := n.updatePrefix .anonymous
  (n.getPrefix == `String && [`fromUTF8!, `pos?, `pos!, `substrEq, `replaceStartEnd!, `slice!].contains method) ||
    (n.getPrefix == `String.Pos && [`get!, `byte, `next!, `next?, `nextn, `ofSlice!, `slice!, `sliceOrPanic].contains method) ||
    (n.getPrefix == `String.Slice && [`pos!, `pos?, `replaceStartEnd!, `slice!].contains method) ||
    (n.getPrefix == `String.Slice.Pos && [`get!, `next, `next?, `next!, `nextFast, `nextn, `prevAux, `ofSlice!,
      `slice!, `sliceOrPanic].contains method) ||
    ([`String, `String.Pos.Raw].contains n.getPrefix && [`utf8GetAux, `utf8GetAux?, `utf8SetAux, `utf8PrevAux].contains method) ||
    [`String.Pos.Raw.extract.go₁, `String.Pos.Raw.extract.go₂, `ByteArray.utf8Decode?, `ByteArray.utf8Decode?.go,
     `String.Internal.toArray, `String.Slice.Pos.prevAux.go, `String.instDecidableIsValidForSlice, `String.Pos.Raw.isValidForSlice,
     `String.Pos.Raw.substrEq, `ByteArray.validateUTF8.go].contains n

private def decodeStringFunction (n : Name) : Bool :=
  (n.getPrefix == `ByteArray.utf8DecodeChar? && [`parseFirstByte, `isInvalidContinuationByte, `verify₂, `verify₃,
    `verify₄, `assemble₂, `assemble₃, `assemble₄, `assemble₂Unchecked, `assemble₃Unchecked,
    `assemble₄Unchecked].contains (n.updatePrefix .anonymous)) ||
    [`UInt8.instDecidableIsUTF8FirstByte, `UInt8.utf8ByteSize, `String.utf8EncodeCharFast,
     `ByteArray.validateUTF8At, `ByteArray.utf8DecodeChar, `ByteArray.utf8DecodeChar?].contains n

private def sliceStringFunction (n : Name) : Bool :=
  n == `String.Slice.lines.lineMap || (n.getPrefix == `String.Slice &&
    [`trimAsciiStart, `trimAsciiEnd, `trimAscii, `intercalate, `isInt, `toInt?, `toInt!, `toName].contains (n.updatePrefix .anonymous))

private def renderName (n : Name) : Bool := [`Lean.Name.escapePart, `Lean.Name.toStringWithSep, `Lean.Name.toStringWithToken].contains n

private def metaLiteralFunction (n : Name) : Bool :=
  n == `Substring.Raw.toName || (n.getPrefix == `Lean.Syntax &&
    [`decodeNatLitVal?, `decodeScientificLitVal?, `decodeNameLit, `decodeStrLit, `decodeStrLitAux,
     `decodeRawStrLitAux, `splitNameLit].contains (n.updatePrefix .anonymous))

private def monadicSeparator (n : Name) : Bool :=
  [`Array.mapSepElemsM, `Array.filterSepElemsM].contains n

private def syntaxTreeFunction (n : Name) : Bool :=
  [`Lean.instQuoteNameMkStr1._private_1,
   `Lean.TSyntax.Compat.instCoeTailArraySyntaxTSepArray, `Lean.TSyntax.Compat.instCoeTailArraySyntaxTSyntaxArray,
   `Lean.Syntax.instCoeOutTSyntaxArrayArray, `Lean.mkIdent, `Lean.mkIdentFrom, `Lean.mkCIdentFrom, `Lean.HygieneInfo.mkIdent,
   `Lean.TSyntax.getHexNumVal, `Lean.TSyntax.getHexNumSize, `Lean.TSyntax.getDocString,
   `Lean.Parser.Tactic.appendConfig, `Lean.Parser.Tactic.getConfigItems, `Lean.Parser.Tactic.mkOptConfig,
   `Array.mapSepElems, `Array.filterSepElems, `Lean.Syntax.TSepArray.getElems,
   `Lean.Syntax.TSepArray.ofElems].contains n || (n.getPrefix == `Lean.Syntax &&
    [`getHead?, `setHeadInfoAux, `setTailInfoAux, `findAux, `structEq, `isToken, `hasArgs, `isAtom, `isNone,
     `isIdOrAtom?, `isLit?, `isInterpolatedStrLit?, `mkApp, `mkCApp].contains (n.updatePrefix .anonymous))

private def rawFold (n : Name) : Bool := n == `Substring.Raw.foldl || n == `Substring.Raw.foldr

private def rawStringFunction (n : Name) : Bool := rawFold n || [`Substring.Raw.all, `Substring.Raw.toString].contains n

private def pinnedStringFunction (n : Name) : Bool := rawStringFunction n || renderName n || defsStringFunction n || basicStringFunction n || decodeStringFunction n || sliceStringFunction n || metaLiteralFunction n || n == `String.toName

private def debugPrimitive (n : Name) : Bool := [`dbgTrace, `dbgTraceIfShared, `dbgSleep, `dbgStackTrace].contains n

private def digitList (n : Name) : Bool := [`Nat.toSuperDigitsAux, `Nat.toSubDigitsAux].contains n

public def usesPinnedFunction (n : Name) : Bool :=
  let method := n.updatePrefix .anonymous
  let trailing := n == `Int.trailingZeros || n == `Int.trailingZeros.aux
  let bytes := [`ByteArray.toUInt64LE!, `ByteArray.toUInt64BE!, `ByteArray.toList.loop, `ByteArray.findIdx?.loop, `ByteArray.findFinIdx?.loop].contains n
  let vector := n.getPrefix == `BitVec &&
    [`abs, `pow, `smod, `replicate, `reverse, `cpop, `cpopNatRec, `ctz, `clz, `clzAuxRec,
     `getLsbD, `getLsb, `getMsbD, `getMsb, `msb, `sdiv, `srem, `smtSDiv, `hash, `ofBoolListLE, `ofBoolListBE].contains method
  MacroNative.supported n || digitList n || trailing || monadicSeparator n || syntaxTreeFunction n || pinnedStringFunction n || modelOperation n || ByteFoldNative.supported n || IndexedNative.supported n || SyntaxPositionNative.supported n || bytes || vector || [`Nat.repr, `Nat.reprFast, `Int.repr].contains n || [`BitVec.toHex, `BitVec.instToString].contains n || n == `Nat.bitwise || ((word? n.getPrefix).isSome && (method == `pow || (method == `ofInt && bitsType n.getPrefix == n.getPrefix))) ||
    (n.getPrefix == `Int && [`negOfNat, `subNatNat, `sign, `toNat, `pow, `fdiv, `fmod, `bdiv, `bmod].contains method)

private def bootstrapStringOp (n : Name) : Bool :=
  (n.getPrefix == `String.Internal && [`length, `append, `posOf, `offsetOfPos, `pushn, `next, `isEmpty,
    `isPrefixOf, `contains, `get, `capitalize, `atEnd, `trim, `front, `drop, `dropRight, `getUTF8Byte,
    `ugetUTF8Byte, `any, `nextWhile, `intercalate, `foldl].contains (n.updatePrefix .anonymous)) ||
    (n.getPrefix == `Substring.Raw.Internal && [`toString, `drop, `front, `takeWhile, `extract, `all, `beq,
      `isEmpty, `get, `prev].contains (n.updatePrefix .anonymous)) ||
    [`String.Pos.Raw.Internal.min, `String.Pos.Raw.Internal.sub].contains n

private def basicStringExtern (n : Name) : Bool :=
  ([`String.Pos.Raw, `String].contains n.getPrefix &&
    [`get?, `get!, `get', `next', `extract].contains (n.updatePrefix .anonymous)) ||
    [`String.decodeChar, `String.Pos.next].contains n

/-- The bootstrap externs implemented in Lean are exported by the pinned string library. -/
public def usesStringExport (n : Name) : Bool :=
  bootstrapStringOp n && ![`String.Internal.next, `String.Internal.get, `String.Internal.atEnd,
    `String.Internal.getUTF8Byte, `String.Internal.ugetUTF8Byte, `String.Internal.length, `String.Internal.append].contains n

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
  let version := owner == `OmegaInit.Meta.Defs && [`Lean.getGithash, `Lean.version.getIsRelease,
    `Lean.version.getSpecialDesc, `Lean.Internal.isStage0, `Lean.Internal.hasLLVMBackend].contains name
  let modular := (owner == `OmegaInit.Data.Nat.Gcd && name == `Nat.gcd) ||
    (owner == `OmegaInit.Data.Nat.Div.Basic && name == `Nat.divExact) ||
    (owner == `OmegaInit.Data.Nat.PowMod && name == `Nat.powMod)
  let stringOp := (owner == `OmegaInit.Data.String.Bootstrap && bootstrapStringOp name) ||
    (owner == `OmegaInit.Data.String.Basic && basicStringExtern name) ||
    (owner == `OmegaInit.Data.String.Length && name == `String.length)
  let textCompare := (owner == `OmegaInit.Data.String.PosRaw && [`String.getUTF8Byte, `String.getUtf8Byte].contains name) ||
    (owner == `OmegaInit.Data.Ord.String && name == `String.compare) ||
    (owner == `OmegaInit.Data.String.Slice && [`String.Slice.hash, `String.Slice.instDecidableLt].contains name) ||
    (owner == `OmegaInit.Data.String.Pattern.Basic && name == `String.Slice.Pattern.Internal.memcmpStr)
  let intPrimitive := intOwner && name.getPrefix == `Int &&
    [`neg, `add, `sub, `mul, `decEq, `decLe, `decLt, `decNonneg, `natAbs, `ediv, `emod, `tdiv, `tmod, `divExact].contains method
  let primitive := ((word? name.getPrefix).isSome && name.getPrefix != `Char && (ops ++ widths).contains method) ||
    (name.getPrefix == `Bool && widths.contains method)
  (owner == `OmegaInit.Util && debugPrimitive name && isExtern source name) ||
    (owner == `OmegaInit.Data.ToString.Name && renderName name) ||
    (owner == `OmegaInit.Data.String.Substring && rawStringFunction name) ||
    (owner == `OmegaInit.Data.String.Defs && defsStringFunction name) ||
    (owner == `OmegaInit.Data.String.Basic && basicStringFunction name) ||
    (owner == `OmegaInit.Data.String.Decode && decodeStringFunction name) ||
    (owner == `OmegaInit.Data.String.Slice && sliceStringFunction name) ||
    (owner == `OmegaInit.Meta.Defs && (name == `String.toName || metaLiteralFunction name || syntaxTreeFunction name || monadicSeparator name)) || isFloatCall source owner name ||
    (owner == `OmegaInit.Prelude && MacroNative.supported name) ||
    (owner == `OmegaInit.Data.ByteArray.Basic && ByteFoldNative.supported name) ||
    ([`OmegaInit.Grind.Ring.CommSolver, `OmegaInit.Data.Nat.Basic, `OmegaInit.Data.Nat.Div.Basic, `OmegaInit.Data.Nat.Lemmas,
    `OmegaInit.Data.RArray, `OmegaInit.Data.Nat.Internal.Linear, `OmegaInit.Data.Nat.Fold, `OmegaInit.Data.Fin.Lemmas].contains owner && IndexedNative.supported name) ||
    ([`OmegaInit.Data.Float.Model.Float, `OmegaInit.Data.Float.Model.Float32].contains owner && modelOperation name) ||
    ([`OmegaInit.Prelude, `OmegaInit.Meta.Defs].contains owner && SyntaxPositionNative.supported name) ||
    ((base || intPrimitive || platform || version || byteOp || textCompare || modular || stringOp || wordRepr || bitwise || logarithm || (inOwner && primitive)) && isExtern source name) ||
    ((intOwner || [`OmegaInit.Data.Dyadic.Basic, `OmegaInit.Data.ByteArray.Extra, `OmegaInit.Data.ByteArray.Basic, `OmegaInit.Data.Int.Repr, `OmegaInit.Data.Repr, `OmegaInit.Data.Nat.Bitwise.Basic, `OmegaInit.Data.BitVec.Basic].contains owner || [`OmegaInit.Data.UInt.Basic, `OmegaInit.Data.SInt.Basic].contains owner) && usesPinnedFunction name)

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

private def checkNameLayout (source strict : Environment) : IO Unit := do
  checkStrictString strict
  unless getExportNameFor? source `Lean.Name.mkStr == some `lean_name_mk_string &&
      getExportNameFor? source `Lean.Name.mkNum == some `lean_name_mk_numeral do
    throw <| IO.userError "unexpected pinned name constructors"
  for (env, root) in [(source, `Lean.Name), (strict, `Omega.Lean.Name)] do
    for (ctor, tag) in [(`anonymous, 0), (`str, 1), (`num, 2)] do
      let name := root ++ ctor
      let some l := ctorLayoutExt.find? env name | throw <| IO.userError s!"missing name layout {name}"
      let valid := if tag == 0 then l.fieldInfo.isEmpty else
        match l.fieldInfo with | #[.object 0 _, .object 1 _] => true | _ => false
      unless valid && l.ctorInfo.cidx == tag && l.ctorInfo.size == l.fieldInfo.size &&
          l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do throw <| IO.userError s!"invalid name layout: {name}"

private def checkSliceLayout (source strict : Environment) : IO Unit := do
  for (env, ns) in [(source, Name.anonymous), (strict, `Omega)] do
    for pos in [`String.Pos, `String.Pos.Raw] do
      let some (some f) := impureTrivialStructureInfoExt.find? env (ns ++ pos)
        | throw <| IO.userError s!"missing erased slice position {ns ++ pos}"
      unless f.fieldIdx == 0 do throw <| IO.userError s!"incorrect slice offset field {ns ++ pos}"
    let some l := ctorLayoutExt.find? env (ns ++ `String.Slice.mk) | throw <| IO.userError "missing slice layout"
    let #[.object 0 _, .object 1 _, .object 2 _, .erased] := l.fieldInfo | throw <| IO.userError "unexpected slice fields"
    unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 3 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do
      throw <| IO.userError "unexpected slice constructor"

/-- Preserve the callback's effects while converting the terminal array underneath arbitrary monads. -/
private def separatorWrapper (source strict : Environment) (n official : Name) : IO String := do
  let some src := source.find? official | throw <| IO.userError s!"missing separator operation {official}"
  let some dst := strict.find? n | throw <| IO.userError s!"missing strict separator operation {n}"
  unless dst.type == InitKernelPort.translate InitKernelPort.portName src.type do throw <| IO.userError "different separator types"
  let some (.fdecl _ params .tobject ..) := IR.findEnvDecl source official | throw <| IO.userError "missing pinned separator IR"
  let some (.extern _ actual .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError "missing strict separator IR"
  unless entry == symbol n && params.map (fun p => (p.ty, p.borrow)) ==
      #[(.erased, false), (.object, false), (.object, false), (.tobject, false)] &&
      actual.map (·.ty) == #[.erased, .object, .tobject, .tobject] do
    throw <| IO.userError s!"unexpected separator ABI {n}: {actual.map (·.ty)}"
  IndexedNative.checkDataTypes source strict [`Monad, `Applicative, `Pure, `Functor, `Seq, `SeqLeft, `SeqRight, `Bind]
  for (ctor, names) in [(`Monad.mk, [`toApplicative, `toBind]), (`Applicative.mk, [`toFunctor, `toPure, `toSeq, `toSeqLeft, `toSeqRight])] do
    let some layout := ctorLayoutExt.find? source ctor | throw <| IO.userError s!"missing separator dictionary {ctor}"
    unless layout.ctorInfo.size == names.length && layout.ctorInfo.cidx == 0 && layout.ctorInfo.ssize == 0 &&
        layout.ctorInfo.usize == 0 do throw <| IO.userError s!"unexpected separator dictionary {ctor}"
    for field in names, i in [:names.length] do
      let some projection := source.getProjectionFnInfo? (ctor.getPrefix ++ field)
        | throw <| IO.userError s!"missing separator projection {field}"
      let .object j _ := layout.fieldInfo[i]! | throw <| IO.userError "separator dictionary field is unboxed"
      unless projection.i == i && j == i do throw <| IO.userError s!"reordered separator dictionary field {field}"
  let target := getSymbolStem source official
  let keep := if actual[2]!.borrow then "lean_inc(values); " else ""
  let keepFn := if actual[3]!.borrow then "lean_inc(callback); " else ""
  let release := if actual[1]!.borrow then "" else "lean_dec(monad); "
  return "\n#include \"sep_array.h\"\n" ++
    s!"extern lean_obj_res {target}(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);\n" ++
    s!"LEAN_EXPORT lean_obj_res {entry}(lean_obj_arg monad, lean_obj_arg values, lean_obj_arg callback) \{\n" ++
    s!"  lean_object *adapted = omega_sep_array_monad(monad);\n  {keep}{keepFn}{release}return {target}(lean_box(0), adapted, lean_array_mk(values), callback);\n}\n"

/-- Check both sides of the call and generate its ownership conversions from their stored IR. -/
public def wrapper (source strict : Environment) (n : Name) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  if MacroNative.supported official then return ← MacroNative.wrapper source strict n (symbol n)
  if monadicSeparator official then return ← separatorWrapper source strict n official
  if ByteFoldNative.supported official then return ← ByteFoldNative.wrapper source strict n (symbol n)
  if IndexedNative.supported official then return ← IndexedNative.wrapper source strict n (symbol n)
  if SyntaxPositionNative.supported official then return ← SyntaxPositionNative.wrapper source strict n (symbol n)
  let some ci := source.find? official | throw <| IO.userError s!"unknown word primitive {official}"
  if bootstrapStringOp official || basicStringExtern official || pinnedStringFunction official || syntaxTreeFunction official then
    let some strictInfo := strict.find? n | throw <| IO.userError s!"missing strict string operation {n}"
    unless strictInfo.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"strict string input type differs at {n}"
    checkStrictString strict
    if official.getPrefix == `Substring.Raw.Internal || rawStringFunction official || [`Substring.Raw.toName, `Lean.Syntax.splitNameLit].contains official then
      for (env, name, text) in [(source, `Substring.Raw.mk, ImpureType.object), (strict, `Omega.Substring.Raw.mk, ImpureType.tobject)] do
        let some fields := ctorLayoutExt.find? env name | throw <| IO.userError s!"missing substring record {name}"
        let #[.object 0 field, .object 1 start, .object 2 stop] := fields.fieldInfo | throw <| IO.userError "invalid substring fields"
        unless field == text && start == ImpureType.tobject && stop == ImpureType.tobject && fields.ctorInfo.cidx == 0 && fields.ctorInfo.size == 3 && fields.ctorInfo.usize == 0 && fields.ctorInfo.ssize == 0 do
          throw <| IO.userError "invalid substring record layout"
  if syntaxTreeFunction official then
    SyntaxPositionNative.checkTreeLayout source strict
    checkNameLayout source strict
  let compiled ← if official == `Nat.repr then do
    unless (Compiler.getImplementedBy? source official) == some `Nat.reprFast do throw <| IO.userError "unexpected Nat.repr implementation"
    let some fast := source.find? `Nat.reprFast | throw <| IO.userError "missing pinned Nat.reprFast"
    unless fast.type == ci.type do throw <| IO.userError "Nat.reprFast type differs from Nat.repr"
    pure `Nat.reprFast
  else pure official
  let some impl := IR.findEnvDecl source compiled | throw <| IO.userError s!"no pinned IR for {official}"
  if debugPrimitive official then
    let some strictInfo := strict.find? n | throw <| IO.userError s!"missing strict debug operation {n}"
    unless strictInfo.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"different debug operation type at {n}"
  if digitList official then
    let some targetInfo := strict.find? n | throw <| IO.userError s!"missing strict character conversion {n}"
    unless targetInfo.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"character conversion type mismatch {n}"
    IndexedNative.checkDataTypes source strict [`List]
    let some (some f) := impureTrivialStructureInfoExt.find? strict `Omega.Char | throw <| IO.userError "missing strict character"
    unless f.fieldIdx == 0 do throw <| IO.userError "invalid strict character"
    layout strict `UInt32
  let params := impl.params
  let ret := impl.resultType
  let target ← match impl with
    | .extern _ _ _ ⟨[.standard `all entry]⟩ => do
      if official == `Lean.getGithash then
        -- The standalone runtime exports the primitive. The shared Lean library exports its boxed entry.
        let boxed := mkBoxedName official
        let some (.fdecl _ args .object ..) := IR.findEnvDecl source boxed
          | throw <| IO.userError "missing boxed git revision getter"
        unless args.map (·.ty) == #[.tagged] && entry == "lean_get_githash" do
          throw <| IO.userError "unexpected git revision getter ABI"
        pure (getSymbolStem source boxed)
      else pure entry
    | .fdecl .. =>
      unless usesPinnedFunction official do
        throw <| IO.userError s!"unexpected compiled word function {official}"
      if let some exported := getExportNameFor? source compiled then
        unless ([ (`String.Internal.pushnImpl, `lean_string_pushn),
                  (`String.Internal.intercalateImpl, `lean_string_intercalate) ] : List (Name × Name)).contains (official, exported) do
          throw <| IO.userError s!"unexpected exported symbol {exported} for {official}"
        pure exported.toString
      else pure (getSymbolStem source compiled)
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
  let passesErased := pinnedStringFunction official || official == `Int.trailingZeros.aux
  for (a, b) in params.zip actual, i in [:params.size] do
    let .forallE _ dom body _ := type | throw <| IO.userError s!"expected argument {i} of {n}"
    type := body
    if a.ty == .erased && b.ty == .erased then
      if passesErased then args := args.push "lean_box(0)"
      continue
    let arg := "a" ++ toString i
    let plainDom := if dom.isAppOfArity `optParam 2 then dom.getAppArgs[0]! else dom
    if renderName official && plainDom.isForall then
      unless plainDom.bindingDomain! == mkConst `String && plainDom.bindingBody! == mkConst `Bool &&
          a.ty == .object && b.ty == .object && !a.borrow do throw <| IO.userError "invalid name token predicate"
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      prepare := prepare ++ s!"  lean_object *token = lean_alloc_closure((void *)omega_name_token, 2, 1);\n  lean_closure_set(token, 0, {arg});\n"
      args := args.push "token"
      continue
    if rawFold official && dom.isForall then
      let left := official == `Substring.Raw.foldl
      let first := if left then mkBVar 0 else mkConst `Char
      let second := if left then mkConst `Char else mkBVar 1
      unless dom.bindingDomain! == first && dom.bindingBody!.isForall &&
          dom.bindingBody!.bindingDomain! == second && dom.bindingBody!.bindingBody! == mkBVar 2 &&
          a.ty == .tobject && (b.ty == .tobject || b.ty == .object) && !a.borrow do
        throw <| IO.userError s!"invalid raw substring fold callback {n}"
      layout strict `Char
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      let step := if left then "omega_raw_fold_left" else "omega_raw_fold_right"
      prepare := prepare ++ s!"  lean_object *step = lean_alloc_closure((void *){step}, 3, 1);\n  lean_closure_set(step, 0, {arg});\n"
      args := args.push "step"
      continue
    if (debugPrimitive official || rawFold official) && (dom.isForall || dom.isBVar) then
      -- The runtime either returns the polymorphic payload or invokes its continuation with Unit.unit.
      let payload := (official == `dbgTraceIfShared || rawFold official) && dom == .bvar (i - 1)
      let thunk := dom.isForall && dom.bindingDomain! == mkConst `Unit && dom.bindingBody! == .bvar i
      unless (payload || thunk) && a.ty == .tobject && (b.ty == .tobject || b.ty == .object) && !a.borrow do
        throw <| IO.userError s!"different debug continuation or payload ABI at {n}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      args := args.push arg
      continue
    if syntaxTreeFunction official && dom.isForall then
      let map := official == `Array.mapSepElems
      unless (map || [`Lean.Syntax.findAux, `Array.filterSepElems].contains official) &&
          dom.bindingDomain! == mkConst `Lean.Syntax && dom.bindingBody! == mkConst (if map then `Lean.Syntax else `Bool) && a.ty == .object && b.ty == .object && !a.borrow do
        throw <| IO.userError s!"incorrect syntax predicate signature {n}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      let adapter := if map then "omega_syntax_map" else "omega_syntax_predicate"
      prepare := prepare ++ s!"  lean_object *predicate = lean_alloc_closure((void *){adapter}, 2, 1);\n  lean_closure_set(predicate, 0, {arg});\n"
      args := args.push "predicate"
      continue
    if (bootstrapStringOp official || official == `Substring.Raw.all) && dom.isForall then
      let arrow := fun (a b : Expr) => Expr.forallE .anonymous a b .default
      let unary := arrow (mkConst `Char) (mkConst `Bool)
      let binary := arrow (mkConst `String) (arrow (mkConst `Char) (mkConst `String))
      let fold := dom == binary && official == `String.Internal.foldl
      unless (fold || dom == unary) && a.ty == .object && b.ty == .object && !a.borrow do
        throw <| IO.userError s!"invalid pinned string callback {n}"
      layout strict `Char
      IndexedNative.checkDataTypes source strict [`Bool]
      hasString := true
      let f := if fold then "omega_string_fold_step" else "omega_string_predicate"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      prepare := prepare ++ s!"  lean_object *cb{i} = lean_alloc_closure((void *){f}, {if fold then 3 else 2}, 1);\n  lean_closure_set(cb{i}, 0, {arg});\n"
      args := args.push s!"cb{i}"
      continue
    if [`String.Internal.intercalate, `String.intercalate, `String.Internal.intercalateImpl, `String.Slice.intercalate].contains official &&
        dom.getAppFn.constName == `List then
      let slice := official == `String.Slice.intercalate
      let elem := if slice then `String.Slice else `String
      unless dom == mkApp (mkConst `List [.zero]) (mkConst elem) && a.ty == .tobject && b.ty == .tobject do
        throw <| IO.userError "invalid list of strings ABI"
      if slice then checkSliceLayout source strict
      IndexedNative.checkDataTypes source strict [`List]
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      let convert := if slice then s!"omega_map_list({arg}, omega_slice_to_lean)" else s!"omega_string_list_to_lean({arg})"
      prepare := prepare ++ s!"  lean_object *texts = {convert};\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      if a.borrow then cleanup := cleanup ++ "  lean_dec(texts);\n"
      args := args.push "texts"
      continue
    let charSeq := fun (t : Name) => mkApp (mkConst t [.zero]) (mkConst `Char)
    if basicStringFunction official && (dom == charSeq `List || dom == charSeq `Array) then
      let array := dom == charSeq `Array
      unless a.ty == (if array then .object else .tobject) && b.ty == .tobject do throw <| IO.userError s!"incorrect character sequence ABI at {n}"
      layout strict `Char
      IndexedNative.checkDataTypes source strict [`List]
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      let conversion := if array then s!"omega_char_array_to_lean({arg})" else s!"omega_map_list({arg}, omega_char_to_lean)"
      prepare := prepare ++ s!"  lean_object *chars{i} = {conversion};\n"
      args := args.push s!"chars{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(chars{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
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
    let syntaxArray := dom.getAppFn.constName == `Array &&
      [`Lean.Syntax, `Lean.TSyntax].contains (dom.getArg! 0).getAppFn.constName
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
    else if dom == `List && digitList official && a.ty == .tobject && b.ty == .tobject then
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *chars{i} = omega_convert_char_list({arg}, true);\n"
      args := args.push s!"chars{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(chars{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `List && official == `ByteArray.toList.loop && a.ty == .tobject && b.ty == .tobject then
      checkStrictString strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if b.borrow && !a.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if [`Nat, `Fin, `BitVec, `String.Pos.Raw, `String.Pos, `String.Slice.Pos].contains dom && a.ty == .tobject && b.ty == .tobject then
      if [`String.Pos.Raw, `String.Pos, `String.Slice.Pos].contains dom then
        for (env, pos) in [(source, dom), (strict, `Omega ++ dom)] do
          let some (some field) := impureTrivialStructureInfoExt.find? env pos | throw <| IO.userError s!"missing position {pos}"
          unless field.fieldIdx == 0 do throw <| IO.userError s!"invalid offset field in {pos}"
      else if dom != `Nat then layout strict dom
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      let borrowed := a.borrow || target == "lean_string_get_byte_fast"
      if b.borrow && !borrowed then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if borrowed && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if syntaxTreeFunction official && (syntaxArray || [`Lean.TSyntaxArray, `Lean.Syntax.TSepArray].contains dom) &&
        a.ty == .object && b.ty == .tobject then
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *syntax_array{i} = omega_syntax_array_to_lean({arg});\n"
      args := args.push s!"syntax_array{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(syntax_array{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if syntaxTreeFunction official && dom == `Lean.SyntaxNodeKinds && a.ty == .tobject && b.ty == .tobject then
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *kinds{i} = omega_map_list({arg}, omega_name_to_lean);\n"
      args := args.push s!"kinds{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(kinds{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if syntaxTreeFunction official && [`Lean.Syntax, `Lean.TSyntax, `Lean.Syntax.Term, `Lean.Syntax.HexNum,
        `Lean.Syntax.HygieneInfo, `Lean.SourceInfo, `Lean.SyntaxNodeKind].contains dom &&
        a.ty == .tobject && b.ty == .tobject then
      let convert := if dom == `Lean.SourceInfo then s!"omega_convert_source_info({arg}, true)" else
        if dom == `Lean.SyntaxNodeKind then s!"omega_name_to_lean({arg})" else s!"omega_convert_syntax({arg}, true)"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *input{i} = {convert};\n"
      args := args.push s!"input{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(input{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Lean.Name && a.ty == .tobject && b.ty == .tobject then
      checkNameLayout source strict
      hasName := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *name{i} = omega_name_to_lean({arg});\n"
      args := args.push s!"name{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(name{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `String.Slice && a.ty == .object && b.ty == .object then
      checkStrictString strict
      checkSliceLayout source strict
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *slice{i} = omega_slice_to_lean({arg});\n"
      args := args.push s!"slice{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(slice{i});\n"
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
    else if dom == `Substring.Raw && a.ty == .object && b.ty == .object then
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *slice{i} = omega_convert_substring({arg}, omega_string_to_lean);\n"
      args := args.push s!"slice{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(slice{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Int && a.ty == .tobject && b.ty == .object then
      checkIntLayout strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *mag{i} = lean_ctor_get({arg}, 0);\n  lean_inc(mag{i});\n"
      prepare := prepare ++ s!"  lean_object *value{i} = lean_obj_tag({arg}) == 0 ? lean_nat_to_int(mag{i}) : lean_int_neg_succ_of_nat(mag{i});\n"
      args := args.push s!"value{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(value{i});\n"
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
  else if dom == `Lean.Name && ret == .tobject && result == .tobject then do
    checkNameLayout source strict
    hasName := true
    prepare := prepare ++ s!"  lean_object *name = {call};\n"
    cleanup := cleanup ++ "  lean_dec(name);\n"
    pure ("lean_obj_res", "omega_name_from_lean(name)")
  else if dom == `Int then do
    checkIntLayout strict
    unless (ret == .tobject || ret == .tagged) && result == .object do throw <| IO.userError s!"incorrect integer result at {n}"
    prepare := prepare ++ s!"  lean_object *integer = {call};\n"
    cleanup := cleanup ++ "  lean_dec(integer);\n"
    pure ("lean_obj_res", "omega_int_from_lean(integer)")
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
  else if [`Substring.Raw, `String.Slice].contains dom && ret == .object && result == .object then do
    if dom == `String.Slice then checkSliceLayout source strict
    hasString := true
    prepare := prepare ++ s!"  lean_object *native_slice = {call};\n"
    cleanup := cleanup ++ "  lean_dec(native_slice);\n"
    pure ("lean_obj_res", "omega_convert_substring(native_slice, omega_string_from_lean)")
  else if [`String, `ByteArray].contains dom then do
    checkStrictString strict
    unless ret == .object && result == .tobject do throw <| IO.userError s!"incorrect string result at {n}"
    prepare := prepare ++ s!"  lean_object *native_string = {call};\n"
    cleanup := cleanup ++ "  lean_dec(native_string);\n"
    let value := if dom == `String then "omega_string_from_lean(native_string)" else
      "omega_bytes_from_data(lean_sarray_cptr(native_string), lean_sarray_size(native_string))"
    pure ("lean_obj_res", value)
  else if dom == `List && digitList official && ret == .tobject && result == .tobject then do
    prepare := prepare ++ s!"  lean_object *digits = {call};\n"
    cleanup := cleanup ++ "  lean_dec(digits);\n"
    pure ("lean_obj_res", "omega_convert_char_list(digits, false)")
  else if dom == `List && official == `ByteArray.toList.loop && ret == .tobject && result == .tobject then do
    checkStrictString strict
    pure ("lean_obj_res", call)
  else if official == `String.utf8EncodeCharFast then do
    unless type == mkApp (mkConst `List [.zero]) (mkConst `UInt8) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect UTF-8 byte list ABI"
    layout strict `UInt8
    IndexedNative.checkDataTypes source strict [`List]
    -- A boxed UInt8 and a native Nat below 256 have the same tagged scalar representation.
    pure ("lean_obj_res", call)
  else if dom == `ByteArray.utf8DecodeChar?.FirstByte && ret == .uint8 && result == .uint8 then do
    IndexedNative.checkDataTypes source strict [dom]
    pure ("uint8_t", call)
  else if basicStringFunction official && [`Array, `List].contains dom then do
    let array := dom == `Array
    unless type == mkApp (mkConst dom [.zero]) (mkConst `Char) && ret == (if array then .object else .tobject) && result == .tobject do
      throw <| IO.userError s!"incorrect character sequence result at {n}"
    layout strict `Char
    IndexedNative.checkDataTypes source strict [`List]
    hasString := true
    prepare := prepare ++ s!"  lean_object *chars = {call};\n"
    cleanup := cleanup ++ "  lean_dec(chars);\n"
    pure ("lean_obj_res", if array then "omega_char_array_from_lean(chars)" else "omega_map_list(chars, omega_char_from_lean)")
  else if dom == `Option && (basicStringFunction official || basicStringExtern official || decodeStringFunction official) &&
      [`Char, `Array].contains (type.getArg! 0).getAppFn.constName then do
    let payload := type.getArg! 0
    let scalar := payload == mkConst `Char
    unless (scalar || payload == mkApp (mkConst `Array [.zero]) (mkConst `Char)) && ret == .tobject && result == .tobject do
      throw <| IO.userError s!"incorrect optional character ABI at {n}"
    layout strict `Char
    IndexedNative.checkDataTypes source strict [`Option]
    hasString := true
    prepare := prepare ++ s!"  lean_object *optional = {call};\n"
    pure ("lean_obj_res", "omega_optional_from_lean(optional, " ++ (if scalar then "omega_char_from_lean)" else "omega_char_array_from_lean)"))
  else if official == `Lean.Name.escapePart then do
    unless type == mkApp (mkConst `Option [.zero]) (mkConst `String) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect escaped name result ABI"
    IndexedNative.checkDataTypes source strict [`Option]
    pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_string_from_lean)")
  else if official == `String.Slice.toInt? then do
    unless type == mkApp (mkConst `Option [.zero]) (mkConst `Int) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect optional integer ABI"
    checkIntLayout strict
    IndexedNative.checkDataTypes source strict [`Option]
    pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_int_from_lean)")
  else if syntaxTreeFunction official && [`CoeOut, `CoeTail].contains dom && ret == .object && result == .object then do
    for (env, cls) in [(source, dom), (strict, `Omega ++ dom)] do
      let some (some field) := impureTrivialStructureInfoExt.find? env cls
        | throw <| IO.userError s!"missing syntax coercion layout {cls}"
      unless field.fieldIdx == 0 do throw <| IO.userError s!"invalid syntax coercion field {cls}"
    let arrayLike (t : Expr) := [`Lean.TSyntaxArray, `Lean.Syntax.TSepArray].contains t.getAppFn.constName ||
      (t.isAppOfArity `Array 1 && (t.getArg! 0).isConstOf `Lean.Syntax)
    unless type.getAppNumArgs == 2 && type.getAppArgs.all arrayLike do throw <| IO.userError "unexpected syntax coercion endpoints"
    prepare := prepare ++ "  lean_object *coerce = lean_alloc_closure((void *)omega_syntax_array_coe, 2, 1);\n"
    prepare := prepare ++ s!"  lean_closure_set(coerce, 0, {call});\n"
    pure ("lean_obj_res", "coerce")
  else if syntaxTreeFunction official && ([`Lean.TSyntaxArray, `Lean.Syntax.TSepArray].contains dom ||
      (dom == `Array && (type.getArg! 0).isConstOf `Lean.Syntax)) && ret == .object && result == .tobject then do
    prepare := prepare ++ s!"  lean_object *values = {call};\n"
    cleanup := cleanup ++ "  lean_dec(values);\n"
    pure ("lean_obj_res", "omega_syntax_array_from_lean(values)")
  else if syntaxTreeFunction official && [`Lean.Syntax.Ident, `Lean.Syntax.Term, `Lean.TSyntax].contains dom && ret == .tobject && result == .tobject then do
    prepare := prepare ++ s!"  lean_object *stx = {call};\n"
    cleanup := cleanup ++ "  lean_dec(stx);\n"
    pure ("lean_obj_res", "omega_syntax_from_lean(stx)")
  else if syntaxTreeFunction official && dom == `Option && ret == .tobject && result == .tobject then do
    let payload := type.getArg! 0
    let converter ← if payload == mkConst `String then pure "omega_string_from_lean"
      else if payload == mkConst `Lean.Syntax then pure "omega_syntax_from_lean"
      else throw <| IO.userError s!"unexpected syntax query payload at {n}"
    pure ("lean_obj_res", s!"omega_optional_from_lean({call}, {converter})")
  else if metaLiteralFunction official && dom == `Option && ret == .tobject && result == .tobject then do
    IndexedNative.checkDataTypes source strict [`Option]
    let payload := type.getArg! 0
    if payload == mkConst `String then
      pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_string_from_lean)")
    else if payload == mkConst `Lean.Name then
      checkNameLayout source strict
      hasName := true
      pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_name_from_lean)")
    else if payload == mkConst `Nat then pure ("lean_obj_res", call)
    else
      let pair := fun a b => mkApp2 (mkConst `Prod [.zero, .zero]) a b
      unless payload == pair (mkConst `Nat) (pair (mkConst `Bool) (mkConst `Nat)) do
        throw <| IO.userError s!"unexpected literal payload at {n}"
      IndexedNative.checkDataTypes source strict [`Prod, `Bool]
      pure ("lean_obj_res", call)
  else if official == `Lean.Syntax.splitNameLit then do
    unless type == mkApp (mkConst `List [.zero]) (mkConst `Substring.Raw) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect raw name component ABI"
    IndexedNative.checkDataTypes source strict [`List]
    prepare := prepare ++ s!"  lean_object *components = {call};\n"
    cleanup := cleanup ++ "  lean_dec(components);\n"
    pure ("lean_obj_res", "omega_map_list(components, omega_substring_from_lean)")
  else if dom == `Option && basicStringFunction official then do
    let pos := type.getArg! 0 |>.getAppFn.constName
    unless [`String.Pos, `String.Slice.Pos].contains pos && ret == .tobject && result == .tobject do
      throw <| IO.userError s!"incorrect optional position ABI at {n}"
    for (env, ns) in [(source, Name.anonymous), (strict, `Omega)] do
      for t in [pos, `String.Pos.Raw] do
        let some (some f) := impureTrivialStructureInfoExt.find? env (ns ++ t) | throw <| IO.userError s!"missing position {t}"
        unless f.fieldIdx == 0 do throw <| IO.userError s!"invalid offset layout at {t}"
    IndexedNative.checkDataTypes source strict [`Option]
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
  else if [`String.Pos.Raw, `String.Pos, `String.Slice.Pos].contains dom && (ret == .tobject || ret == .tagged) && result == .tobject then do
    let some (some field) := impureTrivialStructureInfoExt.find? strict (`Omega ++ dom) | throw <| IO.userError "missing raw position"
    unless field.fieldIdx == 0 do throw <| IO.userError "invalid raw position layout"
    pure ("lean_obj_res", call)
  else if dom == `Nat && (ret == .tobject || ret == .tagged) && result == .tobject then pure ("lean_obj_res", call)
  else if (debugPrimitive official || rawFold official) && type == .bvar (params.size - 1) && ret == .tobject && result == .tobject then
    pure ("lean_obj_res", call)
  else if dom == `Ordering && ret == .uint8 && result == .uint8 then do
    IndexedNative.checkDataTypes source strict [`Ordering]
    pure ("uint8_t", call)
  else if [`Bool, `Decidable].contains dom && ret == .uint8 && result == .uint8 then pure ("uint8_t", call)
  else throw <| IO.userError s!"unsupported result of {n}: {dom}/{ret}/{result}"
  let proto ← if usesPinnedFunction official || usesStringExport official then do
    let ctype (t : IR.IRType) : IO String := match t with
      | .uint8 => pure "uint8_t"
      | .uint16 => pure "uint16_t"
      | .uint32 => pure "uint32_t"
      | .uint64 => pure "uint64_t"
      | .usize => pure "size_t"
      | .object | .tobject | .tagged | .erased => pure "lean_object *"
      | _ => throw <| IO.userError s!"unexpected C type at {official}: {t}"
    let inputs ← (params.filter fun p => p.ty != .erased || passesErased).mapM fun p => ctype p.ty
    pure s!"\nextern {← ctype ret} {target}({String.intercalate ", " inputs.toList});\n"
  else if (float? official.getPrefix).isSome || (float? dom).isSome then do
    let header := "\n#include \"float_bits.h\"\n"
    if target.startsWith "lean_" then pure header else
      let ty := if ret == .float then "double" else "float"
      unless (ret == .float || ret == .float32) && params.all (·.ty == ret) do
        throw <| IO.userError s!"unexpected math library signature {target}"
      pure <| header ++ s!"extern {ty} {target}({String.intercalate ", " (List.replicate params.size ty)});\n"
  else if official == `Lean.getGithash then pure s!"\nextern lean_obj_res {target}(lean_obj_arg);\n"
  else if official == `Lean.Internal.hasLLVMBackend then pure s!"\nextern uint8_t {target}(lean_obj_arg);\n"
  else if [`System.Platform.getIsWindows, `System.Platform.getIsOSX, `System.Platform.getIsLinux,
      `System.Platform.getIsEmscripten, `System.Platform.Internal.getHardwareConcurrency].contains official then
    let t := if ret == .uint8 then "uint8_t" else "uint32_t"
    pure s!"\nextern {t} {target}(lean_obj_arg);\n"
  else if target == "lean_dbg_stack_trace" then
    pure "\nextern lean_obj_res lean_dbg_stack_trace(lean_obj_arg);\n"
  else if target == "lean_string_utf8_get_opt" then
    pure "\nextern lean_obj_res lean_string_utf8_get_opt(b_lean_obj_arg, b_lean_obj_arg);\n"
  else if target == "lean_string_utf8_get_bang" then
    pure "\nextern uint32_t lean_string_utf8_get_bang(b_lean_obj_arg, b_lean_obj_arg);\n"
  else if target == "lean_string_utf8_extract_fast" then
    pure "\nextern lean_obj_res lean_string_utf8_extract_fast(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);\n"
  else if official == `ByteArray.copySlice then
    pure "\nextern lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);\n"
  else if official == `System.Platform.getNumBits then
    pure "\nextern lean_obj_res lean_system_platform_nbits(lean_obj_arg);\n" else pure ""
  let header := if syntaxTreeFunction official then "\n#include \"strict_syntax.h\"\n" else if hasName then "\n#include \"strict_name.h\"\n" else if hasString || [`String, `ByteArray].contains dom then "\n#include \"strict_string.h\"\n" else if dom == `Int then "\n#include \"strict_nat.h\"\n" else ""
  return header ++ proto ++ helper ++ s!"\nLEAN_EXPORT {output} {adapter}({String.intercalate ", " decls.toList}) \{\n{prepare}  {output} r = {value};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.WordNative

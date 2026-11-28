module
import OmegaChecks.InitPort.DynamicValue

public import Lean
import OmegaChecks.InitPort.IONative
import OmegaChecks.InitPort.ArrayMap
import OmegaChecks.InitPort.MacroNative
import OmegaChecks.InitPort.SyntaxPositionNative
import OmegaChecks.InitPort.FloatArrayNative
import OmegaChecks.InitPort.IndexedNative
import OmegaChecks.InitPort.BorrowedNative
import OmegaChecks.InitPort.ByteFoldNative

/-! Select the pinned Init operations handled by native word wrappers. -/

open Lean

namespace OmegaChecks.InitPort.WordNative

private def versionNumber? (n : Name) : Option String := do
  let user ← privateToUserName? n
  guard (privatePrefix? n == some (Name.num `_private.Init.Meta.Defs 0))
  match user with
  | `Lean.version.getMajor => some "lean_version_get_major"
  | `Lean.version.getMinor => some "lean_version_get_minor"
  | `Lean.version.getPatch => some "lean_version_get_patch"
  | _ => none

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

private def floatArrayIndex (n : Name) : Bool := n == `FloatArray.get! || n == `FloatArray.set!

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
  [`Array.mapSepElemsM, `Array.filterSepElemsM].contains n ||
    n == mkPrivateNameCore `Init.Meta.Defs `Array.filterSepElemsMAux

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

private def modifyStringFunction (n : Name) : Bool :=
  (n.getPrefix == `String && [`set, `modify, `mapAux, `map, `capitalize, `decapitalize, `toLower, `toUpper].contains (n.updatePrefix .anonymous)) ||
  (n.getPrefix == `String.Pos && [`set, `pastSet, `toSetOfLE, `modify, `pastModify, `toModifyOfLE].contains (n.updatePrefix .anonymous)) ||
  [`String.Pos.Raw.set, `String.Pos.Raw.modify, `String.Internal.capitalizeImpl].contains n

private def errorString (n : Name) : Bool :=
  [`IO.Error.fopenErrorToString, `IO.Error.otherErrorToString].contains n

private def uriFunction (n : Name) : Bool :=
  [`System.Uri.UriEscape.decodeUri, `System.Uri.UriEscape.uriEscapeAsciiChar,
   `System.Uri.pathToUri, `System.Uri.fileUriToPath?].contains n

private def pinnedStringFunction (n : Name) : Bool := uriFunction n || errorString n || modifyStringFunction n || rawStringFunction n || renderName n || defsStringFunction n || basicStringFunction n || decodeStringFunction n || sliceStringFunction n || metaLiteralFunction n || n == `String.toName

private def debugPrimitive (n : Name) : Bool := [`dbgTrace, `dbgTraceIfShared, `dbgSleep, `dbgStackTrace].contains n

private def digitList (n : Name) : Bool := [`Nat.toSuperDigitsAux, `Nat.toSubDigitsAux].contains n

public def usesPinnedFunction (n : Name) : Bool :=
  let method := n.updatePrefix .anonymous
  let trailing := n == `Int.trailingZeros || n == `Int.trailingZeros.aux
  let bytes := [`ByteArray.toUInt64LE!, `ByteArray.toUInt64BE!, `ByteArray.toList.loop, `ByteArray.findIdx?.loop, `ByteArray.findFinIdx?.loop].contains n
  let vector := n.getPrefix == `BitVec &&
    [`abs, `pow, `smod, `replicate, `reverse, `cpop, `cpopNatRec, `ctz, `clz, `clzAuxRec,
     `getLsbD, `getLsb, `getMsbD, `getMsb, `msb, `sdiv, `srem, `smtSDiv, `hash, `ofBoolListLE, `ofBoolListBE].contains method
  [`IO.sleep, `Lean.Name.hash].contains n || MacroNative.supported n || digitList n || trailing || monadicSeparator n || syntaxTreeFunction n || pinnedStringFunction n || modelOperation n || ByteFoldNative.supported n || IndexedNative.supported n || SyntaxPositionNative.supported n || bytes || vector || [`Nat.repr, `Nat.reprFast, `Int.repr].contains n || [`BitVec.toHex, `BitVec.instToString].contains n || n == `Nat.bitwise || ((word? n.getPrefix).isSome && (method == `pow || (method == `ofInt && bitsType n.getPrefix == n.getPrefix))) ||
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

private def thunkExtern : Name → Option String
  | `Thunk.mk => some "lean_mk_thunk"
  | `Thunk.pure => some "lean_thunk_pure"
  | `Thunk.get => some "lean_thunk_get_own"
  | _ => none

public def supported (source : Environment) (owner name : Name) (boxedFloatArray : Bool) : Bool :=
  let method := name.updatePrefix .anonymous
  let widths := [`toUInt8, `toUInt16, `toUInt32, `toUInt64, `toUSize, `toInt8, `toInt16, `toInt32, `toInt64, `toISize]
  let ops := [`add, `sub, `mul, `div, `mod, `land, `lor, `xor, `complement, `neg,
              `shiftLeft, `shiftRight, `log2, `abs, `toInt, `ofInt, `decLt, `decLe, `decEq, `toNat, `ofNat, `ofNatLT, `ofNat32]
  let base := owner == `OmegaInit.Prelude &&
    [`System.Platform.getNumBits, `Lean.Name.beq, `mixHash, `Nat.pred, `Char.ofNatAux, `USize.toBitVec].contains name
  let inOwner := [`OmegaInit.Prelude, `OmegaInit.Data.UInt.BasicAux, `OmegaInit.Data.UInt.Basic, `OmegaInit.Data.UInt.Log2,
                  `OmegaInit.Data.SInt.Basic].contains owner
  let intOwner := [`OmegaInit.Data.Int.Basic, `OmegaInit.Data.Int.DivMod.Basic].contains owner
  let bitwise := owner == `OmegaInit.Data.Nat.Bitwise.Basic && name.getPrefix == `Nat &&
    [`land, `lor, `xor, `shiftLeft, `shiftRight].contains method
  let logarithm := owner == `OmegaInit.Data.Nat.Log2 && name == `Nat.log2
  let wordRepr := owner == `OmegaInit.Data.Repr && name == `USize.repr
  let borrowed := (owner == `OmegaInit.Prelude || owner == `OmegaInit.Data.Array.Basic) && (BorrowedNative.symbol? name).isSome
  let arraySet := owner == `OmegaInit.Data.Array.Set && name == `Array.set!
  let floatIndex := owner == `OmegaInit.Data.FloatArray.Basic && floatArrayIndex name
  let byteOp := owner == `OmegaInit.Data.ByteArray.Basic && name.getPrefix == `ByteArray &&
    [`uget, `get, `get!, `uset, `set, `set!, `usize, `copySlice, `markLinear, `propagateMark, `beq, `decEq, `hash].contains method
  let platform := owner == `OmegaInit.System.Platform && [`System.Platform.getIsWindows, `System.Platform.getIsOSX,
    `System.Platform.getIsLinux, `System.Platform.getIsEmscripten, `System.Platform.getTarget,
    `System.Platform.Internal.getHardwareConcurrency].contains name
  let version := owner == `OmegaInit.Meta.Defs && ((versionNumber? name).isSome || [`Lean.getGithash, `Lean.version.getIsRelease,
    `Lean.version.getSpecialDesc, `Lean.Internal.isStage0, `Lean.Internal.hasLLVMBackend].contains name)
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
  (owner == `OmegaInit.Dynamic && (DynamicValue.operation? name).isSome) ||
    (owner == `OmegaInit.Core && (thunkExtern name).isSome) ||
    (owner == `OmegaInit.Data.FloatArray.Basic && boxedFloatArray && FloatArrayNative.operations.contains name) ||
    (owner == `OmegaInit.Util && (debugPrimitive name || [`isExclusiveUnsafe, `ptrAddrUnsafe].contains name) && isExtern source name) ||
    (owner == `OmegaInit.System.Uri && uriFunction name) ||
    (owner == `OmegaInit.Data.ToString.Name && renderName name) ||
    (owner == `OmegaInit.Data.String.Substring && rawStringFunction name) ||
    (owner == `OmegaInit.Data.String.Defs && defsStringFunction name) ||
    (owner == `OmegaInit.Data.String.Basic && basicStringFunction name) ||
    (owner == `OmegaInit.Data.String.Decode && decodeStringFunction name) ||
    (owner == `OmegaInit.Data.String.Modify && modifyStringFunction name) ||
    (owner == `OmegaInit.Data.String.Slice && sliceStringFunction name) ||
    (owner == `OmegaInit.Meta.Defs && (name == `String.toName || metaLiteralFunction name || syntaxTreeFunction name || monadicSeparator name)) || isFloatCall source owner name ||
    (owner == `OmegaInit.System.IOError && errorString name) ||
    (owner == `OmegaInit.System.IO && IONative.supported name) ||
    (owner == `OmegaInit.Prelude && (name == `Quot.liftOn || name == `Lean.Name.hash || MacroNative.supported name)) ||
    (owner == `OmegaInit.Data.Array.Basic && (ArrayMap.reference? name).isSome) ||
    (owner == `OmegaInit.Data.ByteArray.Basic && ByteFoldNative.supported name) ||
    ([`OmegaInit.Grind.Ring.Envelope, `OmegaInit.Grind.Module.Envelope, `OmegaInit.Data.Array.BasicAux, `OmegaInit.Util, `OmegaInit.ShareCommon, `OmegaInit.Data.List.Attach, `OmegaInit.Data.Option.Attach, `OmegaInit.Data.Array.Attach, `OmegaInit.Data.Vector.Attach,
    `OmegaInit.Core, `OmegaInit.WFComputable, `OmegaInit.Data.List.Impl, `OmegaInit.Data.List.BasicAux,
    `OmegaInit.Data.BitVec.Lemmas, `OmegaInit.Data.List.ControlImpl, `OmegaInit.Data.List.SplitOn.Basic, `OmegaInit.Grind.Ring.CommSolver, `OmegaInit.Data.Nat.Basic, `OmegaInit.Data.Nat.Div.Basic, `OmegaInit.Data.Nat.Lemmas,
    `OmegaInit.Data.RArray, `OmegaInit.Data.Nat.Internal.Linear, `OmegaInit.Data.Nat.Fold, `OmegaInit.Data.Fin.Lemmas].contains owner && IndexedNative.supported name) ||
    ([`OmegaInit.Data.Float.Model.Float, `OmegaInit.Data.Float.Model.Float32].contains owner && modelOperation name) ||
    ([`OmegaInit.Prelude, `OmegaInit.Meta.Defs].contains owner && SyntaxPositionNative.supported name) ||
    ((base || intPrimitive || platform || version || borrowed || arraySet || floatIndex || byteOp || textCompare || modular || stringOp || wordRepr || bitwise || logarithm || (inOwner && primitive)) && isExtern source name) ||
    ((intOwner || [`OmegaInit.Data.Dyadic.Basic, `OmegaInit.Data.ByteArray.Extra, `OmegaInit.Data.ByteArray.Basic, `OmegaInit.Data.Int.Repr, `OmegaInit.Data.Repr, `OmegaInit.Data.Nat.Bitwise.Basic, `OmegaInit.Data.BitVec.Basic].contains owner || [`OmegaInit.Data.UInt.Basic, `OmegaInit.Data.SInt.Basic].contains owner) && usesPinnedFunction name)

end OmegaChecks.InitPort.WordNative

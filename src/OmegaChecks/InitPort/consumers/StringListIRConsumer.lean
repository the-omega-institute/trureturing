module
import Lean
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean

open OmegaChecks.InitPort.NativeState (StringRepr BytesRepr)
open OmegaChecks.InitPort.NativeState.StringRepr (encode)

public unsafe def main (args : List String) : IO Unit := do
  let (lib, dir, decode) ← match args with
    | [lib, dir] => pure (lib, dir, false)
    | [lib, dir, "--decode"] => pure (lib, dir, true)
    | _ => throw <| IO.userError "expected library and consumer directory, optionally followed by --decode"
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `StringListConsumer, importAll := true}] {} (level := .private)
  let raw ← IO.ofExcept <| env.evalConst (StringRepr → BytesRepr) {} `raw
  let equal ← IO.ofExcept <| env.evalConst (StringRepr → StringRepr → Bool) {} `equal
  let less ← IO.ofExcept <| env.evalConst (StringRepr → StringRepr → Bool) {} `less
  let hashFn ← IO.ofExcept <| env.evalConst (StringRepr → Nat) {} `stringHash
  let scalars ← IO.ofExcept <| env.evalConst (StringRepr → List Nat) {} `scalars
  let data ← IO.ofExcept <| env.evalConst (StringRepr → List Nat) {} `stringData
  let roundTrip ← IO.ofExcept <| env.evalConst (StringRepr → StringRepr) {} `roundTrip
  let size ← IO.ofExcept <| env.evalConst (StringRepr → Nat) {} `bytes
  let getAt ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Nat) {} `getAt
  let nextAt ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Nat) {} `nextAt
  let prevAt ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Nat) {} `prevAt
  let endAt ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Bool) {} `endAt
  let validAt ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Bool) {} `validAt
  let push ← IO.ofExcept <| env.evalConst (StringRepr → Nat → StringRepr) {} `pushChar
  let append ← IO.ofExcept <| env.evalConst (StringRepr → StringRepr → StringRepr) {} `appendText
  let length ← IO.ofExcept <| env.evalConst (StringRepr → Nat) {} `textLength
  let extract ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Nat → StringRepr) {} `extractText
  let utf8 ← IO.ofExcept <| env.evalConst (StringRepr → BytesRepr) {} `textUTF8
  let strings := ["", "abc", "ab", "é", "e\u0301", "\u0000中🙂", "🙂"]
  for a in strings do
    let s := encode a
    let cs := a.toList.map Char.toNat
    unless length s == a.length && (utf8 s).data == s.bytes.data do throw <| IO.userError s!"strict length or UTF-8 differs for {repr a}"
    for c in ['a', 'é', '中', '🙂', '\u0000'] do
      unless push s c.toNat == encode (a.push c) do throw <| IO.userError s!"strict push differs at {repr a}, {c.toNat}"
    unless (raw s).data == s.bytes.data && hashFn s == a.hash.toNat && roundTrip s == s &&
        size s == a.utf8ByteSize && scalars s == cs && data s == cs do
      throw <| IO.userError s!"strict string operations disagree at {repr a}"
    for b in strings do
      let t := encode b
      unless append s t == encode (a ++ b) do throw <| IO.userError "strict append differs"
      unless equal s t == (a == b) && less s t == decide (a < b) do
        throw <| IO.userError s!"strict string comparison differs for {repr a} and {repr b}"
    for i in (List.range (a.utf8ByteSize + 3)) ++ [2 ^ 80] do
      let p : String.Pos.Raw := ⟨i⟩
      for j in [0, i, a.utf8ByteSize, a.utf8ByteSize + 1] do
        unless extract s i j == encode (String.Internal.extract a p ⟨j⟩) do
          throw <| IO.userError s!"strict extract differs at {i}..{j}"
      unless getAt s i == (p.get a).toNat && nextAt s i == (p.next a).byteIdx &&
          prevAt s i == (p.prev a).byteIdx && endAt s i == p.atEnd a && validAt s i == p.isValid a do
        throw <| IO.userError s!"strict UTF-8 position {i} differs for {repr a}"
  let valid ← IO.ofExcept <| env.evalConst (BytesRepr → Bool) {} `validBytes
  for bs in [[], [0], [0xc0, 0xaf], [0x80], [0xc3], [0xed, 0xa0, 0x80], [0xf4, 0x90, 0x80, 0x80],
      [0xf4, 0x8f, 0xbf, 0xbf], (encode "é中🙂").bytes.data] do
    let bytes := ByteArray.mk (bs.map Nat.toUInt8).toArray
    unless valid (.ofList bs) == bytes.validateUTF8 do throw <| IO.userError s!"strict UTF-8 validation differs for {bs}"

  if decode then
    let codepoint ← IO.ofExcept <| env.evalConst (BytesRepr → Nat → Option Nat) {} `Omega.ByteArray.utf8DecodeChar?
    let allChars ← IO.ofExcept <| env.evalConst (BytesRepr → Option (List Nat)) {} `Omega.ByteArray.utf8Decode?
    let get? ← IO.ofExcept <| env.evalConst (StringRepr → Nat → Option Nat) {} `Omega.String.Pos.Raw.get?
    let encodeChar ← IO.ofExcept <| env.evalConst (Nat → List Nat) {} `Omega.String.utf8EncodeCharFast
    for input in [[], [0], [0xc0, 0xaf], [0x80], [0xc3], [0xed, 0xa0, 0x80], [0xf4, 0x8f, 0xbf, 0xbf], (encode "é中🙂").bytes.data] do
      let bytes := ByteArray.mk (input.map Nat.toUInt8).toArray
      unless allChars (.ofList input) == bytes.utf8Decode?.map (fun a => a.toList.map Char.toNat) do
        throw <| IO.userError s!"strict UTF-8 decoding differs at {input}"
      for i in List.range (input.length + 2) do
        unless codepoint (.ofList input) i == (bytes.utf8DecodeChar? i).map Char.toNat do
          throw <| IO.userError s!"strict UTF-8 code point differs at byte {i} of {input}"
    for s in strings do
      for i in List.range (s.utf8ByteSize + 2) do
        unless get? (encode s) i == ((String.Pos.Raw.mk i).get? s).map Char.toNat do
          throw <| IO.userError s!"strict optional character differs at byte {i} of {repr s}"
      for c in s.toList do
        unless encodeChar c.toNat == (String.utf8EncodeCharFast c).map UInt8.toNat do
          throw <| IO.userError s!"strict UTF-8 encoding differs at scalar {c.toNat}"

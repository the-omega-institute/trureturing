module
import Lean

open Lean

private def encode (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

public unsafe def main (args : List String) : IO Unit := do
  let [lib, dir] := args | throw <| IO.userError "expected library and consumer directory"
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `StringListConsumer, importAll := true}] {} (level := .private)
  let raw ← IO.ofExcept <| env.evalConst (List Nat → List Nat) {} `raw
  let equal ← IO.ofExcept <| env.evalConst (List Nat → List Nat → Bool) {} `equal
  let less ← IO.ofExcept <| env.evalConst (List Nat → List Nat → Bool) {} `less
  let hashFn ← IO.ofExcept <| env.evalConst (List Nat → Nat) {} `stringHash
  let scalars ← IO.ofExcept <| env.evalConst (List Nat → List Nat) {} `scalars
  let data ← IO.ofExcept <| env.evalConst (List Nat → List Nat) {} `stringData
  let roundTrip ← IO.ofExcept <| env.evalConst (List Nat → List Nat) {} `roundTrip
  let size ← IO.ofExcept <| env.evalConst (List Nat → Nat) {} `bytes
  let getAt ← IO.ofExcept <| env.evalConst (List Nat → Nat → Nat) {} `getAt
  let nextAt ← IO.ofExcept <| env.evalConst (List Nat → Nat → Nat) {} `nextAt
  let prevAt ← IO.ofExcept <| env.evalConst (List Nat → Nat → Nat) {} `prevAt
  let endAt ← IO.ofExcept <| env.evalConst (List Nat → Nat → Bool) {} `endAt
  let validAt ← IO.ofExcept <| env.evalConst (List Nat → Nat → Bool) {} `validAt
  let push ← IO.ofExcept <| env.evalConst (List Nat → Nat → List Nat) {} `pushChar
  let append ← IO.ofExcept <| env.evalConst (List Nat → List Nat → List Nat) {} `appendText
  let length ← IO.ofExcept <| env.evalConst (List Nat → Nat) {} `textLength
  let extract ← IO.ofExcept <| env.evalConst (List Nat → Nat → Nat → List Nat) {} `extractText
  let utf8 ← IO.ofExcept <| env.evalConst (List Nat → List Nat) {} `textUTF8
  let strings := ["", "abc", "ab", "é", "e\u0301", "\u0000中🙂", "🙂"]
  for a in strings do
    let s := encode a
    let cs := a.toList.map Char.toNat
    unless length s == a.length && utf8 s == s do throw <| IO.userError s!"strict length or UTF-8 differs for {repr a}"
    for c in ['a', 'é', '中', '🙂', '\u0000'] do
      unless push s c.toNat == encode (a.push c) do throw <| IO.userError s!"strict push differs at {repr a}, {c.toNat}"
    unless raw s == s && hashFn s == a.hash.toNat && roundTrip s == s &&
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
  let valid ← IO.ofExcept <| env.evalConst (List Nat → Bool) {} `validBytes
  for bs in [[], [0], [0xc0, 0xaf], [0x80], [0xc3], [0xed, 0xa0, 0x80], [0xf4, 0x90, 0x80, 0x80],
      [0xf4, 0x8f, 0xbf, 0xbf], encode "é中🙂"] do
    let bytes := ByteArray.mk (bs.map Nat.toUInt8).toArray
    unless valid bs == bytes.validateUTF8 do throw <| IO.userError s!"strict UTF-8 validation differs for {bs}"

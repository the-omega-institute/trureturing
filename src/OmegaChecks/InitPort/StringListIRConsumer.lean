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
  let strings := ["", "abc", "ab", "é", "e\u0301", "\u0000中🙂", "🙂"]
  for a in strings do
    let s := encode a
    let cs := a.toList.map Char.toNat
    unless raw s == s && hashFn s == a.hash.toNat && roundTrip s == s &&
        size s == a.utf8ByteSize && scalars s == cs && data s == cs do
      throw <| IO.userError s!"strict string operations disagree at {repr a}"
    for b in strings do
      let t := encode b
      unless equal s t == (a == b) && less s t == decide (a < b) do
        throw <| IO.userError s!"strict string comparison differs for {repr a} and {repr b}"

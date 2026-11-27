module
import Lean
import Init.ShareCommon

open Lean

public unsafe def main (args : List String) : IO Unit := do
  let [lib, dir] := args | throw <| IO.userError "expected the strict library and consumer"
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `ShareObjectConsumer, importAll := true}] {} (level := .private)
  let eq ← IO.ofExcept <| env.evalConst (NonScalar → NonScalar → Bool) {} `omegaShareObjectEq
  let hash ← IO.ofExcept <| env.evalConst (NonScalar → Nat) {} `omegaShareObjectHash
  let a : NonScalar := ⟨2 ^ (80 + args.length)⟩
  let b : NonScalar := ⟨2 ^ (79 + args.length) * 2⟩
  for x in [a, b, (⟨a.val + 1⟩ : NonScalar)] do
    unless hash x == (ShareCommon.Object.hash x).toNat &&
        eq a x == ShareCommon.Object.eq a x do
      throw <| IO.userError "strict object observer disagrees with the pinned runtime"

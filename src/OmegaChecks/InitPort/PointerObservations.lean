import Init.Util

/-! Execute with the pinned Lean interpreter to observe the native results on equal inputs. -/

@[noinline] private def singleton (n : Nat) : List Nat := [n]
@[noinline] private def reversed (xs : List Nat) : List Nat := xs.reverse

unsafe def main (args : List String) : IO Unit := do
  let a := singleton args.length
  let b := reversed [args.length]
  unless a == b do throw <| IO.userError "expected equal list values"
  unless ptrAddrUnsafe a != ptrAddrUnsafe b do throw <| IO.userError "expected two live allocations"
  unless ptrEq a a && !ptrEq a b do throw <| IO.userError "expected pointer identity to distinguish the lists"
  unless ptrEqList [a] [a] && !ptrEqList [a] [b] do
    throw <| IO.userError "expected elementwise pointer identity to distinguish the singleton lists"
  IO.println "Equal list values returned different addresses, pointer equalities, and elementwise pointer equalities."

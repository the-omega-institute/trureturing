module
public import Init.Util
public import Init.System.IO

/-! Native pointer observations can distinguish propositionally equal list values. -/

namespace OmegaChecks.InitBoundaries.PointerObservations

/-- A pure candidate that distinguishes equal inputs contradicts substitution. -/
public theorem address (read : type_of% @ptrAddrUnsafe.{0})
    (observed : ∃ a b : List Nat, a = b ∧ @read _ a ≠ @read _ b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg _ eq)

public theorem pointerEquality (read : type_of% @ptrEq.{0})
    (observed : ∃ a b : List Nat, a = b ∧ read a a ≠ read a b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (read a) eq)

public theorem listPointerEquality (read : type_of% @ptrEqList.{0})
    (observed : ∃ a b : List Nat, a = b ∧ read [a] [a] ≠ read [a] [b]) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (fun x => read [a] [x]) eq)

@[noinline] private def singleton (n : Nat) : List Nat := [n]
@[noinline] private def reversed (xs : List Nat) : List Nat := xs.reverse

/-- Observe which pinned primitives distinguish equal inputs on this runtime. -/
public unsafe def observe (seed : Nat) : IO (List String) := do
  let a := singleton seed
  let b := reversed [seed]
  unless decide (a = b) do throw <| IO.userError "expected equal list values"
  let results := [("ptrAddrUnsafe", ptrAddrUnsafe a != ptrAddrUnsafe b),
    ("ptrEq", ptrEq a a != ptrEq a b), ("ptrEqList", ptrEqList [a] [a] != ptrEqList [a] [b])]
  return (results.filter Prod.snd).map Prod.fst

end OmegaChecks.InitBoundaries.PointerObservations

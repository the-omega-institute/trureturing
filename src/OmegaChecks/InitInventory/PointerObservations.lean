module
public import Init.Util
public import Init.System.IO
public import Init.ShareCommon

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

public theorem objectPointerEquality (read : type_of% @ShareCommon.Object.ptrEq)
    (observed : ∃ a b : NonScalar, a = b ∧ read a a ≠ read a b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (read a) eq)

public theorem objectPointerHash (read : type_of% @ShareCommon.Object.ptrHash)
    (observed : ∃ a b : NonScalar, a = b ∧ read a ≠ read b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg read eq)

@[noinline] private def singleton (n : Nat) : List Nat := [n]
@[noinline] private def reversed (xs : List Nat) : List Nat := xs.reverse

-- A large Nat is boxed. Compute the same field value by two independent allocations.
@[noinline] private def object (n : Nat) : NonScalar := ⟨2 ^ (80 + n)⟩
@[noinline] private def equalObject (n : Nat) : NonScalar := ⟨2 ^ (79 + n) * 2⟩

/-- Observe which pinned primitives distinguish equal inputs on this runtime. -/
public unsafe def observe (seed : Nat) : IO (List String) := do
  let a := singleton seed
  let b := reversed [seed]
  unless decide (a = b) do throw <| IO.userError "expected equal list values"
  let x := object (seed % 17)
  let y := equalObject (seed % 17)
  unless x.val == y.val do throw <| IO.userError "expected equal NonScalar fields"
  let results := [("ptrAddrUnsafe", ptrAddrUnsafe a != ptrAddrUnsafe b),
    ("ptrEq", ptrEq a a != ptrEq a b), ("ptrEqList", ptrEqList [a] [a] != ptrEqList [a] [b]),
    ("ShareCommon.Object.ptrEq", ShareCommon.Object.ptrEq x x != ShareCommon.Object.ptrEq x y),
    ("ShareCommon.Object.ptrHash", ShareCommon.Object.ptrHash x != ShareCommon.Object.ptrHash y)]
  return (results.filter Prod.snd).map Prod.fst

end OmegaChecks.InitBoundaries.PointerObservations

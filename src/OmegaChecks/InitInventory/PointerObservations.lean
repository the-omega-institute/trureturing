module
public import Init.Util

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

end OmegaChecks.InitBoundaries.PointerObservations

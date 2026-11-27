module
public import Init.Util
public import Init.System.IO
public import Init.ShareCommon

/-! Native allocation and pointer observations can distinguish propositionally equal values. -/

namespace OmegaChecks.InitBoundaries.PointerObservations

/-- A pure candidate that distinguishes equal inputs contradicts substitution. -/
public theorem address (read : type_of% @ptrAddrUnsafe.{0})
    (observed : ∃ a b : List Nat, a = b ∧ @read _ a ≠ @read _ b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg _ eq)

public theorem exclusivity (read : type_of% @isExclusiveUnsafe.{0})
    (observed : ∃ a b : Array Nat, a = b ∧ @read _ a ≠ @read _ b) : False := by
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

/-- The type tag is erased. The list field controls the runtime representation. -/
private structure Tagged where
  tag : Type
  data : List Nat

private theorem differentTags (a b : List Nat) (h : Tagged.mk Unit a = Tagged.mk Empty b) : false = true :=
  (Eq.mp (congrArg Tagged.tag h) ()).elim

public def compareTagged (read : type_of% @withPtrEqUnsafe.{1}) (a b : List Nat) : Bool :=
  read (Tagged.mk Unit a) (Tagged.mk Empty b) (fun _ => false) (differentTags a b)

public theorem guardedPointerEquality (read : type_of% @withPtrEqUnsafe.{1})
    (observed : ∃ a b : List Nat, a = b ∧ compareTagged read a a ≠ compareTagged read a b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (compareTagged read a) eq)

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

-- The native compiler stores the two literals persistently. The other array is allocated at runtime.
@[noinline] private def freshArray (bit : Nat) : Array Nat := Array.replicate 1 bit
@[noinline] private def staticArray (bit : Nat) : Array Nat := if bit == 0 then #[0] else #[1]
@[noinline] private unsafe def exclusive (a : @& Array Nat) := isExclusiveUnsafe a

/-- The executed comparisons include an independent equality check on the arrays. -/
public unsafe def distinguishesExclusivity (bit : Nat) : Bool :=
  exclusive (freshArray bit) && !exclusive (staticArray bit) && decide (freshArray bit = staticArray bit)

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
    ("withPtrEqUnsafe", compareTagged (@withPtrEqUnsafe) a a && !compareTagged (@withPtrEqUnsafe) a b),
    ("ShareCommon.Object.ptrEq", ShareCommon.Object.ptrEq x x != ShareCommon.Object.ptrEq x y),
    ("ShareCommon.Object.ptrHash", ShareCommon.Object.ptrHash x != ShareCommon.Object.ptrHash y)]
  return (results.filter Prod.snd).map Prod.fst

end OmegaChecks.InitBoundaries.PointerObservations

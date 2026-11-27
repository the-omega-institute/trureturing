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

private theorem differentTags (a b : List Nat) (h : Tagged.mk Unit a = Tagged.mk Empty b) : False :=
  (Eq.mp (congrArg Tagged.tag h) ()).elim

public def compareTagged (read : type_of% @withPtrEqUnsafe.{1}) (a b : List Nat) : Bool :=
  read (Tagged.mk Unit a) (Tagged.mk Empty b) (fun _ => false) (fun h => (differentTags a b h).elim)

public theorem guardedPointerEquality (read : type_of% @withPtrEqUnsafe.{1})
    (observed : ∃ a b : List Nat, a = b ∧ compareTagged read a a ≠ compareTagged read a b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (compareTagged read a) eq)

/-- Distinct erased tags have a negative equality decision for every choice of list payloads. -/
@[noinline] public def decideTagged (read : type_of% @withPtrEqDecEq.{1}) (a b : List Nat) : Bool :=
  toBoolUsing (read (Tagged.mk Unit a) (Tagged.mk Empty b) (fun _ => .isFalse (differentTags a b)))

public theorem guardedPointerDecision (read : type_of% @withPtrEqDecEq.{1})
    (observed : ∃ a : List Nat, decideTagged read a a = true) : False := by
  obtain ⟨a, h⟩ := observed
  have negative : decideTagged read a a = false :=
    @decide_eq_false _ (read (Tagged.mk Unit a) (Tagged.mk Empty a) (fun _ => .isFalse (differentTags a a)))
      (differentTags a a)
  exact Bool.noConfusion (negative.symm.trans h)

public theorem objectPointerEquality (read : type_of% @ShareCommon.Object.ptrEq)
    (observed : ∃ a b : NonScalar, a = b ∧ read a a ≠ read a b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (read a) eq)

public theorem objectPointerHash (read : type_of% @ShareCommon.Object.ptrHash)
    (observed : ∃ a b : NonScalar, a = b ∧ read a ≠ read b) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg read eq)

public theorem packedPayloadEquality (read : type_of% @ShareCommon.Object.eq) (pack : List (List Nat) → NonScalar)
    (observed : ∃ a b, a = b ∧ read (pack a) (pack a) ≠ read (pack a) (pack b)) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (fun t => read (pack a) (pack t)) eq)

public theorem packedPayloadHash (read : type_of% @ShareCommon.Object.hash) (pack : List (List Nat) → NonScalar)
    (observed : ∃ a b, a = b ∧ read (pack a) ≠ read (pack b)) : False := by
  obtain ⟨a, b, eq, different⟩ := observed
  exact different (congrArg (fun t => read (pack t)) eq)

@[noinline] private def singleton (n : Nat) : List Nat := [n]
@[noinline] private def nested (xs : List Nat) : List (List Nat) := [xs]
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
    ("withPtrEqDecEq", decideTagged (@withPtrEqDecEq) a a && !decideTagged (@withPtrEqDecEq) a b),
    ("ShareCommon.Object.ptrEq", ShareCommon.Object.ptrEq x x != ShareCommon.Object.ptrEq x y),
    ("ShareCommon.Object.ptrHash", ShareCommon.Object.ptrHash x != ShareCommon.Object.ptrHash y)]
  return (results.filter Prod.snd).map Prod.fst

/-- Heterogeneous heap payloads reach the declared NonScalar parameter only through an unsafe cast. -/
public unsafe def observePacked (seed : Nat) : IO (List String) := do
  let a := singleton seed
  let b := reversed [seed]
  let x := object (seed % 17)
  let y := equalObject (seed % 17)
  unless ShareCommon.Object.eq x y && ShareCommon.Object.hash x == ShareCommon.Object.hash y do
    throw <| IO.userError "expected equal large Nat payloads"
  let leaf₁ : NonScalar := unsafeCast a
  let leaf₂ : NonScalar := unsafeCast b
  unless !ptrEq a b && ShareCommon.Object.eq leaf₁ leaf₂ &&
      ShareCommon.Object.hash leaf₁ == ShareCommon.Object.hash leaf₂ do
    throw <| IO.userError "expected separate singleton lists with identical scalar payloads"
  let outer₁ := nested a
  let outer₂ := nested b
  unless decide (outer₁ = outer₂) do throw <| IO.userError "expected equal nested lists"
  let packed₁ : NonScalar := unsafeCast outer₁
  let packed₂ : NonScalar := unsafeCast outer₂
  unless ShareCommon.Object.eq packed₁ packed₁ do throw <| IO.userError "expected identical object payloads"
  let results := [("ShareCommon.Object.eq", !ShareCommon.Object.eq packed₁ packed₂),
    ("ShareCommon.Object.hash", ShareCommon.Object.hash packed₁ != ShareCommon.Object.hash packed₂)]
  return (results.filter Prod.snd).map Prod.fst

end OmegaChecks.InitBoundaries.PointerObservations

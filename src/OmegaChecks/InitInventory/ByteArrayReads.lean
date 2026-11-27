module
public import Init.Data.ByteArray.Basic
public import Init.Data.UInt.Lemmas

/-! Bounds required by the first read of the two machine-word byte array helpers. -/

namespace OmegaChecks.InitBoundaries.ByteArrayReads

private def last : USize :=
  USize.ofFin ⟨1, by
    cases USize.size_eq with
    | inl h => rw [h]; decide
    | inr h => rw [h]; decide⟩

private theorem less : (0 : USize) < last :=
  Nat.zero_lt_succ 0

private theorem ne : (0 : USize) ≠ last := fun e =>
  Nat.noConfusion (congrArg USize.toNat e)

public theorem noForInBound (read : ∀ (xs : ByteArray) (stop i : USize), i < stop → i.toNat < xs.size) : False :=
  Nat.not_lt_zero _ (read ByteArray.empty last 0 less)

public theorem noFoldBound (read : ∀ (xs : ByteArray) (i stop : USize), i ≠ stop → i.toNat < xs.size) : False :=
  Nat.not_lt_zero _ (read ByteArray.empty 0 last ne)

end OmegaChecks.InitBoundaries.ByteArrayReads

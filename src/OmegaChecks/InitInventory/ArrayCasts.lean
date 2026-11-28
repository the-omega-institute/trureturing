module
public import Init.Data.Array.Basic
public import Init.Data.UInt.Lemmas
public import Init.Data.List.Lemmas

/-! A polymorphic array cast cannot preserve the length of an unvisited, nonempty input
when the target element type is empty and its machine-word length wraps to zero. -/

namespace OmegaChecks.InitBoundaries.ArrayCasts

private def fullWord : Array Unit := ⟨List.replicate USize.size ()⟩

private theorem sizeFullWord : fullWord.size = USize.size := by
  have length (n : Nat) : (List.replicate n ()).length = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact length _

private theorem zeroWord : fullWord.usize = 0 := by
  change USize.ofNat fullWord.size = 0
  rw [sizeFullWord]
  apply USize.toNat.inj
  change USize.size % USize.size = 0
  cases USize.size_eq with
  | inl h => rw [h]
  | inr h => rw [h]

private theorem positiveResult (result : Array Empty) (kept : result.size = fullWord.size) : False :=
  (result[0]'(Nat.lt_of_lt_of_eq USize.size_pos (kept.trans sizeFullWord).symm)).elim

/-- The zero-iteration exit of the type-changing map returns the existing buffer
through a cast. A typed successful exit cannot have that buffer's length. -/
public theorem map (candidate : type_of% @Array.mapMUnsafe.{0,0,0})
    (exit : ∀ xs : Array Unit, xs.usize = 0 →
      ∃ out : Array Empty, @candidate Unit Empty Option inferInstance (fun _ => none) xs = some out ∧
        out.size = xs.size) : False := by
  obtain ⟨out, _, size⟩ := exit fullWord zeroWord
  exact positiveResult out size

public theorem mapIndexed (candidate : type_of% @Array.mapFinIdxMUnsafe.{0,0,0})
    (exit : ∀ xs : Array Unit, xs.usize = 0 →
      ∃ out : Array Empty, @candidate Unit Empty Option inferInstance xs (fun _ _ _ => none) = some out ∧
        out.size = xs.size) : False := by
  obtain ⟨out, _, size⟩ := exit fullWord zeroWord
  exact positiveResult out size

end OmegaChecks.InitBoundaries.ArrayCasts

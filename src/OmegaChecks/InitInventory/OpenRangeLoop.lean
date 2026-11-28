module
import all OmegaChecks.InitInventory.Collector
public import Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.RangeIterator
public import Init.Data.Range.Polymorphic.Nat
import OmegaChecks.InitPort.Alternatives.Range.Enumeration

/-! The exported half-open range helper accepts an arbitrary decidable strict comparison.
With the standard natural successor, comparing against a bound can search a Boolean stream. -/

public section

namespace OmegaChecks.InitBoundaries.Collector
open Std Std.Iterators Std.PRange

@[instance_reducible] def whileUnseen (g : Nat → Bool) : LT Nat := ⟨fun k _ => g k = false⟩
@[instance_reducible] private def cmp (g : Nat → Bool) : @DecidableLT Nat (whileUnseen g) :=
  fun k _ => decEq (g k) false

/-- An always-true comparison keeps every natural successor inside the half-open range. -/
theorem openRangeWithoutCutoff : ¬ @Rxo.IsAlwaysFinite Nat _ (whileUnseen (fun _ => false)) := by
  intro finite
  obtain ⟨k, stop⟩ := finite.finite 0 0
  exact stop rfl

private theorem finiteWhenSeen {g : Nat → Bool} (sticky : ∀ i, g i = true → g (i+1) = true)
    {n : Nat} (hit : g n = true) : @Rxo.IsAlwaysFinite Nat _ (whileUnseen g) := by
  letI : LT Nat := whileUnseen g
  exact ⟨fun lo hi => by
    refine ⟨n, ?_⟩
    change ¬ g (lo+n) = false
    exact fun no => Bool.noConfusion (no.symm.trans (signal_after sticky hit (Nat.le_add_left ..)))⟩

abbrev OpenLoop := type_of% (@Rxo.Iterator.instIteratorLoop.loop.{0,0})
def stopIndex (run : OpenLoop) (g : Nat → Bool) (k : Nat) : Nat :=
  @run Nat _ (whileUnseen g) (cmp g)
    OmegaChecks.InitPort.Alternatives.Std.PRange.instLawfulUpwardEnumerableNat Id _ Nat (fun _ _ _ => True)
    (fun _ => True) (fun _ _ _ _ => trivial) 0 k k trivial
    (fun out _ _ _ => ⟨.yield (out+1), trivial⟩)

/-- The pinned implementation satisfies the search equation on finite ranges. -/
theorem officialOpenRangeSearchStep (g : Nat → Bool) (k : Nat) (finite : @Rxo.IsAlwaysFinite Nat _ (whileUnseen g)) :
    stopIndex (@Rxo.Iterator.instIteratorLoop.loop) g k =
      if g k = false then stopIndex (@Rxo.Iterator.instIteratorLoop.loop) g (k+1) else k := by
  letI : LT Nat := whileUnseen g
  letI : DecidableLT Nat := cmp g
  letI : Rxo.IsAlwaysFinite Nat := finite
  let wf := IteratorLoop.wellFounded_of_finite (α := Rxo.Iterator Nat) (m := Id)
    (P := fun (_ _ : Nat) (_ : ForInStep Nat) => True)
  unfold stopIndex
  rw [Rxo.Iterator.instIteratorLoop.loop.eq_1, WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
  by_cases h : g k = false
  · simp only [ite_eq_left h]
    have inside : k < 0 := h
    simp only [dite_eq_left inside]
    rfl
  · simp only [ite_eq_right h]
    have outside : ¬ k < 0 := h
    simp only [dite_eq_right outside]
    rfl

/-- On finite half-open ranges the unrestricted helper recovers an index of the signal. -/
def limitedOmniscienceFromOpenRangeLoop (run : OpenLoop)
    (unroll : ∀ (g : Nat → Bool), @Rxo.IsAlwaysFinite Nat _ (whileUnseen g) →
      ∀ k, stopIndex run g k = if g k = false then stopIndex run g (k+1) else k)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  let g := seen f
  let index := stopIndex run g
  cases observed : g (index 0) with
  | true => exact isTrue (hit_of_seen f _ observed)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have found : g n = true := seen_of_hit f n hit
    have finite := finiteWhenSeen (seenSticky f) found
    have result (fuel k : Nat) (enough : n ≤ k + fuel) : g (index k) = true := by
      induction fuel generalizing k with
      | zero =>
        have yes : g k = true := signal_after (seenSticky f) found enough
        have z := unroll g finite k
        rw [ite_eq_right (fun h => Bool.noConfusion (h.symm.trans yes))] at z
        exact (congrArg g z).trans yes
      | succ fuel ih =>
        have step := unroll g finite k
        cases atK : g k with
        | true =>
          rw [ite_eq_right (fun h => Bool.noConfusion (h.symm.trans atK))] at step
          exact (congrArg g step).trans atK
        | false =>
          rw [ite_eq_left atK] at step
          exact (congrArg g step).trans (ih (k+1) (Nat.succ_add _ _ ▸ enough))
    exact Bool.noConfusion (observed.symm.trans (result n 0 ((Nat.zero_add n).symm ▸ Nat.le_refl n)))

end OmegaChecks.InitBoundaries.Collector

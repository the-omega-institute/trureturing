module
public import OmegaChecks.InitInventory.Collector
import all OmegaChecks.InitInventory.Collector
public import Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.RangeIterator
public import Init.Data.Range.Polymorphic.Nat
import OmegaChecks.InitPort.Alternatives.Range.Enumeration

/-! The half-open range helper can search a Boolean stream through its strict comparison.
The right-unbounded range helper can search the same stream through its successor operation. -/

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

private def decideFromStoppingIndex (f : Nat → Bool) (index : Nat → Nat)
    (unroll : (∃ n, seen f n = true) → ∀ k, index k = if seen f k = false then index (k+1) else k) :
    Decidable (∃ n, f n = true) := by
  let g := seen f
  cases observed : g (index 0) with
  | true => exact isTrue (hit_of_seen f _ observed)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have found : g n = true := seen_of_hit f n hit
    have finite : ∃ j, g j = true := ⟨n, found⟩
    have result (fuel k : Nat) (enough : n ≤ k + fuel) : g (index k) = true := by
      induction fuel generalizing k with
      | zero =>
        have yes : g k = true := signal_after (seenSticky f) found enough
        have z := unroll finite k
        rw [ite_eq_right (fun h => Bool.noConfusion (h.symm.trans yes))] at z
        exact (congrArg g z).trans yes
      | succ fuel ih =>
        have step := unroll finite k
        cases atK : g k with
        | true =>
          rw [ite_eq_right (fun h => Bool.noConfusion (h.symm.trans atK))] at step
          exact (congrArg g step).trans atK
        | false =>
          rw [ite_eq_left atK] at step
          exact (congrArg g step).trans (ih (k+1) (Nat.succ_add _ _ ▸ enough))
    exact Bool.noConfusion (observed.symm.trans (result n 0 ((Nat.zero_add n).symm ▸ Nat.le_refl n)))


/-- On finite half-open ranges the unrestricted helper recovers an index of the signal. -/
def limitedOmniscienceFromOpenRangeLoop (run : OpenLoop)
    (unroll : ∀ (g : Nat → Bool), @Rxo.IsAlwaysFinite Nat _ (whileUnseen g) →
      ∀ k, stopIndex run g k = if g k = false then stopIndex run g (k+1) else k)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  decideFromStoppingIndex f (stopIndex run (seen f)) fun ⟨_, hit⟩ =>
    unroll _ (finiteWhenSeen (seenSticky f) hit)

private def delayed (g : Nat → Bool) (k : Nat) : Bool := g k.pred

private theorem delayedSticky {g : Nat → Bool} (sticky : ∀ k, g k = true → g (k+1) = true) :
    ∀ k, delayed g k = true → delayed g (k+1) = true
  | 0 => id
  | k+1 => sticky k

abbrev UnboundedLoop := type_of% (@Rxi.Iterator.instIteratorLoop.loop.{0,0})

def unboundedStopIndex (run : UnboundedLoop) (f : Nat → Bool) (k : Nat) : Nat :=
  @run Nat (signalRange (delayed (seen f))) (signalRangeLaw (delayedSticky (seenSticky f))) Id _ Nat
    (fun _ _ _ => True) (fun _ => True) (fun _ _ _ _ => trivial) k.pred k trivial
    (fun out _ _ => ⟨.yield out, trivial⟩)

/-- The right-unbounded loop stops when the Boolean stream disables the next successor. -/
theorem officialUnboundedSearchStep (f : Nat → Bool) (found : ∃ n, f n = true) (k : Nat) :
    unboundedStopIndex (@Rxi.Iterator.instIteratorLoop.loop) f k =
      if seen f k = false then unboundedStopIndex (@Rxi.Iterator.instIteratorLoop.loop) f (k+1) else k := by
  obtain ⟨n, hit⟩ := found
  let g := delayed (seen f)
  letI := signalRange g
  letI := signalRangeLaw (delayedSticky (seenSticky f))
  have cutoff : g (n+1) = true := seen_of_hit f n hit
  letI := signalRangeFinite (delayedSticky (seenSticky f)) cutoff
  let wf := IteratorLoop.wellFounded_of_finite (α := Rxi.Iterator Nat) (m := Id)
    (P := fun (_ _ : Nat) (_ : ForInStep Nat) => True)
  unfold unboundedStopIndex
  rw [Rxi.Iterator.instIteratorLoop.loop.eq_1, WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
  dsimp only [Bind.bind, Pure.pure]
  cases state : seen f k with
  | true =>
    have stop : succ? k = none := by
      change (if seen f k = true then none else some (k+1)) = none
      exact ite_eq_left state
    split
    · rename_i y hy; cases stop.symm.trans hy
    · rfl
  | false =>
    have goes : succ? k = some (k+1) := by
      change (if seen f k = true then none else some (k+1)) = _
      exact ite_eq_right (fun yes => Bool.noConfusion (state.symm.trans yes))
    split
    · rename_i y hy; cases Option.some.inj (goes.symm.trans hy); rfl
    · rename_i hn; cases goes.symm.trans hn

/-- Agreement with the official loop when the signal exists determines its existence on every stream. -/
def limitedOmniscienceFromUnboundedRangeLoop (run : UnboundedLoop)
    (unroll : ∀ f : Nat → Bool, (∃ n, f n = true) → ∀ k, unboundedStopIndex run f k =
      if seen f k = false then unboundedStopIndex run f (k+1) else k)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  decideFromStoppingIndex f (unboundedStopIndex run f) fun ⟨i, hi⟩ => unroll f (hit_of_seen f i hi)

end OmegaChecks.InitBoundaries.Collector

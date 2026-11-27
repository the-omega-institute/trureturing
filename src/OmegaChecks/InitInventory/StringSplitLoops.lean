module
import all OmegaChecks.InitInventory.Collector
import all Init.Data.String.Slice
import Init.Data.Iterators.Lemmas.Consumers.Loop

public section

/-! Limited omniscience from a total split loop that agrees with the pinned loop on finite searchers.
Each search step emits the same empty match. Its natural-number state advances until the
input stream signals. When a signal exists, the searcher's finite instance and the loop laws
force the output length to decrease at every preceding step. -/

namespace OmegaChecks.InitBoundaries.Collector
open Std Std.Iterators String.Slice.Pattern

private def decisionFromDecreasingLength (size : (Nat → Bool) → Nat → Nat)
    (drops : ∀ g, (∀ k, g k = true → g (k+1) = true) → (∃ k, g k = true) →
      ∀ k, g k = false → size g (k+1) < size g k)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  let g := seen f
  cases h : g (size g 0) with
  | true => exact isTrue (hit_of_seen f _ h)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have decr := drops g (seenSticky f) ⟨n, seen_of_hit f n hit⟩
    have stops (k fuel : Nat) (enough : size g k ≤ fuel) : g (k + fuel) = true := by
      induction fuel generalizing k with
      | zero =>
        cases e : g k with
        | true => rfl
        | false => have := decr k e; omega
      | succ fuel ih =>
        cases e : g k with
        | true => exact signal_after (seenSticky f) e (Nat.le_add_right ..)
        | false =>
          have lt := decr k e
          simpa only [Nat.add_succ, Nat.succ_add] using ih (k+1) (by omega)
    exact Bool.noConfusion (h.symm.trans (by simpa only [Nat.zero_add] using stops 0 _ (Nat.le_refl _)))

private def countedStep (g : Nat → Bool) (s : String.Slice) (it : IterM (α := Nat) Id (SearchStep s)) :
    IterStep (IterM (α := Nat) Id (SearchStep s)) (SearchStep s) :=
  if g it.internalState then .done else .yield ⟨it.internalState+1⟩ (.matched s.startPos s.startPos)

@[instance_reducible] private def countingSearcher (g : Nat → Bool) (s : String.Slice) :
    Iterator Nat Id (SearchStep s) where
  IsPlausibleStep it step := step = countedStep g s it
  step it := pure (.deflate ⟨countedStep g s it, rfl⟩)

private theorem countingFinite {g : Nat → Bool} (sticky : ∀ k, g k = true → g (k+1) = true)
    {n : Nat} (hit : g n = true) (s : String.Slice) :
    letI := countingSearcher g s
    Finite Nat Id := by
  letI := countingSearcher g s
  apply Finite.of_finitenessRelation
  refine ⟨InvImage Nat.lt (fun it : IterM (α := Nat) Id (SearchStep s) => n - it.internalState),
    InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it it' h
  obtain ⟨step, dest, plausible⟩ := h
  change step = countedStep g s it at plausible
  subst step
  dsimp only [countedStep] at dest
  cases e : g it.internalState with
  | true => simp only [e, ite_true] at dest; cases dest
  | false =>
    simp only [e, Bool.false_eq_true, ite_false] at dest
    cases Option.some.inj dest
    have lt : it.internalState < n := Nat.lt_of_not_ge fun ge => Bool.noConfusion (e.symm.trans (signal_after sticky hit ge))
    change n - (it.internalState + 1) < n - it.internalState
    omega

private abbrev slice := "".toSlice
@[instance_reducible] private def toForward : ToForwardSearcher () (fun _ => Nat) := ⟨fun _ => ⟨0⟩⟩
@[instance_reducible] private def toBackward : ToBackwardSearcher () (fun _ => Nat) := ⟨fun _ => ⟨0⟩⟩
attribute [local instance] toForward toBackward
private abbrev split (k : Nat) : Iter (α := @String.Slice.SplitIterator (fun _ => Nat) Unit () slice toForward) slice.Subslice :=
  ⟨.operating slice.startPos ⟨k⟩⟩

private theorem searchYield {g : Nat → Bool} {k : Nat} (miss : g k = false) :
    letI := countingSearcher g slice
    (⟨k⟩ : Iter (α := Nat) (SearchStep slice)).step.val =
      .yield ⟨k+1⟩ (.matched slice.startPos slice.startPos) := by
  letI := countingSearcher g slice
  change (IterM.Step.toPure (it := (⟨k⟩ : Iter (α := Nat) (SearchStep slice)).toIterM) (Shrink.inflate (Shrink.deflate _))).val = _
  rw [Shrink.inflate_deflate]
  simp [countedStep, miss, IterM.Step.toPure, IterStep.mapIterator, Iter.toIterM, IterM.toIter]

private theorem splitYield {g : Nat → Bool} {k : Nat} (miss : g k = false) :
    letI := countingSearcher g
    letI := toForward
    ∃ b, (split k).step.val = .yield (split (k+1)) b := by
  letI := countingSearcher g
  letI := toForward
  refine ⟨slice.subslice! slice.startPos slice.startPos, ?_⟩
  letI : Iterator Nat Id (SearchStep slice) := countingSearcher g slice
  have h := searchYield miss
  rw [Iter.step_eq]
  simp only [split, Iter.toIterM_mk]
  generalize hs : (⟨k⟩ : Iter (α := Nat) (SearchStep slice)).step = step at *
  rcases step with ⟨v, hv⟩
  change v = _ at h
  cases h
  simp only [Id.run, pure, Shrink.inflate_deflate]
  rfl

private def splitLength (run : type_of% (@String.Slice.SplitIterator.instIteratorLoopIdSubsliceOfMonad.{0,0})) (g : Nat → Bool) (k : Nat) : Nat :=
  letI := countingSearcher g
  letI := @run Unit (fun _ => Nat) (countingSearcher g) () toForward Id slice inferInstance
  (split k).length

/-- An unrestricted forward split loop decides a Boolean stream if it is lawful on finite searchers. -/
def limitedOmniscienceFromSplitLoop
    (run : type_of% (@String.Slice.SplitIterator.instIteratorLoopIdSubsliceOfMonad.{0,0}))
    (correct : ∀ {ρ : Type} {σ : String.Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)]
      (pat : ρ) [searcher : ToForwardSearcher pat σ] (s : String.Slice) [Finite (σ s) Id],
      letI := @run ρ σ _ pat searcher Id s inferInstance
      LawfulIteratorLoop (String.Slice.SplitIterator pat s) Id Id)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply decisionFromDecreasingLength (splitLength run) ?_ f
  intro g sticky ⟨n, hit⟩ k miss
  letI := countingSearcher g
  letI : Iterator Nat Id (SearchStep slice) := countingSearcher g slice
  letI : Finite (β := SearchStep slice) Nat Id := countingFinite sticky hit slice
  letI := @run Unit (fun _ => Nat) (countingSearcher g) () toForward Id slice inferInstance
  letI := @correct Unit (fun _ => Nat) (countingSearcher g) () toForward slice (countingFinite sticky hit slice)
  obtain ⟨b, step⟩ := splitYield miss
  change (split (k+1)).length < (split k).length
  rw [Iter.length_eq_match_step (it := split k), step]
  exact Nat.lt_succ_self _

private abbrev inclusive (k : Nat) : Iter (α := @String.Slice.SplitInclusiveIterator (fun _ => Nat) Unit () slice toForward) String.Slice :=
  ⟨.operating slice.startPos ⟨k⟩⟩
private theorem inclusiveYield {g : Nat → Bool} {k : Nat} (miss : g k = false) :
    letI := countingSearcher g
    letI := toForward
    ∃ b, (inclusive k).step.val = .yield (inclusive (k+1)) b := by
  letI := countingSearcher g
  letI := toForward
  refine ⟨slice.slice! slice.startPos slice.startPos, ?_⟩
  letI : Iterator Nat Id (SearchStep slice) := countingSearcher g slice
  have h := searchYield miss
  rw [Iter.step_eq]
  simp only [inclusive, Iter.toIterM_mk]
  generalize hs : (⟨k⟩ : Iter (α := Nat) (SearchStep slice)).step = step at *
  rcases step with ⟨v, hv⟩
  change v = _ at h
  cases h
  simp only [Id.run, pure, Shrink.inflate_deflate]
  rfl

private def inclusiveLength (run : type_of% (@String.Slice.SplitInclusiveIterator.instIteratorLoopIdOfMonad.{0,0})) (g : Nat → Bool) (k : Nat) : Nat :=
  letI := countingSearcher g
  letI := @run Unit (fun _ => Nat) (countingSearcher g) () toForward Id inferInstance slice
  (inclusive k).length

/-- The same finite-searcher test applies when each output includes the delimiter. -/
def limitedOmniscienceFromInclusiveSplitLoop
    (run : type_of% (@String.Slice.SplitInclusiveIterator.instIteratorLoopIdOfMonad.{0,0}))
    (correct : ∀ {ρ : Type} {σ : String.Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)]
      (pat : ρ) [searcher : ToForwardSearcher pat σ] (s : String.Slice) [Finite (σ s) Id],
      letI := @run ρ σ _ pat searcher Id inferInstance s
      LawfulIteratorLoop (String.Slice.SplitInclusiveIterator pat s) Id Id)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply decisionFromDecreasingLength (inclusiveLength run) ?_ f
  intro g sticky ⟨n, hit⟩ k miss
  letI := countingSearcher g
  letI : Iterator Nat Id (SearchStep slice) := countingSearcher g slice
  letI : Finite (β := SearchStep slice) Nat Id := countingFinite sticky hit slice
  letI := @run Unit (fun _ => Nat) (countingSearcher g) () toForward Id inferInstance slice
  letI := @correct Unit (fun _ => Nat) (countingSearcher g) () toForward slice (countingFinite sticky hit slice)
  obtain ⟨b, step⟩ := inclusiveYield miss
  change (inclusive (k+1)).length < (inclusive k).length
  rw [Iter.length_eq_match_step (it := inclusive k), step]
  exact Nat.lt_succ_self _

private abbrev rev (k : Nat) : Iter (α := @String.Slice.RevSplitIterator (fun _ => Nat) Unit () slice toBackward) String.Slice :=
  ⟨.operating slice.startPos ⟨k⟩⟩
private theorem revYield {g : Nat → Bool} {k : Nat} (miss : g k = false) :
    letI := countingSearcher g
    letI := toBackward
    ∃ b, (rev k).step.val = .yield (rev (k+1)) b := by
  letI := countingSearcher g
  letI := toBackward
  refine ⟨slice.slice! slice.startPos slice.startPos, ?_⟩
  letI : Iterator Nat Id (SearchStep slice) := countingSearcher g slice
  have h := searchYield miss
  rw [Iter.step_eq]
  simp only [rev, Iter.toIterM_mk]
  generalize hs : (⟨k⟩ : Iter (α := Nat) (SearchStep slice)).step = step at *
  rcases step with ⟨v, hv⟩
  change v = _ at h
  cases h
  simp only [Id.run, pure, Shrink.inflate_deflate]
  rfl

private def revLength (run : type_of% (@String.Slice.RevSplitIterator.instIteratorLoopOfMonad.{0,0,0})) (g : Nat → Bool) (k : Nat) : Nat :=
  letI := countingSearcher g
  letI := @run Unit () (fun _ => Nat) (countingSearcher g) toBackward Id Id slice inferInstance inferInstance
  (rev k).length

/-- The identity-monad specialization of a reverse split loop suffices for the stream decision. -/
def limitedOmniscienceFromReverseSplitLoop
    (run : type_of% (@String.Slice.RevSplitIterator.instIteratorLoopOfMonad.{0,0,0}))
    (correct : ∀ {ρ : Type} {σ : String.Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)]
      (pat : ρ) [searcher : ToBackwardSearcher pat σ] (s : String.Slice) [Finite (σ s) Id],
      letI := @run ρ pat σ _ searcher Id Id s inferInstance inferInstance
      LawfulIteratorLoop (String.Slice.RevSplitIterator pat s) Id Id)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply decisionFromDecreasingLength (revLength run) ?_ f
  intro g sticky ⟨n, hit⟩ k miss
  letI := countingSearcher g
  letI : Iterator Nat Id (SearchStep slice) := countingSearcher g slice
  letI : Finite (β := SearchStep slice) Nat Id := countingFinite sticky hit slice
  letI := @run Unit () (fun _ => Nat) (countingSearcher g) toBackward Id Id slice inferInstance inferInstance
  letI := @correct Unit (fun _ => Nat) (countingSearcher g) () toBackward slice (countingFinite sticky hit slice)
  obtain ⟨b, step⟩ := revYield miss
  change (rev (k+1)).length < (rev k).length
  rw [Iter.length_eq_match_step (it := rev k), step]
  exact Nat.lt_succ_self _

end OmegaChecks.InitBoundaries.Collector

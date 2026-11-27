module
import all OmegaChecks.InitInventory.Collector
import all Init.Data.String.Pattern.Basic
import all Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop

public section

/-! Zero-width string matches and termination of the callback supplied to the default search loop. -/

namespace OmegaChecks.InitBoundaries.Collector
open Std Std.Iterators

private def stopOnSignal (g : Nat → Bool) (k : Nat) : ForInStep Nat :=
  if g k then .done k else .yield (k+1)

private abbrev signalStep {β : Type} (g : Nat → Bool) (_ : β) (k : Nat) (t : ForInStep Nat) :=
  t = stopOnSignal g k

private theorem signalWellFounded {α β : Type} [Iterator α Id β]
    (noSkip : ∀ i j : IterM (α := α) Id β, ¬i.IsPlausibleStep (.skip j))
    {g : Nat → Bool} (sticky : ∀ k, g k = true → g (k+1) = true) {n : Nat} (hit : g n = true) :
    IteratorLoop.WellFounded α Id (signalStep g) := by
  refine Subrelation.wf (r := InvImage Nat.lt (fun p : IterM (α := α) Id β × Nat => n - p.2)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro ⟨j, l⟩ ⟨i, k⟩ step
  obtain ⟨b, _, h⟩ | ⟨h, _⟩ := step
  · change ForInStep.yield l = stopOnSignal g k at h
    unfold stopOnSignal at h
    split at h
    · cases h
    · rename_i miss
      cases h
      have lt := Nat.lt_of_not_ge (fun ge => miss (signal_after sticky hit ge))
      change n - (k + 1) < n - k
      omega
  · exact (noSkip i j h).elim

private def signalRun {α β : Type} [Iterator α Id β] (run : IteratorLoop α Id Id)
    (it : IterM (α := α) Id β) (g : Nat → Bool) (k : Nat) : Nat :=
  run.forIn (fun _ _ fn x => fn x) Nat (signalStep g) it k fun _ _ i => ⟨stopOnSignal g i, rfl⟩

private theorem signalUnroll {α β : Type} [Iterator α Id β]
    {it : IterM (α := α) Id β} {out : β} (repeatStep : it.step.run.inflate.val = .yield it out)
    (g : Nat → Bool) (wf : IteratorLoop.WellFounded α Id (signalStep g)) (k : Nat) :
    signalRun .defaultImplementation it g k =
      if g k then k else signalRun .defaultImplementation it g (k+1) := by
  unfold signalRun
  unfold IteratorLoop.defaultImplementation
  dsimp only
  rw [IterM.DefaultConsumers.forIn'_eq_match_step _ wf]
  generalize eq : it.step = s at *
  generalize eq' : s.run.inflate = p at *
  rcases p with ⟨step, plausible⟩
  change step = .yield it out at repeatStep
  cases repeatStep
  dsimp only [Id.run] at eq'
  simp only [eq']
  cases e : g k <;> simp [stopOnSignal, e] <;> rfl

open String.Slice.Pattern

private def signalDecision {α β : Type} [Iterator α Id β] (run : IteratorLoop α Id Id)
    {it : IterM (α := α) Id β} {out : β} (repeats : it.step.run.inflate.val = .yield it out)
    (noSkip : ∀ i j : IterM (α := α) Id β, ¬i.IsPlausibleStep (.skip j))
    (correct : ∀ g, IteratorLoop.WellFounded α Id (signalStep g) → ∀ k,
      signalRun run it g k = signalRun .defaultImplementation it g k)
    (f : Nat → Bool) : Decidable (∃ k, f k = true) := by
  let g := seen f
  let result k := signalRun run it g k
  cases e : g (result 0) with
  | true => exact isTrue (hit_of_seen f _ e)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have found := seen_of_hit f n hit
    have wf := signalWellFounded noSkip (seenSticky f) found
    have unroll (k : Nat) : result k = if g k then k else result (k+1) := by
      have h := signalUnroll repeats g wf k
      rw [← correct g wf k, ← correct g wf (k+1)] at h
      exact h
    have terminates (k : Nat) : g (result k) = true := by
      generalize eq : n - k = fuel
      induction fuel generalizing k with
      | zero =>
        have yes := signal_after (seenSticky f) found (Nat.le_of_sub_eq_zero eq)
        rw [unroll, ite_eq_left yes]
        exact yes
      | succ fuel ih =>
        rw [unroll]
        split
        · assumption
        · exact ih (k+1) (by omega)
    exact Bool.noConfusion (e.symm.trans (terminates 0))

@[instance_reducible] private def emptyForward : ForwardPattern () where
  skipPrefix? s := some s.startPos

@[instance_reducible] private def emptyBackward : BackwardPattern () where
  skipSuffix? s := some s.endPos

private abbrev sample := "a".toSlice

private theorem forwardRepeats :
    letI := emptyForward
    let it := (ToForwardSearcher.DefaultForwardSearcher.iter () sample).toIterM
    it.step.run.inflate.val = .yield it (.matched sample.startPos sample.startPos) := by
  letI := emptyForward
  have h : sample.startPos ≠ sample.endPos := by decide
  dsimp only [ToForwardSearcher.DefaultForwardSearcher.iter, IterM.step, Iterator.step, Iter.toIterM,
    IterM.internalState_mk]
  rw [dite_eq_right h]
  dsimp only [ForwardPattern.skipPrefixOfNonempty?, Id.run_pure]
  simp only [Shrink.inflate_deflate]
  rw [String.Slice.Pos.ofSliceFrom_startPos]

private theorem backwardRepeats :
    letI := emptyBackward
    let it := (ToBackwardSearcher.DefaultBackwardSearcher.iter () sample).toIterM
    it.step.run.inflate.val = .yield it (.matched sample.endPos sample.endPos) := by
  letI := emptyBackward
  have h : sample.endPos ≠ sample.startPos := by decide
  dsimp only [ToBackwardSearcher.DefaultBackwardSearcher.iter, IterM.step, Iterator.step, Iter.toIterM,
    IterM.internalState_mk]
  rw [dite_eq_right h]
  dsimp only [BackwardPattern.skipSuffixOfNonempty?, Id.run_pure]
  simp only [Shrink.inflate_deflate]
  rw [String.Slice.Pos.ofSliceTo_endPos]


private instance : Internal.LawfulMonadLiftBindFunction (m := Id) (n := Id)
    (fun (_ _ : Type) fn x => fn x) := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A zero-width forward match can repeat at the same byte. Agreement with the official
loop on well-founded callbacks locates a signal in an arbitrary Boolean stream. -/
def limitedOmniscienceFromForwardSearchLoop
    (run : type_of% @ToForwardSearcher.DefaultForwardSearcher.instIteratorLoopIdSearchStep)
    (correct : ∀ {ρ : Type} (pat : ρ) {s : String.Slice} [inst : ForwardPattern pat],
      letI := @run ρ pat s inst
      LawfulIteratorLoop (ToForwardSearcher.DefaultForwardSearcher pat s) Id Id)
    (f : Nat → Bool) : Decidable (∃ k, f k = true) := by
  letI := emptyForward
  refine signalDecision (@run Unit () sample _) forwardRepeats (fun _ _ skip => skip) ?_ f
  intro g wf k
  letI := @run Unit () sample _
  letI := correct () (s := sample)
  exact LawfulIteratorLoop.lawful _ _ _ _ _ wf _

/-- A zero-width backward match repeats at the end of a nonempty string, even though the
string has finitely many byte positions. -/
def limitedOmniscienceFromBackwardSearchLoop
    (run : type_of% @ToBackwardSearcher.DefaultBackwardSearcher.instIteratorLoopIdSearchStep)
    (correct : ∀ {ρ : Type} (pat : ρ) {s : String.Slice} [inst : BackwardPattern pat],
      letI := @run ρ pat s inst
      LawfulIteratorLoop (ToBackwardSearcher.DefaultBackwardSearcher pat s) Id Id)
    (f : Nat → Bool) : Decidable (∃ k, f k = true) := by
  letI := emptyBackward
  refine signalDecision (@run Unit () sample _) backwardRepeats (fun _ _ skip => skip) ?_ f
  intro g wf k
  letI := @run Unit () sample _
  letI := correct () (s := sample)
  exact LawfulIteratorLoop.lawful _ _ _ _ _ wf _

end OmegaChecks.InitBoundaries.Collector

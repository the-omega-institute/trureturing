module
public import OmegaChecks.InitPort.Alternatives.Collect
public import OmegaChecks.InitPort.Alternatives.FiniteLoop
public import Init.Data.Slice.Array.Lemmas
import all OmegaChecks.InitPort.Alternatives.Collect
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
import all Init.Data.Slice.Array.Lemmas
import all Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop

/-! Evaluate pure folds by induction on the finite iterator and its current accumulator. -/
open Std Std.Iterators

namespace OmegaChecks.InitPort.Alternatives

private theorem finiteFold {α β : Type u} [Iterator α Id β] [Finite α Id]
    {γ : Type v} (f : γ → β → γ) (it : IterM (α := α) Id β) (init : γ)
    (P : β → Prop) (hp : ∀ b, it.IsPlausibleIndirectOutput b → P b) :
    finiteForIn (n := Id) (fun _ _ k x => k x.run) γ (fun _ _ _ => True) it init P hp
      (fun b _ acc => ⟨.yield (f acc b), trivial⟩) =
      (collectInto it #[]).toList.foldl f init := by
  induction it using (Finite.wf (α := α) (m := Id) (β := β)).induction generalizing init with
  | h it ih =>
    conv =>
      lhs
      unfold finiteForIn
      rw [WellFounded.fix_eq]
    dsimp only [PSigma.fst, PSigma.snd, Id.run]
    rw [collectList_eq]
    dsimp only [Id.run]
    cases it.step.inflate using PlausibleIterStep.casesOn with
    | yield next out plausible => exact ih next (IterM.isPlausibleSuccessorOf_of_yield plausible) _ _
    | skip next plausible => exact ih next (IterM.isPlausibleSuccessorOf_of_skip plausible) _ _
    | done _ => rfl

public theorem Subarray.foldl_toList {γ : Type v} {init : γ} {α : Type u} {s : Subarray α} {f : γ → α → γ} :
    (Std.Iter.Total.toList (_root_.Std.Slice.Internal.iter s).ensureTermination).foldl f init =
      @_root_.Std.Slice.foldl _ _ _ _ f init _ _ instIteratorLoopSubarrayIteratorIdOfMonad s := by
  change (collectInto (_root_.Std.Slice.Internal.iter s).toIterM #[]).toList.foldl f init = _
  let it := (_root_.Std.Slice.Internal.iter s).toIterM
  exact (finiteFold f it init it.IsPlausibleIndirectOutput (fun _ h => h)).symm

end OmegaChecks.InitPort.Alternatives

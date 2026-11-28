module
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import all Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Lemmas.Monadic.Basic
public import Init.Data.Iterators.Lemmas.Consumers.Loop

/-! Pure iterator consumers whose callbacks return immediately on the first output. -/

open Std Std.Iterators
namespace OmegaChecks.InitPort.Alternatives

private theorem firstWF {α β γ : Type w} [Iterator α Id β] [IteratorLoop α Id Id.{w}] [Productive α Id]
    (g : β → γ) : IteratorLoop.WellFounded α Id (fun b (_ : γ) s => s = ForInStep.done (g b)) :=
  IteratorLoop.wellFounded_of_productive (α := α) (m := Id) (fun h => h ▸ rfl)

private def firstWith {α β γ : Type w} [Iterator α Id β] [IteratorLoop α Id Id.{w}] [Productive α Id]
    (g : β → γ) (d : γ) (it : IterM (α := α) Id β) (P : β → Prop)
    (hp : ∀ b, it.IsPlausibleIndirectOutput b → P b) : γ :=
  IterM.DefaultConsumers.forIn'.wf (n := Id) (fun _ _ g x => g x.run) _ _ (firstWF g)
    it d P hp (fun b _ _ => pure ⟨.done (g b), rfl⟩)

private theorem firstWith_congr {α β γ : Type w} [Iterator α Id β] [IteratorLoop α Id Id.{w}] [Productive α Id]
    (g : β → γ) (d : γ) (it : IterM (α := α) Id β) (P Q : β → Prop)
    (hp : ∀ b, it.IsPlausibleIndirectOutput b → P b) (hq : ∀ b, it.IsPlausibleIndirectOutput b → Q b) :
    firstWith g d it P hp = firstWith g d it Q hq := by
  induction it using IterM.inductSkips with
  | step it ihs =>
    unfold firstWith
    rw [IterM.DefaultConsumers.forIn'.wf.eq_def, IterM.DefaultConsumers.forIn'.wf.eq_def]
    dsimp only
    cases it.step.run.inflate using PlausibleIterStep.casesOn
    · rfl
    · apply ihs <;> assumption
    · rfl

private theorem loop_eq_firstWith {α β γ : Type w} [Iterator α Id β] [IteratorLoop α Id Id.{w}]
    [Productive α Id] [h : LawfulIteratorLoop α Id Id.{w}] (g : β → γ) (d : γ) (it : IterM (α := α) Id β) :
    IteratorLoop.forIn (fun _ _ => flip Bind.bind) _ (fun b _ s => s = ForInStep.done (g b)) it d
      (fun b _ _ => pure ⟨ForInStep.done (g b), rfl⟩) =
      firstWith g d it (fun _ => True) (fun _ _ => trivial) := by
  let wf : IteratorLoop.WellFounded α Id (fun b (_ : γ) s => s = ForInStep.done (g b)) := firstWF g
  rw [h.lawful (fun _ _ => flip Bind.bind) _ it d _ wf]
  refine Eq.trans (b := firstWith g d it it.IsPlausibleIndirectOutput (fun _ => id)) ?_ ?_
  · exact IterM.DefaultConsumers.forIn'_eq_wf _ wf _
  · exact firstWith_congr _ _ _ _ _ _ _


public theorem Std.Iter.first?_eq_match_step : type_of% @_root_.Std.Iter.first?_eq_match_step := by
  intro α β iter loop productive laws it
  change IteratorLoop.forIn _ _ _ _ _ _ = _
  rw [loop_eq_firstWith]
  unfold firstWith
  rw [IterM.DefaultConsumers.forIn'.wf.eq_def]
  dsimp only [Iter.step]
  cases it.toIterM.step.run.inflate using PlausibleIterStep.casesOn with
  | yield next out h => rfl
  | skip next h => exact (loop_eq_firstWith some none next).symm
  | done h => rfl

public theorem Std.Iter.isEmpty_eq_match_step.{w} : type_of% @_root_.Std.Iter.isEmpty_eq_match_step.{w} := by
  intro α β iter loop productive laws it
  rw [Iter.isEmpty_eq_isEmpty_toIterM]
  unfold IterM.isEmpty
  change (IteratorLoop.forIn (α := α) (m := Id) (n := Id) _ _ _ _ _ _ : ULift.{w} Bool).down = _
  rw [loop_eq_firstWith]
  unfold firstWith
  rw [IterM.DefaultConsumers.forIn'.wf.eq_def]
  dsimp only [Iter.step]
  cases it.toIterM.step.run.inflate using PlausibleIterStep.casesOn with
  | yield next out h => rfl
  | skip next h => exact congrArg ULift.down (loop_eq_firstWith (fun _ => ULift.up false) (ULift.up true) next).symm
  | done h => rfl

end OmegaChecks.InitPort.Alternatives

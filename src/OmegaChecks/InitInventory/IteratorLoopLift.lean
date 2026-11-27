module
import all OmegaChecks.InitInventory.TransformerLaws
import all OmegaChecks.InitInventory.Traversal
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import all Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop

/-! A finite loop can observe how a continuation is lifted from the identity monad. -/

public section
open Std Std.Iterators
namespace OmegaChecks.InitBoundaries.IteratorLoopLift
open TransformerLaws.MapAfterBind
open IteratorLoopCongruence
universe u v

/-- Binding keeps the two inputs to a mapped function distinct until a reader is observed. -/
@[instance_reducible] private def readerMonad (T : Type u) : Monad (Paired T) where
  pure a := diagonal fun _ => a
  bind := bindPair

private theorem readerLawful (T : Type u) : letI := readerMonad T; LawfulMonad (Paired T) := by
  letI := readerMonad T
  exact {
    map_const := rfl
    id_map := by intros; rfl
    comp_map := by intros; rfl
    map_pure := by intros; rfl
    pure_seq := by intro _ _ f x; obtain ⟨_, rfl⟩ := diagonalExists x; rfl
    seq_pure := by intros; rfl
    seqLeft_eq := by intros; rfl
    seqRight_eq := by intros; rfl
    seq_assoc := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    pure_bind := by
      intro A B a k
      change diagonal (k a).val.2 = k a
      obtain ⟨r, hr⟩ := diagonalExists (k a)
      rw [hr]
      rfl
    bind_assoc := by intros; rfl
  }

@[instance_reducible] private def observing (T : Type u) :
    letI := itInst T
    letI := readerMonad T
    IteratorLoop State.{u} Id (Paired T) := by
  letI := itInst T
  letI := readerMonad T
  refine ⟨fun lift γ Pl it init k => diagonal (fun t => ?_)⟩
  cases active : it.internalState.down with
  | false => exact init
  | true =>
    have out : it.IsPlausibleIndirectOutput t :=
      .direct ⟨⟨⟨false⟩⟩, ⟨active, rfl⟩⟩
    -- The two lift implementations call the same continuation directly or through pure and bind.
    let effect := lift T _ (fun _ => k t out init) t
    exact ForInStep.casesOn (effect.val.1 t).val id id

private theorem endomorphisms (rule : type_of% @Std.Iter.forIn_eq_forIn_toIterM.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := itInst T
  letI := finite T
  letI := readerMonad T
  letI := readerLawful T
  letI := observing T
  let it : Iter (α := State.{u}) T := ⟨⟨true⟩⟩
  let k (t : T) (_ : Option T) : Paired T (ForInStep (Option T)) :=
    ⟨(fun _ => .done (some (f t)), fun _ => .done (some (g t))),
      congrArg (fun y (_ : T) => ForInStep.done (some y)) (agree t)⟩
  have eq := rule (it := it) (init := (none : Option T)) (f := k)
  exact congrArg (fun z : Paired T (Option T) => fun t => (z.val.1 t).getD t) eq

theorem funextOfForIn (law : type_of% @Std.Iter.forIn_eq_forIn_toIterM.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (endomorphisms law)

theorem funextOfForIn' (rule : type_of% @Std.Iter.forIn'_eq_forIn'_toIterM.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextOfForIn
  intro α β iterator finite m mon law loop γ it init f
  exact rule (it := it) (init := init) (f := fun b _ s => f b s)

private theorem foldEndomorphisms (rule : type_of% @Std.Iter.foldM_eq_foldM_toIterM.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := itInst T
  letI := finite T
  letI := readerMonad T
  letI := readerLawful T
  letI := observing T
  let it : Iter (α := State.{u}) T := ⟨⟨true⟩⟩
  let k (_ : Option T) (t : T) : Paired T (Option T) :=
    ⟨(fun _ => some (f t), fun _ => some (g t)), congrArg (fun y (_ : T) => some y) (agree t)⟩
  have eq := rule (it := it) (init := (none : Option T)) (f := k)
  exact congrArg (fun z : Paired T (Option T) => fun t => (z.val.1 t).getD t) eq

theorem funextOfFold (law : type_of% @Std.Iter.foldM_eq_foldM_toIterM.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (foldEndomorphisms law)

end OmegaChecks.InitBoundaries.IteratorLoopLift

module
import all Init.Data.Iterators.Consumers.Monadic.Loop
public import Init.Data.Slice.Array.Iterator
public import Init.Data.Iterators.Producers.Monadic.List
/-! Run the default loop by induction on the finite iterator, for arbitrary lifts and monads. -/

open Std Std.Iterators

namespace OmegaChecks.InitPort.Alternatives

private noncomputable def finiteForIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n] (lift : ∀ γ δ, (γ → n δ) → m γ → n δ)
    (γ : Type x) (Pl : β → γ → ForInStep γ → Prop) (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  let project (p : (i : IterM (α := α) m β) ×' (_ : γ) ×' (∀ b, i.IsPlausibleIndirectOutput b → P b)) :=
    (p.1, p.2.1)
  (InvImage.wf project (IteratorLoop.wellFounded_of_finite (P := Pl))).fix (C := fun _ => n γ)
    (fun p recur => (lift _ _ · p.1.step) fun step => do
      match step.inflate with
      | .yield next out h =>
        match ← f out (p.2.2 out (.direct ⟨_, h⟩)) p.2.1 with
        | ⟨.yield acc, h'⟩ =>
          recur ⟨next, acc, fun _ after => p.2.2 _ (.indirect ⟨_, rfl, h⟩ after)⟩ (Or.inl ⟨out, h, h'⟩)
        | ⟨.done acc, _⟩ => return acc
      | .skip next h =>
        recur ⟨next, p.2.1, fun _ after => p.2.2 _ (.indirect ⟨_, rfl, h⟩ after)⟩ (Or.inr ⟨h, rfl⟩)
      | .done _ => return p.2.1) ⟨it, init, hP⟩

@[instance_reducible] private noncomputable def finiteIteratorLoop {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n] : IteratorLoop α m n where
  forIn lift γ Pl it init := finiteForIn lift γ Pl it init _ (fun _ => id)

@[instance_reducible] public noncomputable def instIteratorLoopSubarrayIteratorIdOfMonad {α : Type u}
    {m : Type v → Type w} [Monad m] : IteratorLoop (SubarrayIterator α) Id m :=
  finiteIteratorLoop

@[instance_reducible] public noncomputable def Std.Iterators.Types.ListIterator.instIteratorLoop :
    type_of% @_root_.Std.Iterators.Types.ListIterator.instIteratorLoop :=
  fun {_ _} _ {_} _ => finiteIteratorLoop

end OmegaChecks.InitPort.Alternatives

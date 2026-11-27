module
public import Init.Data.Option.Monadic

namespace OmegaChecks.InitPort.Alternatives

@[instance_reducible] private def optionLoop
    {m : Type u → Type v} {α : Type w}
    [Monad m] : ForIn' m (Option α) α inferInstance where
  forIn' o init f := match o with
    | none => pure init
    | some a => f a rfl init >>= fun step => pure (ForInStep.value step)

@[instance_reducible] public def Option.instForIn'InferInstanceMembershipOfMonad
    {m : Type u → Type v} {α : Type w} [Monad m] : ForIn' m (Option α) α inferInstance :=
  optionLoop

attribute [local instance] Option.instForIn'InferInstanceMembershipOfMonad

public theorem Option.forIn'_some [Monad m] [LawfulMonad m] (a : α) (b : β)
    (f : (a' : α) → a' ∈ some a → β → m (ForInStep β)) :
    forIn' (some a) b f = bind (f a rfl b) (fun r => pure (ForInStep.value r)) := by rfl

public theorem Option.forIn_some [Monad m] [LawfulMonad m] (a : α) (b : β)
    (f : α → β → m (ForInStep β)) :
    forIn (some a) b f = bind (f a b) (fun r => pure (ForInStep.value r)) := by rfl

public theorem Option.forIn_join : type_of% @_root_.Option.forIn_join := by
  intro m α β init _ _ o f
  exact _root_.Option.forIn'_join init o (fun a _ b => f a b)

end OmegaChecks.InitPort.Alternatives

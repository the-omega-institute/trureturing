module
public import Init.Internal.Order.Basic
public import Init.Internal.Order.Lemmas

/-! Pointwise orders and monotone operations. -/

open _root_.Lean.Order

namespace OmegaChecks.InitPort.Alternatives.Lean.Order

public theorem monotone_bind (m : Type u → Type v) [Bind m] [∀ α, PartialOrder (m α)] [MonoBind m]
    {α β : Type u} {γ : Sort w} [PartialOrder γ]
    (f : γ → m α) (g : γ → α → m β) (hf : monotone f)
    (hg : ∀ x y : γ, x ⊑ y → ∀ a, g x a ⊑ g y a) :
    monotone fun x => f x >>= g x :=
  fun x y h => PartialOrder.rel_trans (MonoBind.bind_mono_left (hf x y h))
    (MonoBind.bind_mono_right (hg x y h))

public theorem monotone_of_monotone_apply {γ : Sort w} {α : Sort u} {β : α → Sort v}
    [PartialOrder γ] [∀ a, PartialOrder (β a)] (f : γ → ∀ a, β a)
    (hf : ∀ a, monotone (fun x => f x a)) :
    ∀ x y : γ, x ⊑ y → ∀ a, f x a ⊑ f y a :=
  fun x y h a => hf a x y h

public theorem monotone_apply {γ : Sort w} {α : Sort u} {β : α → Sort v}
    [PartialOrder γ] [∀ a, PartialOrder (β a)] (a : α) (f : γ → ∀ a, β a)
    (hf : ∀ x y : γ, x ⊑ y → ∀ i, f x i ⊑ f y i) :
    monotone fun x => f x a :=
  fun x y h => hf x y h a

public theorem monotone_dite {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β]
    (c : Prop) [d : Decidable c] (f : α → c → β) (g : α → ¬ c → β)
    (hf : ∀ x y : α, x ⊑ y → ∀ h, f x h ⊑ f y h)
    (hg : ∀ x y : α, x ⊑ y → ∀ h, g x h ⊑ g y h) :
    monotone fun x => dite c (f x) (g x) := by
  intro x y xy
  cases d with
  | isTrue h => exact hf x y xy h
  | isFalse h => exact hg x y xy h

public theorem Functor.monotone_map {m : Type u → Type v} [Monad m] [∀ t, PartialOrder (m t)] [MonoBind m]
    {α β : Type u} {γ : Type w} [PartialOrder γ] [LawfulMonad m]
    (f : γ → m α) (g : α → β) (hf : monotone f) : monotone fun x => g <$> f x := by
  intro x y xy
  change (g <$> f x) ⊑ (g <$> f y)
  rw [← bind_pure_comp g (f x), ← bind_pure_comp g (f y)]
  exact MonoBind.bind_mono_left (hf x y xy)

end OmegaChecks.InitPort.Alternatives.Lean.Order

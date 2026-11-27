module
prelude
public import OmegaInit.Control.StateRef

private abbrev liftState {σ : Type} : Omega.MonadLiftT (Omega.ST σ) (Omega.ST σ) :=
  ⟨fun action => action⟩

@[export omega_state_ref_write] public def write {σ α : Type} (a : α) (ref : Omega.ST.Ref σ α)
    (world : Omega.Void σ) : Omega.ST.Out σ Omega.Unit :=
  @Omega.StateRefT'.set σ α (Omega.ST σ) liftState a ref world

@[export omega_state_ref_new] public def allocate {σ α : Type} (a : α) (world : Omega.Void σ) :=
  @Omega.ST.mkRef σ (Omega.ST σ) liftState α a world

@[export omega_state_ref_swap] public def swap {σ α : Type} (a : α) (ref : Omega.ST.Ref σ α)
    (world : Omega.Void σ) := @Omega.ST.Ref.swap σ (Omega.ST σ) liftState α ref a world

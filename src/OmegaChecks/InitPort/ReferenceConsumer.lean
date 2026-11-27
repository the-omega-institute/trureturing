module
prelude
public import OmegaInit.System.ST

private abbrev liftState {σ : Type} : Omega.MonadLiftT (Omega.ST σ) (Omega.ST σ) :=
  ⟨fun action => action⟩

@[export omega_ref_smoke] public def allocateRef {σ α : Type} (a : α) (s : Omega.Void σ) :
    Omega.ST.Out σ (Omega.ST.Ref σ α) := @Omega.ST.mkRef σ (Omega.ST σ) liftState α a s

@[export omega_ref_swap_smoke] public def swapRef {σ α : Type} (r : Omega.ST.Ref σ α)
    (a : α) (s : Omega.Void σ) : Omega.ST.Out σ α :=
  @Omega.ST.Ref.swap σ (Omega.ST σ) liftState α r a s

@[export omega_ref_set_smoke] public def setRef {σ α : Type} (r : Omega.ST.Ref σ α)
    (a : α) (s : Omega.Void σ) : Omega.ST.Out σ Omega.Unit :=
  @Omega.ST.Ref.set σ (Omega.ST σ) liftState α r a s

@[export omega_ref_equal_smoke] public def equalRef {σ α : Type} (a b : Omega.ST.Ref σ α)
    (s : Omega.Void σ) : Omega.ST.Out σ Omega.Bool :=
  @Omega.ST.Ref.ptrEq σ (Omega.ST σ) liftState α a b s

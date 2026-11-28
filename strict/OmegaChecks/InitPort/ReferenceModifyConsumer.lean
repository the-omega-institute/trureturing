module
prelude
public import OmegaInit.System.ST

@[export omega_test_modify_unsafe]
public unsafe def modifyRef {σ α : Type} (ref : Omega.ST.Ref σ α) (f : α → α) (world : Omega.Void σ) :=
  Omega.ST.Prim.Ref.modifyUnsafe ref f world

module
prelude
public import OmegaInit.System.ST

@[export omega_test_primitive_ref_put]
public unsafe def primitivePut {σ α : Type} (ref : Omega.ST.Ref σ α) (value : α) (world : Omega.Void σ) :=
  Omega.ST.Prim.Ref.put ref value world

@[export omega_test_lifted_ref_put]
public unsafe def liftedPut {σ α : Type} (ref : Omega.ST.Ref σ α) (value : α) (world : Omega.Void σ) :=
  @Omega.ST.Ref.put σ (Omega.ST σ) ⟨fun action => action⟩ α ref value world

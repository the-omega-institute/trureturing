module
prelude
public import OmegaInit.System.ST

@[export omega_ref_smoke] public def allocateRef {σ α : Type} (a : α) (s : Omega.Void σ) :
    Omega.ST.Out σ (Omega.ST.Ref σ α) := Omega.ST.Prim.mkRef a s

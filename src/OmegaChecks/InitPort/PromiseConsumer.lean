module
prelude
public import OmegaInit.System.Promise

@[export omega_smoke_new] public def allocate {α : Type} (h : Omega.Nonempty α)
    (s : Omega.Void Omega.IO.RealWorld) : Omega.ST.Out Omega.IO.RealWorld (Omega.IO.Promise α) :=
  @Omega.IO.Promise.new α h s

@[export omega_smoke_resolve] public def resolve {α : Type} (x : α) (p : Omega.IO.Promise α)
    (s : Omega.Void Omega.IO.RealWorld) : Omega.ST.Out Omega.IO.RealWorld Omega.Unit :=
  Omega.IO.Promise.resolve x p s

module
prelude
public import OmegaInit.System.IO

@[export omega_test_persistent]
public unsafe def markPersistent {α : Type} (value : α) (world : Omega.Void Omega.IO.RealWorld) :=
  Omega.Runtime.markPersistent value world

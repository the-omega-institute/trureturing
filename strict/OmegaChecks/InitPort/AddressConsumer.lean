module
prelude
public import OmegaInit.Util

@[noinline]
public unsafe def omegaTestPointerAddress (value : @& Omega.List Nat) : Nat :=
  (Omega.ptrAddrUnsafe value).toNat

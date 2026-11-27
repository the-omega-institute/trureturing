module
prelude
public import OmegaInit.Util

@[noinline]
public unsafe def omegaTestExclusive (value : @& Omega.List Nat) : Omega.Bool :=
  Omega.isExclusiveUnsafe value

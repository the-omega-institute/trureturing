module
prelude
public import OmegaInit.Util

@[export omega_test_exclusive]
public unsafe def exclusive {α : Type} (value : @& α) : Omega.Bool :=
  Omega.isExclusiveUnsafe value

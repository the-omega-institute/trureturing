module
prelude
public import OmegaInit.ShareCommon

@[noinline] public unsafe def omegaTestPointerHash (x : @& Omega.ShareCommon.Object) : Omega.UInt64 :=
  Omega.ShareCommon.Object.ptrHash x

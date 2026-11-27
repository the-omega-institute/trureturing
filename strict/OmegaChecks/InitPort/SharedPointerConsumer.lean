module
prelude
public import OmegaInit.ShareCommon

@[noinline] public unsafe def omegaTestSharedPointer (x y : @& Omega.ShareCommon.Object) : Omega.Bool :=
  Omega.ShareCommon.Object.ptrEq x y

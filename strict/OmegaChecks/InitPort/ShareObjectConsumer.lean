module
prelude
public import OmegaInit.ShareCommon

@[noinline] public unsafe def omegaShareObjectEq (a b : @& Omega.ShareCommon.Object) : Omega.Bool :=
  Omega.ShareCommon.Object.eq a b

@[noinline] public unsafe def omegaShareObjectHash (a : @& Omega.ShareCommon.Object) : Nat :=
  (Omega.ShareCommon.Object.hash a).toNat

module
prelude
public import OmegaInit.Util

@[noinline] public unsafe def omegaTestPointerEq (x y : @& Omega.List Nat) : Omega.Bool :=
  Omega.ptrEq x y

@[noinline] public unsafe def omegaTestGuardedPointerEq (x y : @& Omega.List Nat) (k : Unit → Omega.Bool)
    (h : Eq x y → Eq (k ()) Omega.Bool.true) : Omega.Bool :=
  Omega.withPtrEqUnsafe x y k h

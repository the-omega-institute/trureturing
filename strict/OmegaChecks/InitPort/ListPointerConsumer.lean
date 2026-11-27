module
prelude
public import OmegaInit.Util

@[noinline] public unsafe def omegaTestListPointer (xs ys : @& Omega.List (Omega.List Nat)) : Omega.Bool :=
  Omega.ptrEqList xs ys

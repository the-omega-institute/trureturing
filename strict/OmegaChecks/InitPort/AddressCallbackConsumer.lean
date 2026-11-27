module
prelude
public import OmegaInit.Util

@[noinline] public unsafe def omegaTestAddressCallback (x : @& Omega.List Nat) (f : Omega.USize → Nat)
    (h : ∀ a b, Eq (f a) (f b)) : Nat := Omega.withPtrAddrUnsafe x f h

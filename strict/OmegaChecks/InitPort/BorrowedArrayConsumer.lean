module
prelude
public import OmegaInit.Data.Array.Basic

public unsafe def borrowedArrayGet := @Omega.Array.getInternalBorrowed
public unsafe def borrowedArrayGetChecked := @Omega.Array.get!InternalBorrowed
public unsafe def borrowedArrayUGet := @Omega.Array.ugetBorrowed

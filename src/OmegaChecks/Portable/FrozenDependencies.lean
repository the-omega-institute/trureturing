module
prelude
public import OmegaMathlib.Data.Nat.Fib.Basic
public import Init.Classical

/-! Exercise direct common-interface imports together with an official axiom. -/

namespace OmegaChecks.Portable.FrozenDependencies

private theorem privateFib :
    Omega.Eq (OmegaMathlib.Nat.fib Omega.Nat.zero) Omega.Nat.zero :=
  OmegaMathlib.Nat.fib_zero

public theorem mixedFib :
    Omega.Eq (OmegaMathlib.Nat.fib Omega.Nat.zero) Omega.Nat.zero :=
  Classical.choice (Nonempty.intro privateFib)

end OmegaChecks.Portable.FrozenDependencies

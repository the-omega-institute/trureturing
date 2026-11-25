module
public import Init.Core
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Exists Iff)
end Omega
namespace Omega.Exists
export _root_.Exists (elim intro rec)
end Omega.Exists
namespace Omega.Iff
export _root_.Iff (intro mp mpr rec)
end Omega.Iff
namespace Omega.Nat
export _root_.Nat (add_zero)
end Omega.Nat
namespace Omega.Nat.succ
export _root_.Nat.succ (inj)
end Omega.Nat.succ

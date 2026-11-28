module
public import Init.Data.Nat.Log2
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.log2.eq_1)
end Omega
namespace Omega.Nat
export _root_.Nat (log2 log2_def log2_le_self log2_terminates)
end Omega.Nat

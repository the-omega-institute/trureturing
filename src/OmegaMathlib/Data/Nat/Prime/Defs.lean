module
public import Mathlib.Data.Nat.Prime.Defs
public import OmegaInit.Data.Nat.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (Prime prime_def)
end Omega.Nat
namespace Omega.Nat.Prime
export _root_.Nat.Prime (eq_one_or_self_of_dvd one_lt two_le)
end Omega.Nat.Prime

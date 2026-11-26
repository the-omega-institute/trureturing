module
public import Mathlib.Data.Nat.Prime.Defs
public import OmegaInit.Data.Nat.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.Prime.eq_one_or_self_of_dvd Nat.Prime.one_lt Nat.Prime.two_le)
end Omega
namespace Omega.Nat
export _root_.Nat (Prime prime_def)
end Omega.Nat

module
public import Init.Data.Nat.Bitwise.Lemmas
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (and_lt_two_pow bitwise_lt_two_pow or_lt_two_pow)
end Omega.Nat

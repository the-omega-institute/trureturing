module
public import Init.Data.Nat.Bitwise.Basic
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.shiftLeft.match_1)
end Omega
namespace Omega.Nat
export _root_.Nat (bitwise land lor shiftRight testBit)
end Omega.Nat

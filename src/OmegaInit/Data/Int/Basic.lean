module
public import Init.Data.Int.Basic
public import OmegaInit.Data.Nat.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int Int.negOfNat.match_1)
end Omega
namespace Omega.Int
export _root_.Int (NonNeg add le lt mul natAbs neg negOfNat negSucc ofNat rec recOn sign sub subNatNat toNat)
end Omega.Int
namespace Omega.Int.NonNeg
export _root_.Int.NonNeg (mk rec recOn)
end Omega.Int.NonNeg

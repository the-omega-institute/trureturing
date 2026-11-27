module
public import Init.Data.Int.Basic
public import OmegaInit.Data.Nat.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int Int.negOfNat.match_1 Int.negSucc.noConfusion Int.ofNat.noConfusion)
end Omega
namespace Omega.Int
export _root_.Int (NonNeg add casesOn le lt mul natAbs neg negOfNat negSucc noConfusion noConfusionType ofNat rec recOn sign sub subNatNat toNat)
end Omega.Int
namespace Omega.Int.NonNeg
export _root_.Int.NonNeg (casesOn mk rec recOn)
end Omega.Int.NonNeg

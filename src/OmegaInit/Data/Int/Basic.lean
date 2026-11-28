module
public import Init.Data.Int.Basic
public import OmegaInit.Data.Cast
public import OmegaInit.Data.Nat.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int Int.add.match_1 Int.decEq.match_1 Int.neg.match_1 Int.negOfNat.match_1 Int.negSucc.noConfusion Int.ofNat.inj Int.ofNat.noConfusion Int.pow.match_1 instNatCastInt instOfNat)
end Omega
namespace Omega.Int
export _root_.Int (NonNeg add casesOn ctorIdx decEq decLe decLt decNonneg instAdd instDecidableEq instDvd instLEInt instLTInt instMul instNatPow instNegInt instSub le lt mul natAbs neg negOfNat negSucc noConfusion noConfusionType ofNat ofNat_zero pow rec recOn sign sub subNatNat toNat)
end Omega.Int
namespace Omega.Int.NonNeg
export _root_.Int.NonNeg (casesOn mk rec recOn)
end Omega.Int.NonNeg

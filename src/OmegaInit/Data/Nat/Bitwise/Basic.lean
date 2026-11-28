module
public import Init.Data.Nat.Bitwise.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.shiftLeft.match_1)
end Omega
namespace Omega.Nat
export _root_.Nat (bitwise bitwise_rec_lemma hasNotBit hasNotBit_eq instAndOp instOrOp instShiftLeft instShiftRight instXorOp land land_eq lor lor_eq shiftLeft shiftLeft_eq shiftLeft_eq' shiftRight shiftRight_add shiftRight_eq' shiftRight_eq_div_pow shiftRight_eq_zero shiftRight_le shiftRight_succ shiftRight_zero testBit xor xor_eq)
end Omega.Nat

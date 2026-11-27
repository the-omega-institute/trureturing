module
public import Init.Data.Nat.Gcd
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (gcd gcd_add_one gcd_one_left gcd_rec gcd_succ gcd_zero_left gcd_zero_right)
end Omega.Nat

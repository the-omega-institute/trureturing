module
public import Init.Data.Nat.Gcd
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (gcd gcd_add_one gcd_one_left gcd_one_right gcd_rec gcd_succ gcd_zero_left gcd_zero_right)
end Omega.Nat

module
public import Init.Data.Nat.Div.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Div.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (succ_div_of_mod_eq_zero succ_div_of_mod_ne_zero)
end Omega.Nat

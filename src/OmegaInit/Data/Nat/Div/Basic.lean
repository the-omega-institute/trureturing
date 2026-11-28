module
public import Init.Data.Nat.Div.Basic
public import OmegaInit.Core
public import OmegaInit.WF

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.mod.eq_2)
end Omega
namespace Omega.Nat
export _root_.Nat (add_div_right add_mod_right add_mul_div_left add_mul_div_right add_mul_mod_self_left div_add_mod div_div_eq_div_mul div_eq_ite div_eq_of_lt div_eq_of_lt_le div_eq_sub_div div_le_self div_lt_iff_lt_mul div_lt_self div_mul_le_self div_one div_zero instDvd le_div_iff_mul_le modCore_eq modCore_eq_mod mod_add_div mod_def mod_eq_ite mod_eq_of_lt mod_eq_sub_div_mul mod_eq_sub_mod mod_eq_sub_mul_div mod_le mod_one mod_zero mul_div_cancel mul_div_le mul_mod_left mul_mod_right mul_sub_div sub_mul_div_of_le zero_div zero_mod)
end Omega.Nat

namespace Omega.Nat
export _root_.Nat (div_self mod_self mul_div_cancel_left mul_mod_mul_left)
end Omega.Nat

namespace Omega.Nat
export _root_.Nat (add_mul_mod_self_right)
end Omega.Nat

namespace Omega.Nat
export _root_.Nat (add_mod_left div_eq_of_eq_mul_right div_le_of_le_mul mul_div_left mul_div_mul_left
  mul_div_right)
end Omega.Nat

module
public import Init.SimpLemmas
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (and_assoc and_congr_left and_congr_right and_iff_left_iff_imp and_iff_left_of_imp and_iff_right_iff_imp and_iff_right_of_imp and_imp and_not_self and_self_left and_self_right forall_prop_congr_dom have_body_congr' have_body_congr_dep' have_unused' have_unused_dep' have_val_congr' iff_congr implies_congr implies_congr_left implies_congr_right let_val_congr ne_eq not_and not_and_self not_iff_self of_eq_false of_eq_true or_assoc or_iff_left_iff_imp or_iff_left_of_imp or_iff_right_of_imp or_self_left or_self_right)
end Omega
namespace Omega.Bool
export _root_.Bool (false_and false_or not_false not_true true_and true_or)
end Omega.Bool
namespace Omega.Eq
export _root_.Eq (mpr_not mpr_prop)
end Omega.Eq
namespace Omega.Or
export _root_.Or (imp imp_left imp_right)
end Omega.Or

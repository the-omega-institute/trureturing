module
public import Init.Data.Ord.Basic
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Ordering Ordering.isLE.match_1 Ordering.isLT.match_1 Ordering.then'.eq_1 Ordering.then.eq_1 Ordering.then.match_1 compareLex compareLex.eq_1 compareLex_eq_eq)
end Omega
namespace Omega.Ordering
export _root_.Ordering (casesOn ctorIdx eq eq_eq_iff_isLE_and_isGE eq_eq_of_eq_swap eq_eq_of_isGE_of_isGE_swap eq_eq_of_isLE_of_isGE eq_eq_of_isLE_of_isLE_swap eq_swap_iff_eq_eq eq_then gt gt_then isEq isEq_eq isEq_eq_false isEq_gt isEq_iff_eq_eq isEq_lt isEq_swap isEq_then isGE isGE_eq isGE_eq_false isGE_eq_isGT_or_isEq isGE_gt isGE_iff_eq_gt_or_eq_eq isGE_iff_ne_lt isGE_left_of_isGE_then isGE_lt isGE_of_eq_eq isGE_of_eq_gt isGE_swap isGT isGT_eq isGT_gt isGT_iff_eq_gt isGT_lt isGT_swap isGT_then isLE isLE_and_isGE_eq isLE_eq isLE_eq_false isLE_eq_isLT_or_isEq isLE_gt isLE_iff_eq_lt_or_eq_eq isLE_iff_ne_gt isLE_left_of_isLE_then isLE_lt isLE_of_eq_eq isLE_of_eq_lt isLE_swap isLE_then_iff_and isLE_then_iff_or isLT isLT_eq isLT_gt isLT_iff_eq_lt isLT_lt isLT_swap isLT_then isNe isNe_eq isNe_eq_false isNe_eq_isLT_or_isGT isNe_gt isNe_iff_ne_eq isNe_lt isNe_swap isNe_then lt lt_then ne_eq_of_eq_gt ne_eq_of_eq_lt ne_gt_iff_isLE ne_lt_iff_isGE not_isEq_eq_isNe not_isGE_eq_isLT not_isGT_eq_isLE not_isLE_eq_isGT not_isLT_eq_isGE not_isNe_eq_isEq rec recOn swap swap_eq swap_eq_eq swap_eq_gt swap_eq_lt swap_gt swap_inj swap_lt swap_swap swap_then then' then'_eq_then then_assoc then_eq then_eq_eq then_eq_gt then_eq_lt then_self «exists» «forall» «then»)
end Omega.Ordering

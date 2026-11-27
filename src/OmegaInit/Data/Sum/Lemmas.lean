module
public import Init.Data.Sum.Lemmas
public import OmegaInit.Data.Sum.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Sum.getLeft?.eq_1 Sum.getLeft?.eq_2 Sum.getRight?.eq_1 Sum.getRight?.eq_2 Sum.isLeft.eq_1 Sum.isLeft.eq_2 Sum.isRight.eq_1 Sum.isRight.eq_2)
end Omega
namespace Omega.Sum
export _root_.Sum (bnot_isLeft bnot_isRight elim_comp_inl elim_comp_inr elim_map getLeft?_map getLeft?_swap getRight?_map getRight?_swap isLeft_map isLeft_swap isRight_map isRight_swap map_map swap_swap «exists» «forall»)
end Omega.Sum

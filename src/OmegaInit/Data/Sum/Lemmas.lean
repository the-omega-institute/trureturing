module
public import Init.Data.Sum.Lemmas
public import OmegaInit.Data.Sum.Basic
public import OmegaInit.WF
public import OmegaInit.SimpLemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Sum.getLeft?.eq_1 Sum.getLeft?.eq_2 Sum.getRight?.eq_1 Sum.getRight?.eq_2 Sum.isLeft.eq_1 Sum.isLeft.eq_2 Sum.isRight.eq_1 Sum.isRight.eq_2)
end Omega
namespace Omega.Sum
export _root_.Sum (elim_eq_iff eq_left_getLeft_of_isLeft eq_right_getRight_of_isRight getLeft_eq_iff getRight_eq_iff getLeft?_eq_some_iff getRight?_eq_some_iff getLeft?_eq_none_iff getRight?_eq_none_iff inl_getLeft inr_getRight isLeft_eq_false isRight_eq_false isLeft_iff isRight_iff not_isLeft not_isRight inl_ne_inr inr_ne_inl lex_acc_inl lex_acc_inr lex_wf liftRel_subrelation_lex liftRel_swap_iff bnot_isLeft bnot_isRight elim_comp_inl elim_comp_inr elim_map getLeft?_map getLeft?_swap getRight?_map getRight?_swap isLeft_map isLeft_swap isRight_map isRight_swap map_map swap_swap «exists» «forall»)
end Omega.Sum
namespace Omega.Sum.Lex
export _root_.Sum.Lex (mono mono_left mono_right)
end Omega.Sum.Lex
namespace Omega.Sum.LiftRel
export _root_.Sum.LiftRel (lex mono mono_left mono_right swap)
end Omega.Sum.LiftRel
namespace Omega.Sum.inl
export _root_.Sum.inl (inj_iff)
end Omega.Sum.inl
namespace Omega.Sum.inr
export _root_.Sum.inr (inj_iff)
end Omega.Sum.inr

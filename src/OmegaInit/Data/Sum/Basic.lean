module
public import Init.Data.Sum.Basic
public import OmegaInit.Core
public import OmegaInit.PropLemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Sum
export _root_.Sum (Lex LiftRel instDecidableLiftRel instDecidableRelSumLex lex_inl_inl lex_inr_inl lex_inr_inr liftRel_inl_inl liftRel_inr_inr not_liftRel_inl_inr not_liftRel_inr_inl elim elim_inl elim_inr getLeft getLeft_inl getLeft? getLeft?_inl getLeft?_inr getRight getRight_inr getRight? getRight?_inl getRight?_inr isLeft isLeft_inl isLeft_inr isRight isRight_inl isRight_inr map map_inl map_inr swap swap_inl swap_inr)
end Omega.Sum
namespace Omega.Sum.Lex
export _root_.Sum.Lex (casesOn inl inr rec recOn sep)
end Omega.Sum.Lex
namespace Omega.Sum.LiftRel
export _root_.Sum.LiftRel (casesOn inl inr rec recOn)
end Omega.Sum.LiftRel
namespace Omega.Sum.instDecidableLiftRel
export _root_.Sum.instDecidableLiftRel (match_1)
end Omega.Sum.instDecidableLiftRel
namespace Omega.Sum.instDecidableRelSumLex
export _root_.Sum.instDecidableRelSumLex (match_1)
end Omega.Sum.instDecidableRelSumLex
namespace Omega.Sum.getLeft
export _root_.Sum.getLeft (congr_simp)
end Omega.Sum.getLeft
namespace Omega.Sum.getRight
export _root_.Sum.getRight (congr_simp)
end Omega.Sum.getRight

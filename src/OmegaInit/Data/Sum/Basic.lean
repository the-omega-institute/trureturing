module
public import Init.Data.Sum.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Sum
export _root_.Sum (elim elim_inl elim_inr getLeft? getLeft?_inl getLeft?_inr getRight? getRight?_inl getRight?_inr isLeft isLeft_inl isLeft_inr isRight isRight_inl isRight_inr map map_inl map_inr swap swap_inl swap_inr)
end Omega.Sum

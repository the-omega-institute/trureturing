module
public import Init.Data.List.Monadic
public import OmegaInit.Data.List.Control

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.zipWithM'.match_1)
end Omega
namespace Omega.List
export _root_.List (zipWithM' zipWithM'_cons_cons zipWithM'_nil_left zipWithM'_nil_right zipWithM_nil_left zipWithM_nil_right)
end Omega.List

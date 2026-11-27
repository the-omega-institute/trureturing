module
public import Init.Data.List.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.List.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.headD.eq_1 List.headD.eq_2 absurd.congr_simp)
end Omega
namespace Omega.List
export _root_.List (exists_cons_of_ne_nil head?_singleton tailD_eq_tail? tail_eq_tailD)
end Omega.List

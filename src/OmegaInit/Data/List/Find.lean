module
public import Init.Data.List.Find
public import OmegaInit.Data.List.Attach
public import OmegaInit.Data.List.Basic
public import OmegaInit.Data.Option.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.List
export _root_.List (finIdxOf?_nil find?_cons_of_neg find?_cons_of_pos findFinIdx?_nil findIdx?_nil findSome?_cons_of_isNone findSome?_cons_of_isSome idxOf?_nil)
end Omega.List

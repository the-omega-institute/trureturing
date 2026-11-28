module
public import Init.Data.List.Control
public import OmegaInit.Control.Basic
public import OmegaInit.Data.List.Basic
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.findSomeM?_cons.match_1 List.forM.match_1 List.mapM.loop List.mapM.match_1 List.zipWithM.loop List.zipWithM.match_1)
end Omega
namespace Omega.List
export _root_.List (allM anyM findM? findSomeM? findSomeM?_cons findSomeM?_nil firstM forA forM mapA mapM zipWithM)
end Omega.List

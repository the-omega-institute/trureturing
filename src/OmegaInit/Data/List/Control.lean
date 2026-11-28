module
public import Init.Data.List.Control
public import OmegaInit.Control.Basic
public import OmegaInit.Data.List.Basic
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.filterMapM.loop List.filterMapM.match_1 List.findSomeM?_cons.match_1 List.flatMapM.loop List.flatMapM.match_1 List.foldlM.match_1 List.forIn'.loop List.forIn'.loop.match_1 List.forIn'.loop.match_3 List.forIn'.loop.match_5 List.forM.match_1 List.mapM.loop List.mapM.match_1 List.zipWithM.loop List.zipWithM.match_1)
end Omega
namespace Omega.List
export _root_.List (allM anyM filterAuxM filterM filterMapM filterRevM findM? findSomeM? findSomeM?_cons findSomeM?_nil firstM flatMapM foldlM foldlM_cons foldlM_nil foldrM foldrM_nil forA forIn' forIn'_eq_forIn' forIn'_nil forIn_nil forM forM_cons forM_eq_forM forM_nil instForIn'InferInstanceMembershipOfMonad instForMOfMonad instFunctor mapA mapM zipWithM)
end Omega.List

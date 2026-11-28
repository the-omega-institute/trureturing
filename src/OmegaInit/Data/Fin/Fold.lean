module
public import Init.Data.Fin.Fold
public import OmegaInit.Data.Fin.Basic

public section
namespace Omega
export _root_ (Fin.foldl.match_1 Fin.foldl.eq_1 Fin.foldl.eq_2)
end Omega
namespace Omega.Fin
export _root_.Fin (foldl foldl_zero foldl_succ foldlM_succ_last foldrM_succ foldlM_add foldrM_add)
end Omega.Fin

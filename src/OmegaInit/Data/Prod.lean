module
public import Init.Data.Prod
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Prod
export _root_.Prod (fst_swap instLawfulBEq instReflBEq map_comp_map map_comp_swap map_id map_id' map_map snd_swap swap swap_inj swap_prod_mk swap_swap swap_swap_eq «exists» «forall»)
end Omega.Prod

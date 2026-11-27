module
public import Init.Data.Option.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.Option.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Function.comp.eq_1 Option.bind.eq_1 Option.bind.eq_2 Option.le.eq_1 Option.le.eq_2 Option.le.eq_3 Option.le.eq_4 Option.lt.eq_1 Option.lt.eq_2)
end Omega
namespace Omega.Option
export _root_.Option (all_map any_map any_true bind_assoc bind_comm bind_fun_none bind_fun_some bind_id_eq_join elim_none elim_some eq_none_or_eq_some ext ext_iff getD_map getD_of_ne_none isNone_bind isNone_or isSome_bind isSome_or map_eq_bind map_or merge_none_left merge_none_right merge_some_some none_or orElse_eq_or or_assoc or_eq_bif or_eq_orElse or_none or_self or_some pmap_pred_congr some_or toList_none toList_some «exists» «forall»)
end Omega.Option

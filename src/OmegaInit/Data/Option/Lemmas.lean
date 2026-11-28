module
public import Init.Data.Option.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.Option.Instances

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Function.comp.eq_1 Option.bind.eq_1 Option.bind.eq_2 Option.le.eq_1 Option.le.eq_2 Option.le.eq_3 Option.le.eq_4 Option.lt.eq_1 Option.lt.eq_2)
end Omega
namespace Omega.Option
export _root_.Option (
  all_map any_map any_true bind_apply bind_assoc bind_comm bind_eq_bind
  bind_fun_none bind_fun_some bind_guard bind_id_eq_join default_eq_none elim_none elim_some
  eq_none_or_eq_some eq_some_of_isSome ext ext_iff filter_none filter_some filter_some_pos
  getD_map getD_of_ne_none get_bind get_congr get_eq_getD get_mem get_of_eq_some
  get_of_mem guard_apply guard_def guard_eq_filter guard_eq_ite guard_false guard_true
  isEqSome_eq_beq_some isNone_bind isNone_or isSome_apply_of_isSome_bind isSome_bind isSome_of_any isSome_of_eq_some
  isSome_of_isSome_bind isSome_of_mem isSome_or map_apply map_dif map_dite map_eq_bind
  map_eq_map map_if map_ite map_or mem_map_of_mem mem_some mem_some_iff mem_some_self merge_max
  merge_none_left merge_none_right merge_some_some none_beq_none none_beq_some none_le none_lt_some
  none_or not_comp_isSome not_isSome not_mem_none orElse_apply orElse_eq_or orElse_eq_orElse
  or_assoc or_eq_bif or_eq_orElse or_none or_self or_some pmap_pred_congr
  pure_apply pure_def some_beq_none some_beq_some some_le_some some_lt_some some_ne_none
  some_or toArray_none toArray_some toList_none toList_some «exists» «forall»)
end Omega.Option

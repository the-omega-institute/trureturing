module
public import Init.Data.Array.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.Array.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Option.getD.eq_1 Option.getD.eq_2)
end Omega
namespace Omega.Array
export _root_.Array (eq_empty_of_size_eq_zero length_toList map_append map_empty map_eq_empty_iff map_id map_id' map_id'' map_map map_push map_singleton singleton_eq_toArray_singleton size_append size_map toList_eq_nil_iff toList_inj toList_map)
end Omega.Array
namespace Omega.List
export _root_.List (map_toArray)
end Omega.List

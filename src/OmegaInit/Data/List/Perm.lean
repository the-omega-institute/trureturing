module
public import Init.Data.List.Perm
public import OmegaInit.Data.List.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.isEmpty.eq_1 List.isEmpty.eq_2)
end Omega
namespace Omega.List
export _root_.List (concat_perm nil_perm not_perm_cons_nil not_perm_nil_cons perm_append_comm perm_append_comm_assoc perm_append_singleton perm_comm perm_middle perm_nil reverse_perm)
end Omega.List
namespace Omega.List.Perm
export _root_.List.Perm (append append_cons append_left append_right congr_left congr_right eq_nil length_eq map nil_eq of_eq recOnSwap' refl rfl swap' symm)
end Omega.List.Perm

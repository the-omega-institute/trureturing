module
public import Init.Data.Nat.MinMax
public import OmegaInit.Data.Nat.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (add_max_add_left add_max_add_right add_min_add_left add_min_add_right instCommutativeMax instCommutativeMin le_max_left le_max_right le_min le_min_of_le_of_le lt_min max_comm max_eq_left max_eq_max max_eq_right max_le max_le_of_le_of_le max_lt max_zero min_comm min_eq_left min_eq_min min_eq_right min_le_left min_le_right min_zero mul_max_mul_left mul_max_mul_right mul_min_mul_left mul_min_mul_right zero_max zero_min)
end Omega.Nat

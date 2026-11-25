module
public import Mathlib.Data.Nat.Choose.Basic
public import OmegaInit.Data.Nat.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (choose choose_succ_succ choose_zero_right choose_zero_succ)
end Omega.Nat

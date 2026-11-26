module
import all Init.Data.Nat.Fold

/-! Transport along equal indices while unfolding a dependent natural-number fold. -/

open Nat

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.dfoldCast_eq_dfoldCast_iff :
    type_of% (private_decl% @_root_.Nat.dfoldCast_eq_dfoldCast_iff) := by
  intros
  exact ⟨fun _ => Subsingleton.elim .., fun h => h ▸ rfl⟩

public theorem Nat.dfold_loop_succ :
    type_of% (private_decl% @_root_.Nat.dfold_loop_succ) := by
  intro n j α f a w
  induction j with
  | zero =>
    simp only [Nat.dfold.loop, Nat.sub_zero, Nat.dfoldCast_rfl]
    rfl
  | succ j ih =>
    rw [Nat.dfold.loop, ih _ (by omega)]
    congr 2
    simp only [Nat.succ_eq_add_one, Nat.dfoldCast_trans]
    rw [Nat.apply_dfoldCast (h := by omega) f]
    erw [Nat.dfoldCast_trans (h := by omega)]
    rfl

public theorem Nat.dfold_succ : type_of% @_root_.Nat.dfold_succ := by
  intro n α f init
  unfold Nat.dfold
  rw [_root_.Nat.dfold_loop_succ (w := Nat.le_refl _)]
  congr 2
  simp only [Nat.dfoldCast_trans]
  rfl

public theorem Nat.dfold_add : type_of% @_root_.Nat.dfold_add := by
  intro n m α f init
  induction m with
  | zero => rw [Nat.dfold_zero]; rfl
  | succ m ih =>
    simp only [Nat.add_succ, Nat.dfold_succ, ih, -eq_self]
    rfl

end OmegaChecks.InitPort.Alternatives

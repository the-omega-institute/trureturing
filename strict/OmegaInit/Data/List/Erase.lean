module
prelude
public import OmegaInit.Data.List.Basic
import OmegaInit.Data.Nat.Basic
import all OmegaInit.Data.List.Basic
import all OmegaInit.Prelude

@[expose] public section

namespace Omega.List


theorem length_eraseIdx_of_lt {α : Type u} {l : List α} {i : Nat} (h : Nat.lt i l.length) :
    Eq (l.eraseIdx i).length (Nat.sub l.length Nat.zero.succ) :=
  (List.rec (motive := fun xs => ∀ j, Nat.lt j xs.length →
      Eq (xs.eraseIdx j).length (Nat.sub xs.length Nat.zero.succ))
    (fun j bound => False.elim (Nat.not_succ_le_zero j bound))
    (fun a tail ih j => Nat.casesOn (motive := fun j => Nat.lt j (cons a tail).length →
        Eq ((cons a tail).eraseIdx j).length (Nat.sub (cons a tail).length Nat.zero.succ)) j
      (fun _ => (Nat.add_one_sub_one tail.length).symm)
      (fun k bound =>
        have fits : Nat.lt k tail.length := Nat.le_of_succ_le_succ bound
        have nonzero : Ne tail.length Nat.zero := fun e =>
          Nat.not_succ_le_zero k (Eq.subst (motive := Nat.lt k) e fits)
        (congrArg Nat.succ (ih k fits)).trans
          ((Nat.succ_pred_eq_of_ne_zero nonzero).trans (Nat.add_one_sub_one tail.length).symm))) l) i h

end Omega.List

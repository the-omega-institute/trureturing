module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Div.Basic
import OmegaInit.Data.Nat.Basic
import all OmegaInit.Prelude

@[expose] public section

namespace Omega.Nat


theorem succ_div_of_mod_ne_zero {a b : Nat} (h : Ne (Nat.mod (Nat.add a (succ zero)) b) zero) :
    Eq (Nat.div (Nat.add a (succ zero)) b) (Nat.div a b) :=
  Nat.casesOn (motive := fun b => Ne (Nat.mod (succ a) b) zero → Eq (Nat.div (succ a) b) (Nat.div a b)) b
    (fun _ => (Nat.div_zero (succ a)).trans (Nat.div_zero a).symm)
    (fun d nonzero =>
      let k := succ d
      let q := Nat.div (succ a) k
      let r := Nat.mod (succ a) k
      have pos : Nat.lt zero k := succ_le_succ (zero_le d)
      have remPos : Nat.lt zero r := Nat.lt_of_not_ge (fun bound => nonzero (Nat.le_antisymm bound (zero_le r)))
      have small : Nat.lt (Nat.mul k q) (succ a) :=
        Eq.subst (motive := Nat.lt (Nat.mul k q)) (div_add_mod (succ a) k)
          (Nat.add_le_add_left remPos (Nat.mul k q))
      have upper : Nat.le q (Nat.div a k) := (le_div_iff_mul_le pos).mpr
        (Eq.subst (motive := fun t => Nat.le t a) (Nat.mul_comm k q) (le_of_succ_le_succ small))
      Nat.le_antisymm upper ((le_div_iff_mul_le pos).mpr (Nat.le.step (div_mul_le_self a k)))) h

theorem succ_div_of_mod_eq_zero {a b : Nat} (h : Eq (Nat.mod (Nat.add a (succ zero)) b) zero) :
    Eq (Nat.div (Nat.add a (succ zero)) b) (Nat.add (Nat.div a b) (succ zero)) :=
  Nat.casesOn (motive := fun b => Eq (Nat.mod (succ a) b) zero →
      Eq (Nat.div (succ a) b) (succ (Nat.div a b))) b
    (fun h => False.elim (succ_ne_zero a ((mod_zero (succ a)).symm.trans h)))
    (fun d h =>
      let k := succ d
      let q := Nat.div (succ a) k
      let prior := Nat.div a k
      have pos : Nat.lt zero k := succ_le_succ (zero_le d)
      have exactProd : Eq (Nat.mul q k) (succ a) :=
        (Nat.mul_comm q k).trans ((congrArg (fun r => Nat.add (Nat.mul k q) r) h.symm).trans (div_add_mod (succ a) k))
      have lower : Nat.lt prior q := (div_lt_iff_lt_mul pos).mpr
        (Eq.subst (motive := Nat.lt a) exactProd.symm (Nat.le_refl (succ a)))
      have blocked : Not (Nat.le (succ (succ prior)) q) := fun higher =>
        have productLe : Nat.le (Nat.mul (succ (succ prior)) k) (succ a) :=
          Eq.subst (motive := Nat.le (Nat.mul (succ (succ prior)) k)) exactProd (mul_le_mul_right k higher)
        have beyond : Nat.lt (Nat.mul (succ prior) k) (Nat.mul (succ (succ prior)) k) :=
          Eq.subst (motive := Nat.lt (Nat.mul (succ prior) k)) (succ_mul (succ prior) k).symm
            (Nat.add_le_add_left pos (Nat.mul (succ prior) k))
        Nat.lt_irrefl prior ((le_div_iff_mul_le pos).mpr (le_of_succ_le_succ (Nat.le_trans beyond productLe)))
      Nat.le_antisymm (le_of_succ_le_succ (Nat.lt_of_not_ge blocked)) lower) h

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (succ_div_of_mod_eq_zero succ_div_of_mod_ne_zero)
end Nat

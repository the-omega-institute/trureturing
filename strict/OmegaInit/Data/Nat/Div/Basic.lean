/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Core
import OmegaInit.Data.Nat.Basic
import all OmegaInit.Prelude

public section
namespace Omega.Nat

attribute [local semireducible] Nat.div Nat.modCore

theorem mod_zero (a : Nat) : Eq (Nat.mod a zero) a :=
  Nat.rec (motive := fun k => Eq (Nat.mod k zero) k) Omega.rfl (fun _ _ => Omega.rfl) a

theorem mod_one (x : Nat) : Eq (Nat.mod x (succ zero)) zero :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ (Nat.mod_lt x (Nat.le_refl (succ zero)))) (Nat.zero_le _)

protected theorem div_zero (n : Nat) : Eq (Nat.div n zero) zero := Omega.rfl

protected theorem zero_div (b : Nat) : Eq (Nat.div zero b) zero :=
  Nat.casesOn (motive := fun d => Eq (Nat.div zero d) zero) b Omega.rfl (fun _ => Omega.rfl)

/-- The fuel counter used by division with a positive divisor. -/
private noncomputable def quotient (d fuel n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => zero)
    (fun _ prior n => Bool.rec zero (succ (prior (Nat.sub n (succ d)))) (Nat.ble (succ d) n)) fuel n

private theorem belowDivisor {k n : Nat} (hk : Not (Nat.le k n)) (q : Nat) :
    Iff (Nat.le q zero) (Nat.le (Nat.mul q k) n) :=
  Nat.casesOn (motive := fun x => Iff (Nat.le x zero) (Nat.le (Nat.mul x k) n)) q
    (Iff.intro (fun _ => Eq.subst (motive := fun x => Nat.le x n) (Nat.zero_mul k).symm (zero_le n))
      (fun _ => Nat.le_refl zero))
    (fun x => Iff.intro (fun h => False.elim (not_succ_le_zero x h))
      (fun h => False.elim (hk (Nat.le_trans (le_add_left k (Nat.mul x k))
        (Eq.subst (motive := fun z => Nat.le z n) (succ_mul x k) h)))))

private theorem sub_lt_fuel {n d fuel : Nat} (fits : Nat.le (succ d) n) (bound : Nat.lt n (succ fuel)) :
    Nat.lt (Nat.sub n (succ d)) fuel :=
  Nat.le_trans (sub_succ_lt_self n d fits)
    (Nat.le_trans (sub_le_of_le_add (le_add_right n d)) (le_of_succ_le_succ bound))

private theorem quotient_bound (d fuel : Nat) : ∀ n, Nat.lt n fuel → ∀ q,
    Iff (Nat.le q (quotient d fuel n)) (Nat.le (Nat.mul q (succ d)) n) :=
  Nat.rec (motive := fun fuel => ∀ n, Nat.lt n fuel → ∀ q,
      Iff (Nat.le q (quotient d fuel n)) (Nat.le (Nat.mul q (succ d)) n))
    (fun n h _ => False.elim (not_succ_le_zero n h))
    (fun fuel ih n bound q =>
      let k := succ d
      let next := quotient d fuel (Nat.sub n k)
      let result := fun bit => Bool.rec (motive := fun _ => Nat) zero (succ next) bit
      Bool.casesOn (motive := fun bit => Eq (Nat.ble k n) bit →
          Iff (Nat.le q (result bit)) (Nat.le (Nat.mul q k) n)) (Nat.ble k n)
        (fun e => belowDivisor (fun h => Bool.ne_false_of_eq_true (ble_eq_true_of_le h) e) q)
        (fun e =>
          have fits := le_of_ble_eq_true e
          have smaller : Nat.lt (Nat.sub n k) fuel :=
            sub_lt_fuel fits bound
          Nat.casesOn (motive := fun x => Iff (Nat.le x (succ next)) (Nat.le (Nat.mul x k) n)) q
            (Iff.intro (fun _ => Eq.subst (motive := fun x => Nat.le x n) (Nat.zero_mul k).symm (zero_le n))
              (fun _ => zero_le _))
            (fun x =>
              have previous := ih (Nat.sub n k) smaller x
              Iff.intro (fun h => Eq.subst (motive := fun y => Nat.le y n) (succ_mul x k).symm
                (Eq.subst (motive := Nat.le (Nat.add (Nat.mul x k) k)) (Nat.sub_add_cancel fits)
                  (Nat.add_le_add_right (previous.mp (le_of_succ_le_succ h)) k)))
                (fun h => succ_le_succ (previous.mpr (le_sub_of_add_le
                  (Eq.subst (motive := fun y => Nat.le y n) (succ_mul x k) h)))))) Omega.rfl) fuel

theorem le_div_iff_mul_le {k x y : Nat} (k0 : Nat.lt zero k) :
    Iff (Nat.le x (Nat.div y k)) (Nat.le (Nat.mul x k) y) :=
  Nat.casesOn (motive := fun d => Nat.lt zero d → Iff (Nat.le x (Nat.div y d)) (Nat.le (Nat.mul x d) y))
    k (fun h => False.elim (not_succ_le_zero zero h))
    (fun d _ => quotient_bound d (succ y) y (Nat.le_refl (succ y)) x) k0

theorem div_lt_iff_lt_mul {k x y : Nat} (Hk : Nat.lt zero k) :
    Iff (Nat.lt (Nat.div x k) y) (Nat.lt x (Nat.mul y k)) :=
  Iff.intro (fun h => Nat.not_le.mp (fun bound => Nat.not_le_of_lt h ((le_div_iff_mul_le Hk).mpr bound)))
    (fun h => Nat.not_le.mp (fun bound => Nat.not_le_of_lt h ((le_div_iff_mul_le Hk).mp bound)))

theorem div_mul_le_self (m n : Nat) : Nat.le (Nat.mul (Nat.div m n) n) m :=
  Nat.casesOn (motive := fun k => Nat.le (Nat.mul (Nat.div m k) k) m) n
    (Eq.subst (motive := fun z => Nat.le z m) (Nat.mul_zero (Nat.div m zero)).symm (zero_le m))
    (fun k => (le_div_iff_mul_le (succ_le_succ (zero_le k))).mp (Nat.le_refl (Nat.div m (succ k))))

theorem div_le_self (n k : Nat) : Nat.le (Nat.div n k) n :=
  Nat.casesOn (motive := fun k => Nat.le (Nat.div n k) n) k (zero_le n) (fun d =>
    have lower := mul_le_mul_left (Nat.div n (succ d)) (succ_le_succ (zero_le d))
    Nat.le_trans (Eq.subst (motive := fun z => Nat.le z (Nat.mul (Nat.div n (succ d)) (succ d)))
      (Nat.mul_one (Nat.div n (succ d))) lower) (div_mul_le_self n (succ d)))

theorem div_lt_self {n k : Nat} (hLtN : Nat.lt zero n) (hLtK : Nat.lt (succ zero) k) : Nat.lt (Nat.div n k) n :=
  (div_lt_iff_lt_mul (Nat.le_trans (Nat.succ_le_succ (zero_le (succ zero))) hLtK)).mpr
    (Eq.subst (motive := fun z => Nat.lt z (Nat.mul n k)) (Nat.mul_one n)
      (Nat.mul_lt_mul_of_pos_left hLtK hLtN))

/-- Quotient and remainder consume the same subtraction at each recursive step. -/
private theorem division_decomposition (d fuel : Nat) : ∀ n, Nat.lt n fuel →
    Eq (Nat.add (remainder d fuel n) (Nat.mul (succ d) (quotient d fuel n))) n :=
  Nat.rec (motive := fun fuel => ∀ n, Nat.lt n fuel →
      Eq (Nat.add (remainder d fuel n) (Nat.mul (succ d) (quotient d fuel n))) n)
    (fun n h => False.elim (not_succ_le_zero n h))
    (fun fuel ih n bound =>
      let k := succ d
      let rest := Nat.sub n k
      let r := remainder d fuel rest
      let q := quotient d fuel rest
      Bool.casesOn (motive := fun bit => Eq (Nat.ble k n) bit →
          Eq (Nat.add (Bool.rec (motive := fun _ => Nat) n r bit) (Nat.mul k (Bool.rec (motive := fun _ => Nat) zero (succ q) bit))) n) (Nat.ble k n)
        (fun _ => (congrArg (Nat.add n) (Nat.mul_zero k)).trans (Nat.add_zero n))
        (fun e =>
          have fits := le_of_ble_eq_true e
          have previous := ih rest (sub_lt_fuel fits bound)
          (congrArg (Nat.add r) (mul_succ k q)).trans ((Nat.add_assoc r (Nat.mul k q) k).symm.trans
            ((congrArg (fun x => Nat.add x k) previous).trans (Nat.sub_add_cancel fits)))) Omega.rfl) fuel

private theorem remainder_branch {p : Prop} (dec : Decidable p) (step : p → Nat)
    (n r : Nat) (same : ∀ h, Eq (step h) r) :
    Eq (@dite Nat p dec step (fun _ => n)) (Bool.rec (motive := fun _ => Nat) n r (@Decidable.decide p dec)) :=
  Decidable.rec (motive := fun d => Eq (@dite Nat p d step (fun _ => n))
    (Bool.rec (motive := fun _ => Nat) n r (@Decidable.decide p d))) (fun bit =>
      Bool.casesOn (motive := fun b => ∀ proof : Bool.Reflects b p,
        Eq (@dite Nat p (Decidable.intro b proof) step (fun _ => n)) (Bool.rec (motive := fun _ => Nat) n r b)) bit
        (fun _ => Omega.rfl) same) dec

private theorem modCoreGo_remainder (d fuel : Nat) (positive : Nat.lt zero (succ d)) :
    ∀ n (bound : Nat.lt n fuel), Eq (Nat.modCore.go (succ d) positive fuel n bound) (remainder d fuel n) :=
  Nat.rec (motive := fun fuel => ∀ n (bound : Nat.lt n fuel),
      Eq (Nat.modCore.go (succ d) positive fuel n bound) (remainder d fuel n))
    (fun n bound => False.elim (not_succ_le_zero n bound))
    (fun fuel ih n bound =>
      let k := succ d
      let rest := Nat.sub n k
      remainder_branch (Nat.decLe k n)
        (fun fit => Nat.modCore.go k positive fuel rest (Nat.div_rec_fuel_lemma positive fit bound))
        n (remainder d fuel rest) (fun fit => ih rest (Nat.div_rec_fuel_lemma positive fit bound))) fuel

private theorem succ_mod_remainder (x d : Nat) :
    Eq (Nat.mod (succ x) (succ d)) (remainder d (succ (succ x)) (succ x)) :=
  let n := succ x
  let k := succ d
  let next := remainder d n (Nat.sub n k)
  Bool.casesOn (motive := fun bit => Eq (Nat.ble k n) bit →
    Eq (Nat.mod n k) (@Bool.rec (fun _ => Nat) n next bit))
    (Nat.ble k n)
    (fun e => ite_eq_right (fun h => Bool.ne_false_of_eq_true (ble_eq_true_of_le h) e))
    (fun e => (ite_eq_left (le_of_ble_eq_true e)).trans
      ((modCoreGo_remainder d (succ n) (succ_le_succ (zero_le d)) n (Nat.le_refl (succ n))).trans
        (congrArg (fun bit => @Bool.rec (fun _ => Nat) n next bit) e))) Omega.rfl

theorem mod_add_div (m k : Nat) : Eq (Nat.add (Nat.mod m k) (Nat.mul k (Nat.div m k))) m :=
  Nat.casesOn (motive := fun m => Eq (Nat.add (Nat.mod m k) (Nat.mul k (Nat.div m k))) m) m
    ((congrArg (fun q => Nat.add zero (Nat.mul k q)) (Nat.zero_div k)).trans
      ((congrArg (Nat.add zero) (Nat.mul_zero k)).trans (Nat.add_zero zero)))
    (fun x => Nat.casesOn (motive := fun k =>
      Eq (Nat.add (Nat.mod (succ x) k) (Nat.mul k (Nat.div (succ x) k))) (succ x)) k
      ((congrArg (Nat.add (succ x)) (Nat.mul_zero zero)).trans (Nat.add_zero (succ x)))
      (fun d => (congrArg (fun r => Nat.add r (Nat.mul (succ d) (Nat.div (succ x) (succ d))))
        (succ_mod_remainder x d)).trans
        (division_decomposition d (succ (succ x)) (succ x) (Nat.le_refl (succ (succ x))))))

protected theorem div_one (n : Nat) : Eq (Nat.div n (succ zero)) n :=
  let q := Nat.div n (succ zero)
  ((Nat.zero_add q).symm.trans (congrArg (Nat.add zero) (Nat.one_mul q).symm)).trans
    ((congrArg (fun x => Nat.add x (Nat.mul (succ zero) q)) (mod_one n).symm).trans (mod_add_div n (succ zero)))

theorem mod_def (m k : Nat) : Eq (Nat.mod m k) (Nat.sub m (Nat.mul k (Nat.div m k))) :=
  (Nat.add_sub_cancel (Nat.mod m k) (Nat.mul k (Nat.div m k))).symm.trans
    (congrArg (fun x => Nat.sub x (Nat.mul k (Nat.div m k))) (mod_add_div m k))

theorem mod_eq_sub_mul_div {x k : Nat} : Eq (Nat.mod x k) (Nat.sub x (Nat.mul k (Nat.div x k))) := mod_def x k

theorem mod_eq_sub_div_mul {x k : Nat} : Eq (Nat.mod x k) (Nat.sub x (Nat.mul (Nat.div x k) k)) :=
  (mod_def x k).trans (congrArg (Nat.sub x) (Nat.mul_comm k (Nat.div x k)))

private theorem quotient_correct (d fuel n : Nat) (bound : Nat.lt n fuel) :
    Eq (quotient d fuel n) (Nat.div n (succ d)) :=
  let k := succ d
  let q := quotient d fuel n
  Nat.le_antisymm ((le_div_iff_mul_le (succ_le_succ (zero_le d))).mpr
    ((quotient_bound d fuel n bound q).mp (Nat.le_refl q)))
    ((quotient_bound d fuel n bound (Nat.div n k)).mpr (div_mul_le_self n k))

private theorem remainder_correct (d fuel n : Nat) (bound : Nat.lt n fuel) :
    Eq (remainder d fuel n) (Nat.mod n (succ d)) :=
  let k := succ d
  have qeq := quotient_correct d fuel n bound
  Nat.add_right_cancel ((congrArg (fun x => Nat.add (remainder d fuel n) (Nat.mul k x)) qeq.symm).trans
    ((division_decomposition d fuel n bound).trans (mod_add_div n k).symm))

private theorem mod_step (d n : Nat) : Eq (Nat.mod n (succ d))
    (Bool.rec (motive := fun _ => Nat) n (Nat.mod (Nat.sub n (succ d)) (succ d)) (Nat.ble (succ d) n)) :=
  let k := succ d
  let rest := Nat.sub n k
  (remainder_correct d (succ n) n (Nat.le_refl (succ n))).symm.trans
    (Bool.casesOn (motive := fun bit => Eq (Nat.ble k n) bit →
        Eq (Bool.rec (motive := fun _ => Nat) n (remainder d n rest) bit)
           (Bool.rec (motive := fun _ => Nat) n (Nat.mod rest k) bit))
      (Nat.ble k n) (fun _ => Omega.rfl)
      (fun e => remainder_correct d n rest (sub_lt_fuel (le_of_ble_eq_true e) (Nat.le_refl (succ n)))) Omega.rfl)

private theorem modCoreGo_correct (y : Nat) (positive : Nat.lt zero y) (fuel n : Nat) (bound : Nat.lt n fuel) :
    Eq (Nat.modCore.go y positive fuel n bound) (modCoreGoImpl y positive fuel n bound) :=
  Nat.casesOn (motive := fun y => ∀ positive : Nat.lt zero y,
      Eq (Nat.modCore.go y positive fuel n bound) (modCoreGoImpl y positive fuel n bound)) y
    (fun impossible => False.elim (not_succ_le_zero zero impossible))
    (fun d h => (modCoreGo_remainder d fuel h n bound).trans (remainder_correct d fuel n bound)) positive

protected theorem modCore_eq_mod (n m : Nat) : Eq (Nat.modCore n m) (Nat.mod n m) :=
  Nat.casesOn (motive := fun k => Eq (Nat.modCore n k) (Nat.mod n k)) m
    (mod_zero n).symm (fun d =>
      modCoreGo_correct (succ d) (Nat.succ_le_succ (Nat.zero_le d)) (succ n) n (Nat.le_refl (succ n)))

theorem mod_eq_ite (x y : Nat) : Eq (Nat.mod x y)
    (Omega.ite (And (LT.lt zero y) (LE.le y x)) (Nat.mod (Nat.sub x y) y) x) :=
  Nat.casesOn (motive := fun y => Eq (Nat.mod x y)
      (Omega.ite (And (LT.lt zero y) (LE.le y x)) (Nat.mod (Nat.sub x y) y) x)) y
    ((mod_zero x).trans (ite_eq_right (fun h => not_succ_le_zero zero h.left)).symm)
    (fun d =>
      let k := succ d
      let next := Nat.mod (Nat.sub x k) k
      (mod_step d x).trans
        (Bool.casesOn (motive := fun bit => Eq (Nat.ble k x) bit →
            Eq (Bool.rec (motive := fun _ => Nat) x next bit)
              (Omega.ite (And (LT.lt zero k) (LE.le k x)) next x)) (Nat.ble k x)
          (fun e => (ite_eq_right (fun h => Bool.ne_false_of_eq_true (ble_eq_true_of_le h.right) e)).symm)
          (fun e => (ite_eq_left (And.intro (succ_le_succ (zero_le d)) (le_of_ble_eq_true e))).symm) Omega.rfl))

protected theorem modCore_eq (x y : Nat) : Eq (Nat.modCore x y)
    (Omega.ite (And (LT.lt zero y) (LE.le y x)) (Nat.modCore (Nat.sub x y) y) x) :=
  (Nat.modCore_eq_mod x y).trans ((mod_eq_ite x y).trans
    (congrArg (fun r => Omega.ite (And (LT.lt zero y) (LE.le y x)) r x)
      (Nat.modCore_eq_mod (Nat.sub x y) y).symm))

theorem div_eq_ite (x y : Nat) : Eq (Nat.div x y)
    (Omega.ite (And (LT.lt zero y) (LE.le y x)) (succ (Nat.div (Nat.sub x y) y)) zero) :=
  Nat.casesOn (motive := fun y => Eq (Nat.div x y)
      (Omega.ite (And (LT.lt zero y) (LE.le y x)) (succ (Nat.div (Nat.sub x y) y)) zero)) y
    ((Nat.div_zero x).trans (ite_eq_right (fun h => not_succ_le_zero zero h.left)).symm)
    (fun d =>
      let k := succ d
      let rest := Nat.sub x k
      let next := succ (Nat.div rest k)
      (quotient_correct d (succ x) x (Nat.le_refl (succ x))).symm.trans
        (Bool.casesOn (motive := fun bit => Eq (Nat.ble k x) bit →
            Eq (Bool.rec (motive := fun _ => Nat) zero (succ (quotient d x rest)) bit)
              (Omega.ite (And (LT.lt zero k) (LE.le k x)) next zero)) (Nat.ble k x)
          (fun e => (ite_eq_right (fun h => Bool.ne_false_of_eq_true (ble_eq_true_of_le h.right) e)).symm)
          (fun e => (congrArg succ (quotient_correct d x rest (sub_lt_fuel (le_of_ble_eq_true e) (Nat.le_refl (succ x))))).trans
            (ite_eq_left (And.intro (succ_le_succ (zero_le d)) (le_of_ble_eq_true e))).symm) Omega.rfl))

theorem div_eq_sub_div {b a : Nat} (h₁ : Nat.lt zero b) (h₂ : Nat.le b a) :
    Eq (Nat.div a b) (succ (Nat.div (Nat.sub a b) b)) := (div_eq_ite a b).trans (ite_eq_left (And.intro h₁ h₂))

theorem div_eq_of_lt {a b : Nat} (h₀ : Nat.lt a b) : Eq (Nat.div a b) zero :=
  (div_eq_ite a b).trans (ite_eq_right (fun h => Nat.not_le_of_lt h₀ h.right))

theorem div_add_mod (m n : Nat) : Eq (Nat.add (Nat.mul n (Nat.div m n)) (Nat.mod m n)) m :=
  (Nat.add_comm _ _).trans (mod_add_div m n)

theorem mul_div_le (m n : Nat) : Nat.le (Nat.mul n (Nat.div m n)) m :=
  Eq.subst (motive := fun k => Nat.le k m) (Nat.mul_comm (Nat.div m n) n) (div_mul_le_self m n)

theorem mod_eq_of_lt {a b : Nat} (h : Nat.lt a b) : Eq (Nat.mod a b) a :=
  (mod_eq_ite a b).trans (ite_eq_right (fun fit => Nat.not_le_of_lt h fit.right))

private theorem mod_succ_eq (k n : Nat) : Eq (Nat.mod (succ n) k)
    (Omega.ite (LE.le k (succ n)) (Nat.modCore (succ n) k) (succ n)) :=
  Bool.casesOn (motive := fun bit => Eq (Nat.ble k (succ n)) bit → Eq (Nat.mod (succ n) k)
      (Omega.ite (LE.le k (succ n)) (Nat.modCore (succ n) k) (succ n))) (Nat.ble k (succ n))
    (fun e =>
      have notFit : Not (Nat.le k (succ n)) := fun h => Bool.ne_false_of_eq_true (ble_eq_true_of_le h) e
      (mod_eq_of_lt (Nat.lt_of_not_ge notFit)).trans (ite_eq_right notFit).symm)
    (fun e => (Nat.modCore_eq_mod _ _).symm.trans (ite_eq_left (le_of_ble_eq_true e)).symm) Omega.rfl

end Omega.Nat

port_proof Nat.mod.eq_2 using Omega.Nat.mod_succ_eq

public section
namespace Omega.Nat.mod
export _root_.Nat.mod (eq_2)
end Omega.Nat.mod

namespace Nat
export _root_.Omega.Nat (div_add_mod div_eq_ite div_eq_of_lt div_eq_sub_div div_le_self div_lt_iff_lt_mul div_lt_self div_mul_le_self div_one div_zero le_div_iff_mul_le modCore_eq modCore_eq_mod mod_add_div mod_def mod_eq_ite mod_eq_of_lt mod_eq_sub_div_mul mod_eq_sub_mul_div mod_one mod_zero mul_div_le zero_div)
end Nat

port_proof Nat.mod_le

public section
namespace Nat
export _root_.Omega.Nat (mod_le)
end Nat

port_private_declaration Nat.sub_mul_div_of_le.match_1_1
port_proof Nat.sub_mul_div_of_le by_constructive_casts
port_proof Nat.add_div_right
port_proof Nat.add_mul_div_left
port_proof Nat.add_mul_div_right
port_proof Nat.div_eq_of_lt_le
port_proof Nat.div_div_eq_div_mul
port_proof Nat.mul_sub_div by_constructive_casts
port_definition Nat.instDvd with_native_code
attribute [instance] Omega.Nat.instDvd

public section
namespace Nat
export _root_.Omega.Nat (add_div_right add_mul_div_left add_mul_div_right div_div_eq_div_mul div_eq_of_lt_le instDvd mul_sub_div sub_mul_div_of_le)
end Nat

port_proof Nat.zero_mod
port_private_declaration Nat.add_mul_mod_self_left.match_1_1
port_private_declaration Nat.mod_eq_sub_mod.match_1_1
port_proof Nat.mod_eq_sub_mod
port_proof Nat.add_mod_right
port_definition Nat.add_mul_mod_self_left._f
port_proof Nat.add_mul_mod_self_left
port_proof Nat.mul_mod_right
port_proof Nat.mul_div_cancel

public section
namespace Nat
export _root_.Omega.Nat (add_mod_right add_mul_mod_self_left mod_eq_sub_mod mul_div_cancel mul_mod_right zero_mod)
end Nat

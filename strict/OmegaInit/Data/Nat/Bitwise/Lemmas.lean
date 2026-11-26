module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic
import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Div.Basic
import all OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.Nat

attribute [local semireducible] Nat.pow Nat.add Nat.mul Nat.bitwise Nat.div Nat.mod Nat.beq Nat.ble

private def steps (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => Nat.zero)
    (fun _ prev a b => Nat.casesOn (motive := fun _ => Nat) a
      (Bool.casesOn (motive := fun _ => Nat) (f Bool.false Bool.true) Nat.zero b)
      (fun i => Nat.casesOn (motive := fun _ => Nat) b
        (Bool.casesOn (motive := fun _ => Nat) (f Bool.true Bool.false) Nat.zero (Nat.succ i))
        (fun j =>
          let x := Nat.succ i
          let y := Nat.succ j
          let one := Nat.succ Nat.zero
          let two := Nat.succ one
          let r := prev (Nat.div x two) (Nat.div y two)
          let bit := f (Nat.beq (Nat.mod x two) one) (Nat.beq (Nat.mod y two) one)
          Bool.casesOn (motive := fun _ => Nat) bit (Nat.add r r) (Nat.succ (Nat.add r r)))))

private theorem choose_lt (b : Bool) {u v limit : Nat} (hu : Nat.lt u limit) (hv : Nat.lt v limit) :
    Nat.lt (Bool.casesOn (motive := fun _ => Nat) b u v) limit :=
  Bool.casesOn (motive := fun t => Nat.lt (Bool.casesOn (motive := fun _ => Nat) t u v) limit) b hu hv

private theorem zero_lt_bound {x lim : Nat} (h : Nat.lt x lim) : Nat.lt zero lim :=
  Nat.le_trans (succ_le_succ (zero_le x)) h

private theorem half_lt {x n : Nat} (h : Nat.lt x (Nat.pow (succ (succ zero)) (succ n))) :
    Nat.lt (Nat.div x (succ (succ zero))) (Nat.pow (succ (succ zero)) n) :=
  (div_lt_iff_lt_mul (succ_le_succ (zero_le (succ zero)))).mpr h

private theorem doubled_lt {r limit : Nat} (h : Nat.lt r limit) :
    Nat.lt (succ (Nat.add r r)) (Nat.mul limit (succ (succ zero))) :=
  Eq.subst (motive := fun k => Nat.lt (succ (Nat.add r r)) k) (Nat.mul_two limit).symm
    (Eq.subst (motive := fun k => Nat.le k (Nat.add limit limit)) (succ_add r (succ r))
      (add_le_add h h))

/-- The bound on the left operand is needed only when the operation can return that operand at a zero right argument. -/
private def left_bound (f : Bool → Bool → Bool) (x limit : Nat) : Prop :=
  Eq (f Bool.true Bool.false) Bool.true → Nat.lt x limit

private theorem steps_small (f : Bool → Bool → Bool) (fuel : Nat) :
    ∀ n x y, left_bound f x (Nat.pow (succ (succ zero)) n) → Nat.lt y (Nat.pow (succ (succ zero)) n) →
      Nat.lt (steps f fuel x y) (Nat.pow (succ (succ zero)) n) :=
  Nat.rec (motive := fun fuel => ∀ n x y, left_bound f x (Nat.pow (succ (succ zero)) n) →
      Nat.lt y (Nat.pow (succ (succ zero)) n) → Nat.lt (steps f fuel x y) (Nat.pow (succ (succ zero)) n))
    (fun _ _ _ _ hy => zero_lt_bound hy)
    (fun fuel previous n x y =>
      let two := succ (succ zero)
      let limit := Nat.pow two n
      Nat.casesOn (motive := fun x => left_bound f x limit → Nat.lt y limit →
          Nat.lt (steps f (succ fuel) x y) limit) x
        (fun _ hy => choose_lt (f Bool.false Bool.true) (zero_lt_bound hy) hy)
        (fun i => Nat.casesOn (motive := fun y => left_bound f (succ i) limit → Nat.lt y limit →
            Nat.lt (steps f (succ fuel) (succ i) y) limit) y
          (fun hx hy =>
            Bool.casesOn (motive := fun b => Eq (f Bool.true Bool.false) b →
                Nat.lt (Bool.casesOn (motive := fun _ => Nat) b zero (succ i)) limit)
              (f Bool.true Bool.false) (fun _ => hy) hx Omega.rfl)
          (fun j =>
            Nat.casesOn (motive := fun n => left_bound f (succ i) (Nat.pow two n) → Nat.lt (succ j) (Nat.pow two n) →
                Nat.lt (steps f (succ fuel) (succ i) (succ j)) (Nat.pow two n)) n
              (fun _ hy => False.elim (not_succ_le_zero j (le_of_succ_le_succ hy)))
              (fun k hx hy =>
                let x := succ i
                let y := succ j
                let r := steps f fuel (Nat.div x two) (Nat.div y two)
                let bit := f (Nat.beq (Nat.mod x two) (succ zero)) (Nat.beq (Nat.mod y two) (succ zero))
                have recursive := previous k (Nat.div x two) (Nat.div y two) (fun e => half_lt (hx e)) (half_lt hy)
                have hi := doubled_lt recursive
                choose_lt bit (Nat.le_trans (Nat.le.step (Nat.le_refl (succ (Nat.add r r)))) hi) hi)))) fuel

theorem bitwise_lt_two_pow {x n y : Nat} {f : Bool → Bool → Bool}
    (left : Nat.lt x (Nat.pow (succ (succ zero)) n)) (right : Nat.lt y (Nat.pow (succ (succ zero)) n)) :
    Nat.lt (bitwise f x y) (Nat.pow (succ (succ zero)) n) :=
  steps_small f (succ x) n x y (fun _ => left) right

theorem and_lt_two_pow (x : Nat) {y n : Nat} (right : Nat.lt y (Nat.pow (succ (succ zero)) n)) :
    Nat.lt (Nat.land x y) (Nat.pow (succ (succ zero)) n) :=
  steps_small Bool.and (succ x) n x y (fun e => False.elim (Bool.ne_false_of_eq_true e Omega.rfl)) right

theorem or_lt_two_pow {x y n : Nat} (left : Nat.lt x (Nat.pow (succ (succ zero)) n))
    (right : Nat.lt y (Nat.pow (succ (succ zero)) n)) : Nat.lt (Nat.lor x y) (Nat.pow (succ (succ zero)) n) :=
  bitwise_lt_two_pow left right

private theorem shift_inside (x n : Nat) : Eq (Nat.shiftRight x (succ n)) (Nat.shiftRight (Nat.div x (succ (succ zero))) n) :=
  Nat.rec (motive := fun n => Eq (Nat.shiftRight x (succ n)) (Nat.shiftRight (Nat.div x (succ (succ zero))) n))
    Omega.rfl (fun _ ih => congrArg (fun z => Nat.div z (succ (succ zero))) ih) n

theorem testBit_succ (x i : Nat) : Eq (testBit x (succ i)) (testBit (Nat.div x (succ (succ zero))) i) :=
  congrArg (fun k => Bool.not (Nat.beq (Nat.land (succ zero) k) zero)) (shift_inside x i)

private theorem one_bit : Eq (testBit (succ zero) zero) Bool.true := Omega.rfl

theorem testBit_add_one (x i : Nat) : Eq (testBit x (Nat.add i (succ zero)))
    (testBit (Nat.div x (succ (succ zero))) i) := testBit_succ x i

theorem testBit_div_two (x i : Nat) : Eq (testBit (Nat.div x (succ (succ zero))) i)
    (testBit x (Nat.add i (succ zero))) := (testBit_add_one x i).symm

private theorem set_bit_of_pos (fuel : Nat) : ∀ x, Nat.lt x fuel → Nat.lt zero x →
    Exists (fun i => Eq (testBit x i) Bool.true) :=
  Nat.rec (motive := fun fuel => ∀ x, Nat.lt x fuel → Nat.lt zero x → Exists (fun i => Eq (testBit x i) Bool.true))
    (fun x h _ => False.elim (not_succ_le_zero x h))
    (fun fuel ih x bound =>
      Nat.casesOn (motive := fun x => Nat.lt x (succ fuel) → Nat.lt zero x →
          Exists (fun i => Eq (testBit x i) Bool.true)) x
        (fun _ h => False.elim (not_succ_le_zero zero h))
        (fun a => Nat.casesOn (motive := fun a => Nat.lt (succ a) (succ fuel) → Nat.lt zero (succ a) →
            Exists (fun i => Eq (testBit (succ a) i) Bool.true)) a
          (fun _ _ => Exists.intro zero one_bit)
          (fun k h pos =>
            let two := succ (succ zero)
            let n := succ (succ k)
            have q_bound : Nat.lt (Nat.div n two) fuel :=
              Nat.le_trans (div_lt_self pos Nat.one_lt_two) (le_of_succ_le_succ h)
            have q_pos : Nat.lt zero (Nat.div n two) := (le_div_iff_mul_le Nat.zero_lt_two).mpr
              (Eq.subst (motive := fun t => Nat.le t n) (Nat.one_mul two).symm
                (succ_le_succ (succ_le_succ (zero_le k))))
            (ih (Nat.div n two) q_bound q_pos).elim fun i bit =>
              Exists.intro (succ i) ((testBit_succ n i).trans bit))) bound) fuel

theorem exists_testBit_of_ne_zero {x : Nat} (xnz : Ne x zero) : Exists (fun i => Eq (testBit x i) Bool.true) :=
  set_bit_of_pos (succ x) x (Nat.le_refl _) (Nat.lt_of_not_ge (fun h => xnz (Nat.le_antisymm h (zero_le x))))

theorem exists_ge_and_testBit_of_ge_two_pow {n x : Nat} (p : Nat.le (Nat.pow (succ (succ zero)) n) x) :
    Exists (fun i => And (Nat.le n i) (Eq (testBit x i) Bool.true)) :=
  (Nat.rec (motive := fun n => ∀ x, Nat.le (Nat.pow (succ (succ zero)) n) x →
      Exists (fun i => And (Nat.le n i) (Eq (testBit x i) Bool.true)))
    (fun x h => (set_bit_of_pos (succ x) x (Nat.le_refl _) h).elim fun i bit =>
      Exists.intro i (And.intro (zero_le i) bit))
    (fun n ih x h =>
      let two := succ (succ zero)
      have lower : Nat.le (Nat.pow two n) (Nat.div x two) := (le_div_iff_mul_le Nat.zero_lt_two).mpr h
      (ih (Nat.div x two) lower).elim fun i b =>
        Exists.intro (succ i) (And.intro (succ_le_succ b.left) ((testBit_succ x i).trans b.right))) n) x p

theorem lt_pow_two_of_testBit {n : Nat} (x : Nat)
    (p : ∀ i, Nat.le n i → Eq (testBit x i) Bool.false) : Nat.lt x (Nat.pow (succ (succ zero)) n) :=
  Nat.lt_of_not_ge (fun h => (exists_ge_and_testBit_of_ge_two_pow h).elim fun i b =>
    Bool.ne_false_of_eq_true b.right (p i b.left))

theorem zero_testBit (i : Nat) : Eq (testBit zero i) Bool.false :=
  Nat.rec (motive := fun i => Eq (testBit zero i) Bool.false) Omega.rfl
    (fun j ih => (testBit_succ zero j).trans
      ((congrArg (fun q => testBit q j) (Nat.zero_div (succ (succ zero)))).trans ih)) i

theorem ge_two_pow_of_testBit {i x : Nat} (p : Eq (testBit x i) Bool.true) :
    Nat.le (Nat.pow (succ (succ zero)) i) x :=
  (Nat.rec (motive := fun i => ∀ x, Eq (testBit x i) Bool.true → Nat.le (Nat.pow (succ (succ zero)) i) x)
    (fun x => Nat.casesOn (motive := fun x => Eq (testBit x zero) Bool.true → Nat.le (succ zero) x) x
      (fun h => False.elim (Bool.ne_false_of_eq_true h (zero_testBit zero)))
      (fun k _ => succ_le_succ (zero_le k)))
    (fun i ih x h => (le_div_iff_mul_le Nat.zero_lt_two).mp
      (ih (Nat.div x (succ (succ zero))) ((testBit_succ x i).symm.trans h))) i) x p

theorem testBit_lt_two_pow {x i : Nat} (lt : Nat.lt x (Nat.pow (succ (succ zero)) i)) :
    Eq (testBit x i) Bool.false :=
  Bool.casesOn (motive := fun bit => Eq (testBit x i) bit → Eq bit Bool.false) (testBit x i)
    (fun _ => Omega.rfl) (fun h => False.elim (Nat.not_le_of_lt lt (ge_two_pow_of_testBit h))) Omega.rfl

theorem testBit_of_two_pow_le_and_two_pow_add_one_gt {n i : Nat}
    (hle : Nat.le (Nat.pow (succ (succ zero)) i) n)
    (hgt : Nat.lt n (Nat.pow (succ (succ zero)) (Nat.add i (succ zero)))) : Eq (testBit n i) Bool.true :=
  (exists_ge_and_testBit_of_ge_two_pow hle).elim fun j witness =>
    have atMost : Nat.le j i := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge (fun higher =>
      Nat.not_le_of_lt hgt (Nat.le_trans (Nat.pow_le_pow_right Nat.zero_lt_two higher)
        (ge_two_pow_of_testBit witness.right))))
    (congrArg (testBit n) (Nat.le_antisymm witness.left atMost)).trans witness.right

private theorem bool_of_binary (r : Nat) (small : Nat.lt r (succ (succ zero))) :
    Eq (Bool.casesOn (motive := fun _ => Nat) (Nat.beq r (succ zero)) zero (succ zero)) r :=
  (Nat.casesOn (motive := fun r => Nat.lt r (succ (succ zero)) →
      Eq (Bool.casesOn (motive := fun _ => Nat) (Nat.beq r (succ zero)) zero (succ zero)) r) r
    (fun _ => Omega.rfl)
    (fun d => Nat.casesOn (motive := fun d => Nat.lt (succ d) (succ (succ zero)) →
        Eq (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (succ d) (succ zero)) zero (succ zero)) (succ d)) d
      (fun _ => Omega.rfl) (fun k h => False.elim (not_succ_le_zero k (le_of_succ_le_succ (le_of_succ_le_succ h)))))) small

theorem one_and_eq_mod_two (n : Nat) : Eq (Nat.land (succ zero) n) (Nat.mod n (succ (succ zero))) :=
  Nat.casesOn (motive := fun n => Eq (Nat.land (succ zero) n) (Nat.mod n (succ (succ zero)))) n
    Omega.rfl (fun k => bool_of_binary _ (Nat.mod_lt (succ k) Nat.zero_lt_two))

end Omega.Nat

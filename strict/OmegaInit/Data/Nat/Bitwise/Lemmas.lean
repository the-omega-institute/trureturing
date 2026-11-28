module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic
import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Lemmas
import OmegaInit.Data.Nat.Log2
import OmegaInit.Data.Nat.Div.Basic
import all OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.Nat

attribute [local semireducible] Nat.bitwise Nat.div

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

/-- Append a single low bit to the binary representation of the quotient. -/
private def pack (r : Nat) (b : Bool) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) b (Nat.add r r) (succ (Nat.add r r))

private def digit (b : Bool) : Nat := Bool.casesOn (motive := fun _ => Nat) b zero (succ zero)

private theorem packed_bounds (r : Nat) (b : Bool) :
    And (Nat.le (Nat.mul r (succ (succ zero))) (pack r b))
      (Nat.lt (pack r b) (Nat.mul (succ r) (succ (succ zero)))) :=
  let two := succ (succ zero)
  let base := Nat.add r r
  have upper : Eq (Nat.mul (succ r) two) (succ (succ base)) :=
    (succ_mul r two).trans (congrArg (fun z => succ (succ z)) (Nat.mul_two r))
  Bool.casesOn (motive := fun b => And (Nat.le (Nat.mul r two) (pack r b))
      (Nat.lt (pack r b) (Nat.mul (succ r) two))) b
    (And.intro (Eq.subst (motive := fun k => Nat.le k base) (Nat.mul_two r).symm (Nat.le_refl base))
      (Eq.subst (motive := Nat.lt base) upper.symm (Nat.le.step (Nat.le_refl (succ base)))))
    (And.intro (Eq.subst (motive := fun k => Nat.le k (succ base)) (Nat.mul_two r).symm (Nat.le.step (Nat.le_refl base)))
      (Eq.subst (motive := Nat.lt (succ base)) upper.symm (Nat.le_refl (succ (succ base)))))

private theorem packed_div (r : Nat) (b : Bool) : Eq (Nat.div (pack r b) (succ (succ zero))) r :=
  let bounds := packed_bounds r b
  Nat.le_antisymm (le_of_succ_le_succ ((div_lt_iff_lt_mul Nat.zero_lt_two).mpr bounds.right))
    ((le_div_iff_mul_le Nat.zero_lt_two).mpr bounds.left)

private theorem packed_mod (r : Nat) (b : Bool) : Eq (Nat.mod (pack r b) (succ (succ zero))) (digit b) :=
  let two := succ (succ zero)
  let p := pack r b
  have split := div_add_mod p two
  have canonical : Eq (Nat.add (Nat.mul two r) (digit b)) p :=
    Bool.casesOn (motive := fun b => Eq (Nat.add (Nat.mul two r) (digit b)) (pack r b)) b
      ((Nat.add_zero (Nat.mul two r)).trans (Nat.two_mul r)) (congrArg succ (Nat.two_mul r))
  Nat.add_left_cancel ((congrArg (fun q => Nat.add (Nat.mul two q) (Nat.mod p two)) (packed_div r b).symm).trans
    (split.trans canonical.symm))

private theorem bit_as_parity (x : Nat) : Eq (testBit x zero) (Nat.beq (Nat.mod x (succ (succ zero))) (succ zero)) :=
  let r := Nat.mod x (succ (succ zero))
  let P := fun r => Eq (Bool.not (Nat.beq r zero)) (Nat.beq r (succ zero))
  have parity : ∀ v, Nat.lt v (succ (succ zero)) → P v :=
    fun v => Nat.casesOn (motive := fun v => Nat.lt v (succ (succ zero)) → P v) v (fun _ => Omega.rfl)
      (fun d => Nat.casesOn (motive := fun d => Nat.lt (succ d) (succ (succ zero)) → P (succ d)) d
        (fun _ => Omega.rfl) (fun k h => False.elim (not_succ_le_zero k (le_of_succ_le_succ (le_of_succ_le_succ h)))))
  (congrArg (fun t => Bool.not (Nat.beq t zero)) (one_and_eq_mod_two x)).trans (parity r (Nat.mod_lt x Nat.zero_lt_two))

private theorem packed_test_zero (r : Nat) (b : Bool) : Eq (testBit (pack r b) zero) b :=
  (bit_as_parity (pack r b)).trans ((congrArg (fun t => Nat.beq t (succ zero)) (packed_mod r b)).trans
    (Bool.casesOn (motive := fun b => Eq (Nat.beq (digit b) (succ zero)) b) b Omega.rfl Omega.rfl))

private theorem packed_test_succ (r : Nat) (b : Bool) (i : Nat) : Eq (testBit (pack r b) (succ i)) (testBit r i) :=
  (testBit_succ (pack r b) i).trans (congrArg (fun t => testBit t i) (packed_div r b))

private theorem bit_congr (f : Bool → Bool → Bool) {a b c d : Bool} (left : Eq a b) (right : Eq c d) :
    Eq (f a c) (f b d) := (congrArg (fun t => f t c) left).trans (congrArg (f b) right)

private theorem test_zero_or (f : Bool → Bool) (h : Eq (f Bool.false) Bool.false) (x i : Nat) :
    Eq (testBit (Bool.casesOn (motive := fun _ => Nat) (f Bool.true) zero x) i) (f (testBit x i)) :=
  Bool.casesOn (motive := fun b => Eq (f Bool.true) b →
      Eq (testBit (Bool.casesOn (motive := fun _ => Nat) b zero x) i) (f (testBit x i))) (f Bool.true)
    (fun no => (zero_testBit i).trans (Bool.casesOn (motive := fun bit => Eq Bool.false (f bit))
      (testBit x i) h.symm no.symm))
    (fun yes => Bool.casesOn (motive := fun bit => Eq bit (f bit)) (testBit x i) h.symm yes.symm) Omega.rfl

private theorem steps_test (f : Bool → Bool → Bool) (h : Eq (f Bool.false Bool.false) Bool.false) (fuel : Nat) :
    ∀ x y i, Nat.lt x fuel → Eq (testBit (steps f fuel x y) i) (f (testBit x i) (testBit y i)) :=
  Nat.rec (motive := fun fuel => ∀ x y i, Nat.lt x fuel →
      Eq (testBit (steps f fuel x y) i) (f (testBit x i) (testBit y i)))
    (fun x _ _ bound => False.elim (not_succ_le_zero x bound))
    (fun fuel ih x y i => Nat.casesOn (motive := fun x => Nat.lt x (succ fuel) →
        Eq (testBit (steps f (succ fuel) x y) i) (f (testBit x i) (testBit y i))) x
      (fun _ => (test_zero_or (f Bool.false) h y i).trans (bit_congr f (zero_testBit i).symm Omega.rfl))
      (fun a => Nat.casesOn (motive := fun y => Nat.lt (succ a) (succ fuel) →
          Eq (testBit (steps f (succ fuel) (succ a) y) i) (f (testBit (succ a) i) (testBit y i))) y
        (fun _ => (test_zero_or (fun b => f b Bool.false) h (succ a) i).trans (bit_congr f Omega.rfl (zero_testBit i).symm))
        (fun b bound =>
          let x := succ a
          let y := succ b
          let two := succ (succ zero)
          let r := steps f fuel (Nat.div x two) (Nat.div y two)
          let bit := f (Nat.beq (Nat.mod x two) (succ zero)) (Nat.beq (Nat.mod y two) (succ zero))
          have smaller := Nat.le_trans (div_lt_self (succ_le_succ (zero_le a)) Nat.one_lt_two) (le_of_succ_le_succ bound)
          Nat.casesOn (motive := fun i => Eq (testBit (pack r bit) i) (f (testBit x i) (testBit y i))) i
            ((packed_test_zero r bit).trans (bit_congr f (bit_as_parity x).symm (bit_as_parity y).symm))
            (fun j => (packed_test_succ r bit j).trans
              ((ih (Nat.div x two) (Nat.div y two) j smaller).trans
                (bit_congr f (testBit_succ x j).symm (testBit_succ y j).symm)))))) fuel

theorem testBit_bitwise {f : Bool → Bool → Bool} (of_false_false : Eq (f Bool.false Bool.false) Bool.false)
    (x y i : Nat) : Eq (testBit (bitwise f x y) i) (f (testBit x i) (testBit y i)) :=
  steps_test f of_false_false (succ x) x y i (Nat.le_refl _)

theorem testBit_and (x y i : Nat) : Eq (testBit (Nat.land x y) i) (Bool.and (testBit x i) (testBit y i)) :=
  testBit_bitwise (f := Bool.and) Omega.rfl x y i

theorem testBit_or (x y i : Nat) : Eq (testBit (Nat.lor x y) i) (Bool.or (testBit x i) (testBit y i)) :=
  testBit_bitwise (f := Bool.or) Omega.rfl x y i

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (and_lt_two_pow bitwise_lt_two_pow exists_ge_and_testBit_of_ge_two_pow exists_testBit_of_ne_zero ge_two_pow_of_testBit lt_pow_two_of_testBit one_and_eq_mod_two or_lt_two_pow testBit_add_one testBit_and testBit_bitwise testBit_div_two testBit_lt_two_pow testBit_of_two_pow_le_and_two_pow_add_one_gt testBit_or testBit_succ zero_testBit)
end Nat

namespace Omega.Nat

private theorem highestBit {n : Nat} (nz : Not (Eq n 0)) : Eq (testBit n (log2 n)) Bool.true :=
  let bounds := (log2_eq_iff nz).mp rfl
  testBit_of_two_pow_le_and_two_pow_add_one_gt bounds.left bounds.right

private theorem lowerBits (k : Nat) : ∀ i, Nat.lt i k → Eq (testBit (Nat.pow 2 k) i) Bool.false :=
  Nat.rec (motive := fun k => ∀ i, Nat.lt i k → Eq (testBit (Nat.pow 2 k) i) Bool.false)
    (fun i h => False.elim (not_succ_le_zero i h))
    (fun k ih i => Nat.casesOn (motive := fun i => Nat.lt i (Nat.succ k) →
      Eq (testBit (Nat.pow 2 k.succ) i) Bool.false) i
      (fun _ => (bit_as_parity (Nat.pow 2 k.succ)).trans
        (congrArg (fun r => Nat.beq r 1) ((congrArg (fun y => Nat.mod y 2) (Nat.mul_comm (Nat.pow 2 k) 2)).trans (Nat.mul_mod_right 2 (Nat.pow 2 k)))))
      (fun i hi => (testBit_succ (Nat.pow 2 k.succ) i).trans
        ((congrArg (fun r => testBit r i) (Nat.mul_div_cancel (Nat.pow 2 k) Nat.zero_lt_two)).trans
          (ih i (Nat.le_of_succ_le_succ hi))))) k

private theorem offBit {n m : Nat} (ne : Not (Eq n m)) : Eq (testBit (Nat.pow 2 n) m) Bool.false :=
  Decidable.byCases (dec := Nat.decLt m n) (fun lt => lowerBits n m lt)
    (fun no =>
      let h : Nat.lt n m := Nat.lt_of_not_ge (fun rev => ne (Nat.le_antisymm (Nat.le_of_not_gt no) rev))
      let scale : Nat.lt (Nat.pow 2 n) (Nat.mul (Nat.pow 2 n) 2) :=
        Eq.subst (motive := fun a => Nat.lt a (Nat.mul (Nat.pow 2 n) 2)) (Nat.mul_one _)
          (Nat.mul_lt_mul_of_pos_left Nat.one_lt_two (Nat.two_pow_pos n))
      let pos : Nat.lt (Nat.pow 2 n) (Nat.pow 2 m) := Nat.lt_of_lt_of_le scale (Nat.pow_le_pow_right Nat.zero_lt_two h)
      testBit_lt_two_pow pos)

end Omega.Nat
port_proof Nat.testBit_log2 using Omega.Nat.highestBit
port_proof Nat.testBit_two_pow_of_ne using Omega.Nat.offBit

namespace Nat
export _root_.Omega.Nat (testBit_log2 testBit_two_pow_of_ne)
end Nat

module
prelude
public import OmegaMath.Arithmetic.Euclidean.Division
import OmegaMath.Data.Int

/-!
Omega original.

The rational square-root obstruction at three, in denominator-cleared form.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

private abbrev two : Nat := Nat.one.succ
private abbrev three : Nat := Nat.one.succ.succ

private theorem below_three (r : Nat) (hr : Nat.lt r three) :
    Or (Eq r .zero) (Or (Eq r Nat.one) (Eq r two)) :=
  let P := fun value => Nat.lt value three →
    Or (Eq value .zero) (Or (Eq value Nat.one) (Eq value two))
  Nat.rec (motive := P) (fun _ => Or.inl Eq.refl)
    (fun n _ => Nat.rec (motive := fun k => P k.succ)
      (fun _ => Or.inr (Or.inl Eq.refl))
      (fun m _ => Nat.rec (motive := fun k => P k.succ.succ)
        (fun _ => Or.inr (Or.inr Eq.refl))
        (fun _ _ h => False.elim h) m) n) r hr

private theorem square_of_three_mul_add (q r : Nat) :
    Eq (((three.mul q).add r).mul ((three.mul q).add r))
      ((three.mul ((q.mul ((three.mul q).add r)).add (q.mul r))).add (r.mul r)) :=
  let multiple := three.mul q
  let x := multiple.add r
  let left := q.mul x
  let right := q.mul r
  have hright := (Nat.mul_comm r multiple).trans (Nat.mul_assoc three q r)
  have hparts := (congrArg (fun t : Nat => t.add (r.mul x)) (Nat.mul_assoc three q x)).trans
    (congrArg (Nat.add (three.mul left))
      ((Nat.mul_add r multiple r).trans (congrArg (fun t : Nat => t.add (r.mul r)) hright)))
  (Nat.add_mul multiple r x).trans (hparts.trans
    ((Nat.add_assoc (three.mul left) (three.mul right) (r.mul r)).symm.trans
      (congrArg (fun t : Nat => t.add (r.mul r)) (Nat.mul_add three left right).symm)))

private theorem three_dvd_of_three_dvd_square (a : Nat) (h : Dvd three (a.mul a)) :
    Dvd three a :=
  let division := divMod a three
  let r := division.remainder
  let q := division.quotient
  let quotient := (q.mul ((three.mul q).add r)).add (q.mul r)
  have hpos : Nat.lt Nat.zero three := True.intro
  have spec := divMod_spec a three hpos
  have expand : Eq (a.mul a) ((three.mul quotient).add (r.mul r)) :=
    (congrArg (fun t : Nat => t.mul t) spec.left).trans (square_of_three_mul_add q r)
  have impossible (k : Nat) (hk : Eq (a.mul a) ((three.mul k).add Nat.one)) : False :=
    h.elim fun _ eqMultiple =>
      Nat.succ_ne_zero .zero
        (divMod_remainder_unique (r := Nat.one) (r' := Nat.zero) (hk.symm.trans eqMultiple)
          (show Nat.lt Nat.one three from True.intro) hpos)
  (below_three r spec.right).elim
    (fun hz => Exists.intro q (spec.left.trans (congrArg (Nat.add (three.mul q)) hz)))
    (fun nonzero => nonzero.elim
      (fun h1 => False.elim (impossible quotient
        (expand.trans (congrArg (fun t : Nat => (three.mul quotient).add (t.mul t)) h1))))
      (fun h2 => False.elim (impossible quotient.succ
        (expand.trans (congrArg (fun t : Nat => (three.mul quotient).add (t.mul t)) h2)))))

private theorem cancel_square_factor {a b q : Nat} (ha : Eq a (three.mul q))
    (h : Eq (a.mul a) (three.mul (b.mul b))) : Eq (b.mul b) (three.mul (q.mul q)) :=
  have expand : Eq ((three.mul q).mul (three.mul q)) (three.mul (three.mul (q.mul q))) :=
    (Nat.mul_assoc three q (three.mul q)).trans (congrArg (Nat.mul three)
      ((Nat.mul_comm q (three.mul q)).trans (Nat.mul_assoc three q q)))
  have multiplied := h.symm.trans ((congrArg (fun t : Nat => t.mul t) ha).trans expand)
  Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left
    (show Not (Eq (Int.ofNat three) (Int.ofNat .zero)) from
      fun h0 => Nat.succ_ne_zero two (Int.ofNat_inj.mp h0))
    (congrArg Int.ofNat multiplied))

/-- Three times a nonzero natural square is never a square. -/
theorem no_square_eq_three_mul_square (a b : Nat) (hb : Not (Eq b .zero))
    (h : Eq (a.mul a) (Nat.one.succ.succ.mul (b.mul b))) : False :=
  strongInduction (P := fun (denominator : Nat) => ∀ (numerator : Nat),
    Not (Eq denominator .zero) →
      Eq (numerator.mul numerator) (three.mul (denominator.mul denominator)) → False)
    (fun n smaller m hn hnm =>
      (three_dvd_of_three_dvd_square m (Exists.intro (n.mul n) hnm)).elim fun q hq =>
        have swapped := cancel_square_factor hq hnm
        (three_dvd_of_three_dvd_square n (Exists.intro (q.mul q) swapped)).elim fun r hr =>
          have hrne : Not (Eq r .zero) := fun hz =>
            hn (hr.trans (congrArg (Nat.mul three) hz))
          have hgrowth : Nat.lt r (three.mul r) :=
            Eq.subst (Nat.lt r) ((Nat.add_comm r (two.mul r)).trans (Nat.succ_mul two r).symm)
              (add_lt_add_left (mul_pos (show Nat.lt .zero two from True.intro)
                (pos_of_ne_zero hrne)) r)
          have hlt : Nat.lt r n := Eq.subst (Nat.lt r) hr.symm hgrowth
          smaller r hlt q hrne (cancel_square_factor hr swapped)) b a hb h

end Omega.Arithmetic

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.Int

/-!
Omega original.

Homogeneous coordinates and multiplication of integer complex numbers.
The first coordinate is the imaginary part and the second is the real part.
-/

noncomputable section

@[expose] public section

namespace Omega.Projective.Circle

structure Coordinates where
  p : Int
  q : Int

namespace Coordinates

def mul (a b : Coordinates) : Coordinates :=
  ⟨(a.p.mul b.q).add (a.q.mul b.p), (a.q.mul b.q).sub (a.p.mul b.p)⟩

def normSq (a : Coordinates) : Nat :=
  (a.p.natAbs.mul a.p.natAbs).add (a.q.natAbs.mul a.q.natAbs)

theorem normSq_cast (a : Coordinates) :
    Eq (Int.ofNat a.normSq) ((Int.square a.p).add (Int.square a.q)) :=
  Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self

theorem normSq_zero_iff (a : Coordinates) :
    Iff (Eq a.normSq Nat.zero) (And (Eq a.p Int.zero) (Eq a.q Int.zero)) :=
  let squares := Int.sum_of_two_squares_eq_zero a.p a.q
  Iff.intro
    (fun h => squares.mp (a.normSq_cast.symm.trans (congrArg Int.ofNat h)))
    (fun h => Int.ofNat_inj.mp (a.normSq_cast.trans (squares.mpr h)))

private theorem sq_add (x y : Int) :
    Eq (Int.square (x.add y))
      (((Int.square x).add (Int.square y)).add ((x.mul y).add (x.mul y))) :=
  have first := Int.mul_add x x y
  have second := (Int.mul_add y x y).trans
    (congrArg (fun t : Int => t.add (Int.square y)) (Int.mul_comm y x))
  (Int.add_mul x y (x.add y)).trans
    ((Eq.map₂ Int.add first second).trans
      ((congrArg (fun t : Int => ((Int.square x).add (x.mul y)).add t)
        (Int.add_comm (x.mul y) (Int.square y))).trans
          (Int.add_add_add_comm (Int.square x) (x.mul y) (Int.square y) (x.mul y))))

private theorem sq_sub (x y : Int) :
    Eq (Int.square (x.sub y))
      (((Int.square x).add (Int.square y)).sub ((x.mul y).add (x.mul y))) :=
  (sq_add x y.neg).trans
    (Eq.map₂ Int.add
      (congrArg (Int.square x).add (Int.neg_mul_neg y y))
      ((Eq.map₂ Int.add (Int.mul_neg x y) (Int.mul_neg x y)).trans Int.neg_add.symm))

private theorem square_sum_product (a b c d : Int) :
    Eq ((Int.square ((a.mul d).add (b.mul c))).add (Int.square ((b.mul d).sub (a.mul c))))
      (((Int.square a).add (Int.square b)).mul ((Int.square c).add (Int.square d))) :=
  let A := (Int.square (a.mul d)).add (Int.square (b.mul c))
  let B := (Int.square (b.mul d)).add (Int.square (a.mul c))
  let T := ((a.mul d).mul (b.mul c)).add ((a.mul d).mul (b.mul c))
  have sameCross : Eq ((b.mul d).mul (a.mul c)) ((a.mul d).mul (b.mul c)) :=
    (Int.mul_mul_mul_comm b d a c).trans
      ((congrArg (fun t : Int => t.mul (d.mul c)) (Int.mul_comm b a)).trans
        (Int.mul_mul_mul_comm a d b c).symm)
  have split : Eq ((Int.square ((a.mul d).add (b.mul c))).add
      (Int.square ((b.mul d).sub (a.mul c)))) ((A.add T).add (B.add T.neg)) :=
    Eq.map₂ Int.add (sq_add (a.mul d) (b.mul c))
      ((sq_sub (b.mul d) (a.mul c)).trans
        (congrArg (fun t : Int => B.sub t) (Eq.map₂ Int.add sameCross sameCross)))
  have diagonal : Eq (A.add B)
      ((((Int.square a).mul (Int.square c)).add ((Int.square a).mul (Int.square d))).add
        (((Int.square b).mul (Int.square c)).add ((Int.square b).mul (Int.square d)))) :=
    let ac := (Int.square a).mul (Int.square c)
    let ad := (Int.square a).mul (Int.square d)
    let bc := (Int.square b).mul (Int.square c)
    let bd := (Int.square b).mul (Int.square d)
    (Eq.map₂ Int.add
      (Eq.map₂ Int.add (Int.square_mul a d) (Int.square_mul b c))
      (Eq.map₂ Int.add (Int.square_mul b d) (Int.square_mul a c))).trans
      ((congrArg (fun t : Int => (ad.add bc).add t) (Int.add_comm bd ac)).trans
        ((Int.add_add_add_comm ad bc ac bd).trans
          (congrArg (fun t : Int => t.add (bc.add bd)) (Int.add_comm ad ac))))
  split.trans
    ((Int.add_add_add_comm A T B T.neg).trans
      ((congrArg (A.add B).add (Int.add_right_neg T)).trans
        ((Int.add_zero (A.add B)).trans
          (diagonal.trans
            ((Eq.map₂ Int.add
              (Int.mul_add (Int.square a) (Int.square c) (Int.square d)).symm
              (Int.mul_add (Int.square b) (Int.square c) (Int.square d)).symm).trans
              (Int.add_mul (Int.square a) (Int.square b)
                ((Int.square c).add (Int.square d))).symm)))))

theorem mul_normSq (a b : Coordinates) :
    Eq (a.normSq.mul b.normSq) (a.mul b).normSq :=
  Int.ofNat_inj.mp
    ((Eq.map₂ Int.mul a.normSq_cast b.normSq_cast).trans
      ((square_sum_product a.p a.q b.p b.q).symm.trans (a.mul b).normSq_cast.symm))

theorem mul_comm (a b : Coordinates) : Eq (a.mul b) (b.mul a) :=
  have imaginary := (Eq.map₂ Int.add (Int.mul_comm a.p b.q) (Int.mul_comm a.q b.p)).trans
    (Int.add_comm (b.q.mul a.p) (b.p.mul a.q))
  have real := Eq.map₂ Int.sub (Int.mul_comm a.q b.q) (Int.mul_comm a.p b.p)
  Eq.map₂ Coordinates.mk imaginary real

theorem mul_assoc (a b c : Coordinates) : Eq ((a.mul b).mul c) (a.mul (b.mul c)) :=
  let p := a.p
  let q := a.q
  let r := b.p
  let s := b.q
  let u := c.p
  let v := c.q
  have imaginary : Eq ((a.mul b).mul c).p (a.mul (b.mul c)).p :=
    let A := (p.mul s).mul v
    let B := (q.mul r).mul v
    let C := (q.mul s).mul u
    let D := ((p.mul r).mul u).neg
    have expandLeft : Eq ((a.mul b).mul c).p ((A.add B).add (C.add D)) :=
      Eq.map₂ Int.add (Int.add_mul (p.mul s) (q.mul r) v) (Int.sub_mul (q.mul s) (p.mul r) u)
    have rearrange := (congrArg (A.add B).add (Int.add_comm C D)).trans (Int.add_add_add_comm A B D C)
    have expandRight : Eq (a.mul (b.mul c)).p ((A.add D).add (B.add C)) :=
      (Eq.map₂ Int.add (Int.mul_sub p (s.mul v) (r.mul u))
        (Int.mul_add q (r.mul v) (s.mul u))).trans
        (Eq.map₂ Int.add
          (Eq.map₂ Int.sub (Int.mul_assoc p s v).symm (Int.mul_assoc p r u).symm)
          (Eq.map₂ Int.add (Int.mul_assoc q r v).symm (Int.mul_assoc q s u).symm))
    expandLeft.trans (rearrange.trans expandRight.symm)
  have real : Eq ((a.mul b).mul c).q (a.mul (b.mul c)).q :=
    let A := (q.mul s).mul v
    let B := ((p.mul r).mul v).neg
    let C := ((p.mul s).mul u).neg
    let D := ((q.mul r).mul u).neg
    have expandLeft : Eq ((a.mul b).mul c).q ((A.add B).add (C.add D)) :=
      (Eq.map₂ Int.sub (Int.sub_mul (q.mul s) (p.mul r) v) (Int.add_mul (p.mul s) (q.mul r) u)).trans
        (congrArg (A.add B).add Int.neg_add)
    have rearrange := (congrArg (A.add B).add (Int.add_comm C D)).trans (Int.add_add_add_comm A B D C)
    have expandRight : Eq (a.mul (b.mul c)).q ((A.add D).add (B.add C)) :=
      (Eq.map₂ Int.sub (Int.mul_sub q (s.mul v) (r.mul u))
        (Int.mul_add p (r.mul v) (s.mul u))).trans
        ((Eq.map₂ Int.sub
          (Eq.map₂ Int.sub (Int.mul_assoc q s v).symm (Int.mul_assoc q r u).symm)
          (Eq.map₂ Int.add (Int.mul_assoc p r v).symm (Int.mul_assoc p s u).symm)).trans
          (congrArg (A.add D).add Int.neg_add))
    expandLeft.trans (rearrange.trans expandRight.symm)
  Eq.map₂ Coordinates.mk imaginary real

theorem mul_square (a b : Coordinates) : Eq ((a.mul b).mul (a.mul b)) ((a.mul a).mul (b.mul b)) :=
  have reorder : Eq (b.mul (a.mul b)) (a.mul (b.mul b)) :=
    (mul_assoc b a b).symm.trans
      ((congrArg (fun z : Coordinates => z.mul b) (mul_comm b a)).trans (mul_assoc a b b))
  (mul_assoc a b (a.mul b)).trans
    ((congrArg a.mul reorder).trans (mul_assoc a a (b.mul b)).symm)

end Coordinates
end Omega.Projective.Circle

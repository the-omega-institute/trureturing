/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Exact factorial moments of the squared coordinates on the unit three-sphere,
and the first three character polynomials in the squared scalar coordinate.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.PiFreeHaar

open IntRatio (Equivalent)

namespace Numerals

def two : Nat := Nat.one.succ
def three : Nat := two.succ
def four : Nat := three.succ
def five : Nat := four.succ
def seven : Nat := five.succ.succ
def eight : Nat := seven.succ
def sixteen : Nat := eight.add eight
def sixtyFour : Nat := sixteen.mul four
def oneTwentyEight : Nat := sixtyFour.add sixtyFour

end Numerals

open Numerals

def fact (n : Nat) : Nat :=
  Nat.rec Nat.one (fun k product => product.mul k.succ) n

def pow4 (n : Nat) : Nat :=
  Nat.rec Nat.one (fun _ power => power.mul four) n

def sum4 (a b c d : Nat) : Nat := ((a.add b).add c).add d
def product4 (a b c d : Nat) : Nat := ((a.mul b).mul c).mul d

/-- The even-coordinate moment with exponents `(2a, 2b, 2c, 2d)`. For
`s = a + b + c + d`, its numerator is `(2a)! (2b)! (2c)! (2d)!` and its denominator
is `4^s (s+1)! a! b! c! d!`. -/
def haarMonomial (a b c d : Nat) : IntRatio :=
  let s := sum4 a b c d
  let numerator := product4 (fact (two.mul a)) (fact (two.mul b))
    (fact (two.mul c)) (fact (two.mul d))
  let denominator := (pow4 s).mul
    ((fact s.succ).mul (product4 (fact a) (fact b) (fact c) (fact d)))
  IntRatio.value (Int.ofNat numerator) denominator

private theorem haarMonomial_congr
    {a b c d w x y z : Nat}
    (hs : Eq (sum4 a b c d) (sum4 w x y z))
    (hn : Eq (product4 (fact (two.mul a)) (fact (two.mul b))
        (fact (two.mul c)) (fact (two.mul d)))
      (product4 (fact (two.mul w)) (fact (two.mul x))
        (fact (two.mul y)) (fact (two.mul z))))
    (hd : Eq (product4 (fact a) (fact b) (fact c) (fact d))
      (product4 (fact w) (fact x) (fact y) (fact z))) :
    Eq (haarMonomial a b c d) (haarMonomial w x y z) :=
  Eq.map₂ IntRatio.value (congrArg Int.ofNat hn)
    (Eq.map₂ (fun s p => (pow4 s).mul ((fact s.succ).mul p)) hs hd)

theorem haarMonomial_swap01 (a b c d : Nat) :
    Eq (haarMonomial a b c d) (haarMonomial b a c d) :=
  haarMonomial_congr
    (congrArg (fun n : Nat => (n.add c).add d) (Nat.add_comm a b))
    (congrArg (fun n : Nat => (n.mul (fact (two.mul c))).mul (fact (two.mul d)))
      (Nat.mul_comm (fact (two.mul a)) (fact (two.mul b))))
    (congrArg (fun n : Nat => (n.mul (fact c)).mul (fact d))
      (Nat.mul_comm (fact a) (fact b)))

theorem haarMonomial_swap12 (a b c d : Nat) :
    Eq (haarMonomial a b c d) (haarMonomial a c b d) :=
  haarMonomial_congr
    (congrArg (fun n : Nat => n.add d) (Nat.add_right_comm a b c))
    (congrArg (fun n : Nat => n.mul (fact (two.mul d)))
      (Nat.mul_right_comm (fact (two.mul a)) (fact (two.mul b)) (fact (two.mul c))))
    (congrArg (fun n : Nat => n.mul (fact d))
      (Nat.mul_right_comm (fact a) (fact b) (fact c)))

theorem haarMonomial_swap23 (a b c d : Nat) :
    Eq (haarMonomial a b c d) (haarMonomial a b d c) :=
  haarMonomial_congr
    (Nat.add_right_comm (a.add b) c d)
    (Nat.mul_right_comm ((fact (two.mul a)).mul (fact (two.mul b)))
      (fact (two.mul c)) (fact (two.mul d)))
    (Nat.mul_right_comm ((fact a).mul (fact b)) (fact c) (fact d))

structure Exponents where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

/-- A composition of the adjacent transpositions of four coordinates. -/
inductive CoordinatePermutation where
  | identity
  | swap01 (rest : CoordinatePermutation)
  | swap12 (rest : CoordinatePermutation)
  | swap23 (rest : CoordinatePermutation)

def CoordinatePermutation.apply (permutation : CoordinatePermutation) (e : Exponents) : Exponents :=
  CoordinatePermutation.rec e
    (fun _ p => ⟨p.b, p.a, p.c, p.d⟩)
    (fun _ p => ⟨p.a, p.c, p.b, p.d⟩)
    (fun _ p => ⟨p.a, p.b, p.d, p.c⟩) permutation

/-- The factorial moment is invariant under every word in the generators of `S₄`. -/
theorem haarMonomial_symm (permutation : CoordinatePermutation) (e : Exponents) :
    let p := permutation.apply e
    Eq (haarMonomial p.a p.b p.c p.d) (haarMonomial e.a e.b e.c e.d) :=
  let moment := fun (p : Exponents) => haarMonomial p.a p.b p.c p.d
  CoordinatePermutation.rec (motive := fun perm => Eq (moment (perm.apply e)) (moment e))
    Eq.refl
    (fun rest ih =>
      let p := rest.apply e
      (haarMonomial_swap01 p.a p.b p.c p.d).symm.trans ih)
    (fun rest ih =>
      let p := rest.apply e
      (haarMonomial_swap12 p.a p.b p.c p.d).symm.trans ih)
    (fun rest ih =>
      let p := rest.apply e
      (haarMonomial_swap23 p.a p.b p.c p.d).symm.trans ih) permutation

def haarKappaMoment (k : Nat) : IntRatio := haarMonomial k Nat.zero Nat.zero Nat.zero

private theorem product4_axis (a : Nat) : Eq (product4 a Nat.one Nat.one Nat.one) a :=
  (Nat.mul_one ((a.mul Nat.one).mul Nat.one)).trans
    ((Nat.mul_one (a.mul Nat.one)).trans (Nat.mul_one a))

private def axisDenominator (k : Nat) : Nat :=
  (pow4 k).mul ((fact k.succ).mul (fact k))

private theorem haarKappaMoment_axis (k : Nat) :
    Eq (haarKappaMoment k) (IntRatio.value (Int.ofNat (fact (two.mul k))) (axisDenominator k)) :=
  Eq.map₂ IntRatio.value (congrArg Int.ofNat (product4_axis (fact (two.mul k))))
    (congrArg (fun n => (pow4 k).mul ((fact k.succ).mul n)) (product4_axis (fact k)))

private theorem mul_interchange (a b c d : Nat) :
    Eq ((a.mul b).mul (c.mul d)) ((a.mul c).mul (b.mul d)) :=
  have middle : Eq (b.mul (c.mul d)) (c.mul (b.mul d)) :=
    (Nat.mul_assoc b c d).symm.trans
      ((congrArg (fun n : Nat => n.mul d) (Nat.mul_comm b c)).trans (Nat.mul_assoc c b d))
  (Nat.mul_assoc a b (c.mul d)).trans
    ((congrArg a.mul middle).trans (Nat.mul_assoc a c (b.mul d)).symm)

private theorem axisDenominator_succ (k : Nat) :
    Eq (axisDenominator k.succ)
      (((axisDenominator k).mul (two.mul k.succ.succ)).mul (two.mul k.succ)) :=
  let p := pow4 k
  let a := fact k.succ
  let b := fact k
  let c := k.succ
  let d := k.succ.succ
  (congrArg (fun n => (p.mul four).mul n) (mul_interchange a d b c)).trans
    ((mul_interchange p four (a.mul b) (d.mul c)).trans
      ((congrArg (fun n => (axisDenominator k).mul n) (mul_interchange two two d c)).trans
        (Nat.mul_assoc (axisDenominator k) (two.mul d) (two.mul c)).symm))

/-- The ratio `(2k+1)/(2(k+2))` between consecutive scalar-coordinate moments. -/
def haarKappaStep (k : Nat) : IntRatio :=
  IntRatio.value (Int.ofNat (two.mul k).succ) (two.mul k.succ.succ)

theorem haarKappaMoment_succ (k : Nat) :
    Equivalent (haarKappaMoment k.succ) ((haarKappaMoment k).mul (haarKappaStep k)) :=
  let odd := (two.mul k).succ
  let scale := two.mul k.succ
  let stepDen := two.mul k.succ.succ
  let numerator := (Int.ofNat (fact (two.mul k))).mul (Int.ofNat odd)
  let denominator := (axisDenominator k).mul stepDen
  let scaled := IntRatio.value (numerator.mul (Int.ofNat scale)) (denominator.mul scale)
  have left : Eq (haarKappaMoment k.succ) scaled :=
    (haarKappaMoment_axis k.succ).trans
      (congrArg (IntRatio.value (numerator.mul (Int.ofNat scale))) (axisDenominator_succ k))
  have right : Eq ((haarKappaMoment k).mul (haarKappaStep k)) (IntRatio.value numerator denominator) :=
    (congrArg (fun r : IntRatio => r.mul (haarKappaStep k)) (haarKappaMoment_axis k)).trans
      (IntRatio.value_mul (Int.ofNat (fact (two.mul k))) (Int.ofNat odd) (axisDenominator k) stepDen)
  Eq.subst (fun r => Equivalent (haarKappaMoment k.succ) r) right.symm
    (Eq.subst (fun r => Equivalent r (IntRatio.value numerator denominator)) left.symm
      (IntRatio.value_scale numerator denominator (two.mul k).succ))

private theorem moment_step {k : Nat} {m result : IntRatio}
    (hm : Equivalent (haarKappaMoment k) m)
    (hr : Equivalent (m.mul (haarKappaStep k)) result) :
    Equivalent (haarKappaMoment k.succ) result :=
  (haarKappaMoment_succ k).trans
    ((IntRatio.mul_congr_left hm (haarKappaStep k)).trans hr)

theorem haarKappaMoment_0 : Equivalent (haarKappaMoment Nat.zero) (IntRatio.ofInt Int.one) :=
  Eq.refl

theorem haarKappaMoment_1 : Equivalent (haarKappaMoment Nat.one) (IntRatio.value Int.one four) :=
  moment_step (k := Nat.zero) haarKappaMoment_0 (IntRatio.equivalent_refl (IntRatio.value Int.one four))

theorem haarKappaMoment_2 : Equivalent (haarKappaMoment two) (IntRatio.value Int.one eight) :=
  moment_step (k := Nat.one) haarKappaMoment_1 (IntRatio.value_scale Int.one eight two)

theorem haarKappaMoment_3 :
    Equivalent (haarKappaMoment three) (IntRatio.value (Int.ofNat five) sixtyFour) :=
  moment_step (k := two) haarKappaMoment_2
    (IntRatio.equivalent_refl (IntRatio.value (Int.ofNat five) sixtyFour))

theorem haarKappaMoment_4 :
    Equivalent (haarKappaMoment four) (IntRatio.value (Int.ofNat seven) oneTwentyEight) :=
  have product := IntRatio.value_mul (Int.ofNat five) (Int.ofNat seven) sixtyFour (two.mul five)
  have regroup : Eq (sixtyFour.mul (two.mul five)) (oneTwentyEight.mul five) :=
    (Nat.mul_assoc sixtyFour two five).symm.trans
      (congrArg (fun d : Nat => d.mul five)
        (congrArg (fun d : Nat => d.add sixtyFour) (Nat.zero_add sixtyFour)))
  have scaled := product.trans
    (Eq.map₂ IntRatio.value (congrArg Int.ofNat (Nat.mul_comm five seven)) regroup)
  moment_step (k := three) (m := IntRatio.value (Int.ofNat five) sixtyFour) haarKappaMoment_3
    (Eq.subst (fun r => Equivalent r (IntRatio.value (Int.ofNat seven) oneTwentyEight))
      scaled.symm (IntRatio.value_scale (Int.ofNat seven) oneTwentyEight four))

/-- A finite list of rational coefficients in ascending degree order. -/
inductive CoefficientList where
  | nil
  | cons (head : IntRatio) (tail : CoefficientList)

namespace CoefficientList

def add (p q : CoefficientList) : CoefficientList :=
  CoefficientList.rec (motive := fun _ => CoefficientList → CoefficientList)
    (fun q => q)
    (fun a tail addTail q => CoefficientList.rec (.cons a tail)
      (fun b rest _ => .cons (a.add b) (addTail rest)) q) p q

def scale (a : IntRatio) (p : CoefficientList) : CoefficientList :=
  CoefficientList.rec .nil (fun b _ tail => .cons (a.mul b) tail) p

/-- Multiply coefficient lists by convolution. -/
def mul (p q : CoefficientList) : CoefficientList :=
  CoefficientList.rec .nil
    (fun a _ product => (q.scale a).add (.cons (IntRatio.ofInt Int.zero) product)) p

end CoefficientList

/-- Integrate a coefficient list whose first term has degree `k`. -/
def haarKappaPolyFrom (k : Nat) (p : CoefficientList) : IntRatio :=
  CoefficientList.rec (motive := fun _ => Nat → IntRatio)
    (fun _ => IntRatio.ofInt Int.zero)
    (fun a _ integrateTail k =>
      (a.mul (haarKappaMoment k)).add (integrateTail k.succ)) p k

def haarKappaPoly (p : CoefficientList) : IntRatio := haarKappaPolyFrom Nat.zero p

def haarInner (p q : CoefficientList) : IntRatio := haarKappaPoly (p.mul q)

def chi0 : CoefficientList := .cons (IntRatio.ofInt Int.one) .nil
def chi1Constant : Int := Int.one.neg
def chi1Linear : Int := Int.ofNat four

def chi1 : CoefficientList :=
  .cons (IntRatio.ofInt chi1Constant) (.cons (IntRatio.ofInt chi1Linear) .nil)
def chi2 : CoefficientList :=
  .cons (IntRatio.ofInt Int.one) (.cons (IntRatio.ofInt (Int.ofNat (three.mul four)).neg)
    (.cons (IntRatio.ofInt (Int.ofNat sixteen)) .nil))

/-- Reduce a weighted moment when its coefficient is a multiple of the moment denominator. -/
private theorem weighted_multiple (q n : Int) (d : Nat) :
    Equivalent ((IntRatio.ofInt (q.mul (IntRatio.denominator d))).mul (IntRatio.fraction n d))
      (IntRatio.ofInt (q.mul n)) :=
  let denominator := IntRatio.denominator d
  have product := (IntRatio.value_mul (q.mul denominator) n Nat.one d.succ).trans
    (congrArg (fun a => IntRatio.value a (Nat.one.mul d.succ))
      (Int.mul_right_comm q denominator n))
  Eq.subst (fun r => Equivalent r (IntRatio.ofInt (q.mul n))) product.symm
    (IntRatio.value_scale (q.mul n) Nat.one d)

private theorem integrate_multiple (k : Nat) (q n : Int) (d : Nat)
    {p : CoefficientList} {b : Int}
    (hm : Equivalent (haarKappaMoment k) (IntRatio.fraction n d))
    (hp : Equivalent (haarKappaPolyFrom k.succ p) (IntRatio.ofInt b)) :
    Equivalent (haarKappaPolyFrom k (.cons (IntRatio.ofInt (q.mul (IntRatio.denominator d))) p))
      (IntRatio.ofInt ((q.mul n).add b)) :=
  let c := IntRatio.ofInt (q.mul (IntRatio.denominator d))
  have term := (IntRatio.mul_congr (IntRatio.equivalent_refl c) hm).trans (weighted_multiple q n d)
  (IntRatio.add_congr term hp).trans (IntRatio.value_add_same (q.mul n) b Nat.one)

private theorem integrate_nil (k : Nat) :
    Equivalent (haarKappaPolyFrom k .nil) (IntRatio.ofInt Int.zero) :=
  IntRatio.equivalent_refl (IntRatio.ofInt Int.zero)

private theorem integrate_product {p q product : CoefficientList} {r : IntRatio}
    (integral : Equivalent (haarKappaPoly product) r)
    (coefficients : Eq (p.mul q) product) :
    Equivalent (haarInner p q) r :=
  Eq.subst (fun cs => Equivalent (haarKappaPoly cs) r) coefficients.symm integral

theorem haarInner_chi00 :
    Equivalent (haarInner chi0 chi0) (IntRatio.ofInt Int.one) :=
  integrate_product
    (integrate_multiple Nat.zero Int.one Int.one Nat.zero haarKappaMoment_0 (integrate_nil Nat.one))
    Eq.refl

theorem haarInner_chi01 :
    Equivalent (haarInner chi0 chi1) (IntRatio.ofInt Int.zero) :=
  integrate_product
    (integrate_multiple Nat.zero Int.one.neg Int.one Nat.zero haarKappaMoment_0
      (integrate_multiple Nat.one Int.one Int.one four.pred haarKappaMoment_1 (integrate_nil two)))
    Eq.refl

theorem haarInner_chi02 :
    Equivalent (haarInner chi0 chi2) (IntRatio.ofInt Int.zero) :=
  integrate_product
    (integrate_multiple Nat.zero Int.one Int.one Nat.zero haarKappaMoment_0
      (integrate_multiple Nat.one (Int.ofNat three).neg Int.one four.pred haarKappaMoment_1
        (integrate_multiple two Int.two Int.one eight.pred haarKappaMoment_2 (integrate_nil three))))
    Eq.refl

theorem haarInner_chi11 :
    Equivalent (haarInner chi1 chi1) (IntRatio.ofInt Int.one) :=
  integrate_product
    (integrate_multiple Nat.zero Int.one Int.one Nat.zero haarKappaMoment_0
      (integrate_multiple Nat.one Int.two.neg Int.one four.pred haarKappaMoment_1
        (integrate_multiple two Int.two Int.one eight.pred haarKappaMoment_2 (integrate_nil three))))
    Eq.refl

theorem haarInner_chi12 :
    Equivalent (haarInner chi1 chi2) (IntRatio.ofInt Int.zero) :=
  integrate_product
    (integrate_multiple Nat.zero Int.one.neg Int.one Nat.zero haarKappaMoment_0
      (integrate_multiple Nat.one (Int.ofNat four) Int.one four.pred haarKappaMoment_1
        (integrate_multiple two (Int.ofNat eight).neg Int.one eight.pred haarKappaMoment_2
          (integrate_multiple three Int.one (Int.ofNat five) sixtyFour.pred haarKappaMoment_3
            (integrate_nil four)))))
    Eq.refl

set_option maxRecDepth 1024 in
theorem haarInner_chi22 :
    Equivalent (haarInner chi2 chi2) (IntRatio.ofInt Int.one) :=
  integrate_product
    (integrate_multiple Nat.zero Int.one Int.one Nat.zero haarKappaMoment_0
      (integrate_multiple Nat.one (Int.ofNat five.succ).neg Int.one four.pred haarKappaMoment_1
        (integrate_multiple two (Int.ofNat ((eight.add three).mul two)) Int.one eight.pred haarKappaMoment_2
          (integrate_multiple three (Int.ofNat five.succ).neg (Int.ofNat five) sixtyFour.pred haarKappaMoment_3
            (integrate_multiple four Int.two (Int.ofNat seven) oneTwentyEight.pred haarKappaMoment_4
              (integrate_nil five))))))
    Eq.refl

theorem haarInner_chi10 :
    Equivalent (haarInner chi1 chi0) (IntRatio.ofInt Int.zero) :=
  Eq.subst (fun r => Equivalent r (IntRatio.ofInt Int.zero))
    (congrArg haarKappaPoly (Eq.refl : Eq (chi0.mul chi1) (chi1.mul chi0))) haarInner_chi01

theorem haarInner_chi20 :
    Equivalent (haarInner chi2 chi0) (IntRatio.ofInt Int.zero) :=
  Eq.subst (fun r => Equivalent r (IntRatio.ofInt Int.zero))
    (congrArg haarKappaPoly (Eq.refl : Eq (chi0.mul chi2) (chi2.mul chi0))) haarInner_chi02

theorem haarInner_chi21 :
    Equivalent (haarInner chi2 chi1) (IntRatio.ofInt Int.zero) :=
  Eq.subst (fun r => Equivalent r (IntRatio.ofInt Int.zero))
    (congrArg haarKappaPoly (Eq.refl : Eq (chi1.mul chi2) (chi2.mul chi1))) haarInner_chi12

/-- The six entries on and above the diagonal of the character Gram matrix. -/
theorem peter_weyl_chi012_orthonormal :
    And (Equivalent (haarInner chi0 chi0) (IntRatio.ofInt Int.one))
      (And (Equivalent (haarInner chi0 chi1) (IntRatio.ofInt Int.zero))
      (And (Equivalent (haarInner chi0 chi2) (IntRatio.ofInt Int.zero))
      (And (Equivalent (haarInner chi1 chi1) (IntRatio.ofInt Int.one))
      (And (Equivalent (haarInner chi1 chi2) (IntRatio.ofInt Int.zero))
           (Equivalent (haarInner chi2 chi2) (IntRatio.ofInt Int.one)))))) :=
  And.intro haarInner_chi00
    (And.intro haarInner_chi01
    (And.intro haarInner_chi02
    (And.intro haarInner_chi11
    (And.intro haarInner_chi12 haarInner_chi22))))

end Omega.Harmonic.PiFreeHaar

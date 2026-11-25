/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.IntRatio
public import OmegaMath.Projective.Circle.Identity

/-!
Omega original.

Signed projective overlap, spread and the rational Cayley circle.
The homogeneous denominator includes the antipode with second coordinate zero.
-/

noncomputable section

@[expose] public section

namespace Omega.Projective.Circle

def normSq (p q : Int) : Nat := (Coordinates.mk p q).normSq

def kappa (p q : Int) : IntRatio := IntRatio.value (Int.square q) (normSq p q)

def spread (p q : Int) : IntRatio := IntRatio.value (Int.square p) (normSq p q)

def cayleyX (p q : Int) : IntRatio :=
  IntRatio.value ((Int.square q).sub (Int.square p)) (normSq p q)

def cayleyY (p q : Int) : IntRatio :=
  IntRatio.value ((p.mul q).add (q.mul p)) (normSq p q)

def projectiveMul (p₁ q₁ p₂ q₂ : Int) : Coordinates :=
  (Coordinates.mk p₁ q₁).mul (Coordinates.mk p₂ q₂)

def Nonzero (p q : Int) : Prop := Or (Not (Eq p Int.zero)) (Not (Eq q Int.zero))

private theorem normSq_nonzero {p q : Int} (h : Nonzero p q) : Not (Eq (normSq p q) Nat.zero) :=
  fun hz =>
    have both := (Coordinates.normSq_zero_iff (Coordinates.mk p q)).mp hz
    h.elim (fun hp => hp both.left) (fun hq => hq both.right)

theorem kappa_undefined_iff (p q : Int) :
    Iff (Eq (kappa p q) IntRatio.undefined) (And (Eq p Int.zero) (Eq q Int.zero)) :=
  let v := IntRatio.value_undefined_iff (Int.square q) (normSq p q)
  let n := (Coordinates.mk p q).normSq_zero_iff
  Iff.intro (fun e => n.mp (v.mp e)) (fun e => v.mpr (n.mpr e))

theorem spread_undefined_iff (p q : Int) :
    Iff (Eq (spread p q) IntRatio.undefined) (And (Eq p Int.zero) (Eq q Int.zero)) :=
  let v := IntRatio.value_undefined_iff (Int.square p) (normSq p q)
  let n := (Coordinates.mk p q).normSq_zero_iff
  Iff.intro (fun e => n.mp (v.mp e)) (fun e => v.mpr (n.mpr e))

private theorem square_scale (k a : Int) :
    Eq (Int.square (k.mul a)) ((Int.square a).mul (Int.ofNat (k.natAbs.mul k.natAbs))) :=
  (congrArg Int.square (Int.mul_comm k a)).trans
    ((Int.square_mul a k).trans (congrArg (Int.square a).mul Int.natAbs_mul_self.symm))

private theorem normSq_scale (p q k : Int) :
    Eq (normSq (k.mul p) (k.mul q)) ((normSq p q).mul (k.natAbs.mul k.natAbs)) :=
  let K := k.natAbs.mul k.natAbs
  let square := fun a : Int => a.natAbs.mul a.natAbs
  let scaled := fun a : Int =>
    (congrArg (fun n : Nat => n.mul n)
      ((Int.natAbs_mul k a).trans (Nat.mul_comm k.natAbs a.natAbs))).trans
      (Nat.square_mul a.natAbs k.natAbs)
  (Eq.map₂ Nat.add (scaled p) (scaled q)).trans (Nat.add_mul (square p) (square q) K).symm

private theorem ratio_scale (p q k old scaled : Int) (hk : Not (Eq k Int.zero))
    (numerators : Eq scaled (old.mul (Int.ofNat (k.natAbs.mul k.natAbs)))) :
    IntRatio.Equivalent (IntRatio.value scaled (normSq (k.mul p) (k.mul q)))
      (IntRatio.value old (normSq p q)) :=
  let K := k.natAbs.mul k.natAbs
  have absNonzero : Not (Eq k.natAbs Nat.zero) := fun e => hk (Int.natAbs_eq_zero.mp e)
  have nonzero : Not (Eq K Nat.zero) := fun e => (Nat.mul_eq_zero.mp e).elim absNonzero absNonzero
  Eq.subst (fun v => IntRatio.Equivalent v (IntRatio.value old (normSq p q)))
    (Eq.map₂ IntRatio.value numerators (normSq_scale p q k)).symm
    (IntRatio.value_scale_of_ne_zero old (normSq p q) K nonzero)

/-- Signed common rescaling preserves overlap for all nonzero integer factors. -/
theorem kappa_scale (p q k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (kappa (k.mul p) (k.mul q)) (kappa p q) :=
  ratio_scale p q k (Int.square q) (Int.square (k.mul q)) hk (square_scale k q)

theorem spread_scale (p q k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (spread (k.mul p) (k.mul q)) (spread p q) :=
  ratio_scale p q k (Int.square p) (Int.square (k.mul p)) hk (square_scale k p)

theorem kappa_add_spread_eq_one (p q : Int) (h : Nonzero p q) :
    IntRatio.Equivalent ((kappa p q).add (spread p q)) (IntRatio.ofInt Int.one) :=
  let d := normSq p q
  have numerator := (Int.add_comm (Int.square q) (Int.square p)).trans
    (Coordinates.normSq_cast (Coordinates.mk p q)).symm
  (IntRatio.value_add_same (Int.square q) (Int.square p) d).trans
    (Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t d) (IntRatio.ofInt Int.one))
      numerator.symm (IntRatio.value_self d (normSq_nonzero h)))

theorem cayley_scale (p q k : Int) (hk : Not (Eq k Int.zero)) :
    And (IntRatio.Equivalent (cayleyX (k.mul p) (k.mul q)) (cayleyX p q))
      (IntRatio.Equivalent (cayleyY (k.mul p) (k.mul q)) (cayleyY p q)) :=
  let K := Int.ofNat (k.natAbs.mul k.natAbs)
  have squareX := (Eq.map₂ Int.sub (square_scale k q) (square_scale k p)).trans
    (Int.sub_mul (Int.square q) (Int.square p) K).symm
  have term : Eq ((k.mul p).mul (k.mul q)) ((p.mul q).mul K) :=
    (Int.mul_mul_mul_comm k p k q).trans
      ((Int.mul_comm (Int.square k) (p.mul q)).trans
        (congrArg (p.mul q).mul Int.natAbs_mul_self.symm))
  have reverseTerm : Eq ((k.mul q).mul (k.mul p)) ((q.mul p).mul K) :=
    (Int.mul_mul_mul_comm k q k p).trans
      ((Int.mul_comm (Int.square k) (q.mul p)).trans
        (congrArg (q.mul p).mul Int.natAbs_mul_self.symm))
  have squareY := (Eq.map₂ Int.add term reverseTerm).trans
    (Int.add_mul (p.mul q) (q.mul p) K).symm
  And.intro (ratio_scale p q k _ _ hk squareX) (ratio_scale p q k _ _ hk squareY)

theorem projective_circle_mul_normSq (p₁ q₁ p₂ q₂ : Int) :
    Eq ((normSq p₁ q₁).mul (normSq p₂ q₂)) (projectiveMul p₁ q₁ p₂ q₂).normSq :=
  Coordinates.mul_normSq (Coordinates.mk p₁ q₁) (Coordinates.mk p₂ q₂)

theorem projective_mul_nonzero (p₁ q₁ p₂ q₂ : Int)
    (h₁ : Nonzero p₁ q₁) (h₂ : Nonzero p₂ q₂) :
    Nonzero (projectiveMul p₁ q₁ p₂ q₂).p (projectiveMul p₁ q₁ p₂ q₂).q :=
  let product := projectiveMul p₁ q₁ p₂ q₂
  (Int.eq_zero_or_ne_zero product.p).elim
    (fun hp => Or.inr (fun hq =>
      have zero := product.normSq_zero_iff.mpr (And.intro hp hq)
      (Nat.mul_eq_zero.mp ((projective_circle_mul_normSq p₁ q₁ p₂ q₂).trans zero)).elim
        (normSq_nonzero h₁) (normSq_nonzero h₂)))
    Or.inl

theorem cayley_circle_unit (p q : Int) (h : Nonzero p q) :
    IntRatio.Equivalent (((cayleyX p q).mul (cayleyX p q)).add
      ((cayleyY p q).mul (cayleyY p q))) (IntRatio.ofInt Int.one) :=
  let a := projectiveMul p q p q
  let d := (normSq p q).mul (normSq p q)
  have norm : Eq (Int.ofNat d) ((Int.square a.q).add (Int.square a.p)) :=
    (congrArg Int.ofNat (projective_circle_mul_normSq p q p q)).trans
      (a.normSq_cast.trans (Int.add_comm (Int.square a.p) (Int.square a.q)))
  have hd : Not (Eq d Nat.zero) :=
    fun e => (Nat.mul_eq_zero.mp e).elim (normSq_nonzero h) (normSq_nonzero h)
  have combine := (IntRatio.value_add_same (Int.square a.q) (Int.square a.p) d).trans
    (Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t d) (IntRatio.ofInt Int.one))
      norm (IntRatio.value_self d hd))
  Eq.subst (fun t => IntRatio.Equivalent t (IntRatio.ofInt Int.one))
    (Eq.map₂ IntRatio.add
      (IntRatio.value_mul a.q a.q (normSq p q) (normSq p q))
      (IntRatio.value_mul a.p a.p (normSq p q) (normSq p q))).symm combine

/-- At the point at infinity, the Cayley map attains the antipode. -/
theorem cayley_antipodal_closure (p : Int) (hp : Not (Eq p Int.zero)) :
    And (IntRatio.Equivalent (kappa p Int.zero) (IntRatio.ofInt Int.zero))
      (And (IntRatio.Equivalent (spread p Int.zero) (IntRatio.ofInt Int.one))
        (And (IntRatio.Equivalent (cayleyX p Int.zero) (IntRatio.ofInt Int.one.neg))
          (IntRatio.Equivalent (cayleyY p Int.zero) (IntRatio.ofInt Int.zero)))) :=
  let d := normSq p Int.zero
  let zero := IntRatio.ofInt Int.zero
  let one := IntRatio.ofInt Int.one
  let minusOne := IntRatio.ofInt Int.one.neg
  have hd := normSq_nonzero (p := p) (q := Int.zero) (Or.inl hp)
  have square : Eq (Int.ofNat d) (Int.square p) := Int.natAbs_mul_self
  have spreadOne : IntRatio.Equivalent (spread p Int.zero) one :=
    Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t d) one)
      square (IntRatio.value_self d hd)
  have xMinusOne : IntRatio.Equivalent (cayleyX p Int.zero) minusOne :=
    Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t d) minusOne)
      ((congrArg Int.neg square).trans (Int.zero_add (Int.square p).neg).symm)
      (IntRatio.value_neg_self d hd)
  have yZero : IntRatio.Equivalent (cayleyY p Int.zero) zero :=
    Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t d) zero)
      ((Eq.map₂ Int.add (Int.mul_zero p) (Int.zero_mul p)).symm)
      (IntRatio.value_zero d hd)
  And.intro (IntRatio.value_zero d hd) (And.intro spreadOne (And.intro xMinusOne yZero))

/-- At the three causal anchors, spread reads zero, one half and one. -/
theorem spread_causal_anchors :
    And (IntRatio.Equivalent (spread Int.zero Int.one) (IntRatio.ofInt Int.zero))
      (And (IntRatio.Equivalent (spread Int.one Int.one) (IntRatio.fraction Int.one Nat.one))
        (IntRatio.Equivalent (spread Int.one Int.zero) (IntRatio.ofInt Int.one))) :=
  And.intro Eq.refl (And.intro Eq.refl Eq.refl)

/-- At the three causal anchors, overlap reads one, one half and zero. -/
theorem kappa_causal_anchors :
    And (IntRatio.Equivalent (kappa Int.zero Int.one) (IntRatio.ofInt Int.one))
      (And (IntRatio.Equivalent (kappa Int.one Int.one) (IntRatio.fraction Int.one Nat.one))
        (IntRatio.Equivalent (kappa Int.one Int.zero) (IntRatio.ofInt Int.zero))) :=
  And.intro Eq.refl (And.intro Eq.refl Eq.refl)

theorem cayley_y_numerator (p q : Int) : Eq ((p.mul q).add (q.mul p)) ((Int.two.mul p).mul q) :=
  (congrArg (p.mul q).add (Int.mul_comm q p)).trans
    ((Eq.map₂ Int.add (Int.one_mul (p.mul q)).symm (Int.one_mul (p.mul q)).symm).trans
      ((Int.add_mul Int.one Int.one (p.mul q)).symm.trans (Int.mul_assoc Int.two p q).symm))

/-- Multiplication of homogeneous pairs realizes the exact rational rotation law. -/
theorem cayley_compose (p₁ q₁ p₂ q₂ : Int) :
    let a := projectiveMul p₁ q₁ p₂ q₂
    let X₁ := cayleyX p₁ q₁
    let Y₁ := cayleyY p₁ q₁
    let X₂ := cayleyX p₂ q₂
    let Y₂ := cayleyY p₂ q₂
    And (IntRatio.Equivalent (cayleyX a.p a.q) ((X₁.mul X₂).sub (Y₁.mul Y₂)))
      (IntRatio.Equivalent (cayleyY a.p a.q) ((Y₁.mul X₂).add (X₁.mul Y₂))) :=
  let a := Coordinates.mk p₁ q₁
  let b := Coordinates.mk p₂ q₂
  let sa := a.mul a
  let sb := b.mul b
  let d := a.normSq.mul b.normSq
  have denominator := (a.mul_normSq b).symm
  have numeratorX := congrArg Coordinates.q (a.mul_square b)
  have numeratorY := congrArg Coordinates.p (a.mul_square b)
  have real := IntRatio.value_add_same (sa.q.mul sb.q) (sa.p.mul sb.p).neg d
  have imaginary := IntRatio.value_add_same (sa.p.mul sb.q) (sa.q.mul sb.p) d
  have negValue : Eq (IntRatio.value (sa.p.mul sb.p).neg d)
      (IntRatio.value (sa.p.mul sb.p) d).neg :=
    Nat.rec (motive := fun d => Eq (IntRatio.value (sa.p.mul sb.p).neg d)
      (IntRatio.value (sa.p.mul sb.p) d).neg) Eq.refl (fun _ _ => Eq.refl) d
  have realOps := Eq.map₂ IntRatio.add
    (IntRatio.value_mul sa.q sb.q a.normSq b.normSq)
    ((congrArg IntRatio.neg (IntRatio.value_mul sa.p sb.p a.normSq b.normSq)).trans negValue.symm)
  have imagOps := Eq.map₂ IntRatio.add
    (IntRatio.value_mul sa.p sb.q a.normSq b.normSq)
    (IntRatio.value_mul sa.q sb.p a.normSq b.normSq)
  have compose := fun (x y : IntRatio) (z w : Int) (hn : Eq z w)
      (ho : Eq y x) (he : IntRatio.Equivalent x (IntRatio.value w d)) =>
    Eq.subst (fun t => IntRatio.Equivalent t y) (Eq.map₂ IntRatio.value hn denominator).symm
      (Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value w d) t) ho.symm he.symm)
  And.intro (compose _ _ _ _ numeratorX realOps real) (compose _ _ _ _ numeratorY imagOps imaginary)

private theorem sub_eq_of_add_eq (x y z : Int) (h : Eq (x.add y) z) : Eq (z.sub y) x :=
  (congrArg (fun t : Int => t.sub y) h.symm).trans
    ((Int.add_assoc x y y.neg).trans
      ((congrArg x.add (Int.add_right_neg y)).trans (Int.add_zero x)))

private theorem ratio_unit_interval (a : Int) (d : Nat) (hd : Not (Eq d Nat.zero))
    (lower : Int.NonNeg a) (upper : Int.NonNeg ((Int.ofNat d).sub a)) :
    And (IntRatio.Le (IntRatio.ofInt Int.zero) (IntRatio.value a d))
      (IntRatio.Le (IntRatio.value a d) (IntRatio.ofInt Int.one)) :=
  let P := fun d => Not (Eq d Nat.zero) → Int.NonNeg ((Int.ofNat d).sub a) →
    And (IntRatio.Le (IntRatio.ofInt Int.zero) (IntRatio.value a d))
      (IntRatio.Le (IntRatio.value a d) (IntRatio.ofInt Int.one))
  (Nat.rec (motive := P) (fun h _ => False.elim (h Eq.refl))
    (fun k _ _ upper =>
      let d := Int.ofNat k.succ
      have lo : Eq ((a.mul Int.one).sub (Int.zero.mul d)) a :=
        (Eq.map₂ Int.sub (Int.mul_one a) (Int.zero_mul d)).trans (Int.add_zero a)
      have hi : Eq ((Int.one.mul d).sub (a.mul Int.one)) (d.sub a) :=
        Eq.map₂ Int.sub (Int.one_mul d) (Int.mul_one a)
      And.intro (Eq.subst Int.NonNeg lo.symm lower) (Eq.subst Int.NonNeg hi.symm upper)) d) hd upper

/-- Overlap and spread both lie in the unit interval at every projective point. -/
theorem kappa_spread_unit_interval (p q : Int) (h : Nonzero p q) :
    And (And (IntRatio.Le (IntRatio.ofInt Int.zero) (kappa p q))
      (IntRatio.Le (kappa p q) (IntRatio.ofInt Int.one)))
      (And (IntRatio.Le (IntRatio.ofInt Int.zero) (spread p q))
        (IntRatio.Le (spread p q) (IntRatio.ofInt Int.one))) :=
  let d := normSq p q
  let P := Int.square p
  let Q := Int.square q
  let norm := (Coordinates.mk p q).normSq_cast
  have upperKappa : Eq ((Int.ofNat d).sub Q) P :=
    sub_eq_of_add_eq P Q (Int.ofNat d) norm.symm
  have upperSpread : Eq ((Int.ofNat d).sub P) Q :=
    sub_eq_of_add_eq Q P (Int.ofNat d) ((Int.add_comm Q P).trans norm.symm)
  let positive := normSq_nonzero h
  And.intro
    (ratio_unit_interval Q d positive (Int.square_nonneg q)
      (Eq.subst Int.NonNeg upperKappa.symm (Int.square_nonneg p)))
    (ratio_unit_interval P d positive (Int.square_nonneg p)
      (Eq.subst Int.NonNeg upperSpread.symm (Int.square_nonneg q)))

private theorem sub_add_sub (a b c d : Int) :
    Eq ((a.add b).sub (c.add d)) ((a.sub c).add (b.sub d)) :=
  (congrArg (a.add b).add (Int.neg_add (a := c) (b := d))).trans
    (Int.add_add_add_comm a b c.neg d.neg)

private theorem difference_squares (a b : Int) :
    Eq ((a.sub b).mul (a.add b)) ((Int.square a).sub (Int.square b)) :=
  (Int.sub_mul a b (a.add b)).trans
    ((Eq.map₂ Int.sub (Int.mul_add a a b) (Int.mul_add b a b)).trans
      ((Eq.map₂ Int.sub Eq.refl
        (Int.add_comm (b.mul a) (Int.square b))).trans
        ((sub_add_sub (Int.square a) (a.mul b) (Int.square b) (b.mul a)).trans
          ((congrArg ((Int.square a).sub (Int.square b)).add
            (Int.sub_eq_zero.mpr (Int.mul_comm a b))).trans
            (Int.add_zero ((Int.square a).sub (Int.square b)))))))

private theorem sum_double (a : Int) : Eq (a.add a) (Int.two.mul a) :=
  (Eq.map₂ Int.add (Int.one_mul a).symm (Int.one_mul a).symm).trans
    (Int.add_mul Int.one Int.one a).symm

private theorem chord_factor (a b : Int) :
    And (Eq ((a.add b).add (a.sub b)) (Int.two.mul a))
      (Eq ((a.add b).sub (a.sub b)) (Int.two.mul b)) :=
  have sum := (Int.add_add_add_comm a b a b.neg).trans
    ((congrArg (a.add a).add (Int.add_right_neg b)).trans
      ((Int.add_zero (a.add a)).trans (sum_double a)))
  have diff := (sub_add_sub a b a b.neg).trans
    ((Eq.map₂ Int.add (Int.sub_self a) (congrArg b.add (Int.neg_neg b))).trans
      ((Int.zero_add (b.add b)).trans (sum_double b)))
  And.intro sum diff

private theorem cross_double (a d t : Int) :
    Eq (((Int.two.mul a).mul t).mul d) (a.mul ((Int.two.mul d).mul t)) :=
  (Int.mul_right_comm (Int.two.mul a) t d).trans
    ((congrArg (fun x : Int => x.mul t) (Int.mul_right_comm Int.two a d)).trans
      ((Int.mul_right_comm (Int.two.mul d) a t).trans
        (Int.mul_comm ((Int.two.mul d).mul t) a)))

private theorem cayley_of_common_denominator (a b : Int) (n : Nat)
    (hn : Not (Eq n Nat.zero))
    (unit : Eq ((Int.square a).add (Int.square b)) (Int.square (Int.ofNat n))) :
    Exists fun (p : Int) => Exists fun (q : Int) =>
      And (Nonzero p q) (And
        (IntRatio.Equivalent (cayleyX p q) (IntRatio.value a n))
        (IntRatio.Equivalent (cayleyY p q) (IntRatio.value b n))) :=
  let d := Int.ofNat n
  let t := d.add a
  let result := fun (p q : Int) =>
    And (Nonzero p q) (And
      (IntRatio.Equivalent (cayleyX p q) (IntRatio.value a n))
      (IntRatio.Equivalent (cayleyY p q) (IntRatio.value b n)))
  have bSq : Eq (Int.square b) ((d.sub a).mul t) :=
    (sub_eq_of_add_eq (Int.square b) (Int.square a) (Int.square d)
      ((Int.add_comm (Int.square b) (Int.square a)).trans unit)).symm.trans
      (difference_squares d a).symm
  (Int.eq_zero_or_ne_zero t).elim
    (fun ht =>
      have hbSq : Eq (Int.square b) Int.zero :=
        bSq.trans ((congrArg (d.sub a).mul ht).trans (Int.mul_zero (d.sub a)))
      have hb : Eq b Int.zero := (Int.mul_eq_zero.mp hbSq).elim (fun h => h) (fun h => h)
      have ha : Eq a d.neg := (Int.neg_eq_of_add_eq_zero ht).symm
      have antipode := cayley_antipodal_closure Int.one (Int.ofNat_succ_ne_zero Nat.zero)
      have x := Eq.subst (fun x => IntRatio.Equivalent (cayleyX Int.one Int.zero) (IntRatio.value x n))
        ha.symm (antipode.right.right.left.trans (IntRatio.value_neg_self n hn).symm)
      have y := Eq.subst (fun y => IntRatio.Equivalent (cayleyY Int.one Int.zero) (IntRatio.value y n))
        hb.symm (antipode.right.right.right.trans (IntRatio.value_zero n hn).symm)
      Exists.intro Int.one (Exists.intro Int.zero
        (show result Int.one Int.zero from And.intro (Or.inl (Int.ofNat_succ_ne_zero Nat.zero)) (And.intro x y))))
    (fun ht =>
      have coordinates : Nonzero b t := Or.inr ht
      have hnorm := normSq_nonzero coordinates
      have norm : Eq (Int.ofNat (normSq b t)) ((Int.two.mul d).mul t) :=
        ((Coordinates.mk b t).normSq_cast).trans
          ((Int.add_comm (Int.square b) (Int.square t)).trans
            ((congrArg (Int.square t).add bSq).trans
              ((Int.add_mul t (d.sub a) t).symm.trans
                (congrArg (fun x : Int => x.mul t) (chord_factor d a).left))))
      have xNum : Eq ((Int.square t).sub (Int.square b)) ((Int.two.mul a).mul t) :=
        (congrArg (Int.square t).sub bSq).trans
          ((Int.sub_mul t (d.sub a) t).symm.trans
            (congrArg (fun x : Int => x.mul t) (chord_factor d a).right))
      have x := (IntRatio.value_cross_iff _ _ _ _ hnorm hn).mpr
        ((congrArg (fun u : Int => u.mul d) xNum).trans
          ((cross_double a d t).trans (congrArg a.mul norm.symm)))
      have y := (IntRatio.value_cross_iff _ _ _ _ hnorm hn).mpr
        ((congrArg (fun u : Int => u.mul d) (cayley_y_numerator b t)).trans
          ((cross_double b d t).trans (congrArg b.mul norm.symm)))
      Exists.intro b (Exists.intro t (show result b t from And.intro coordinates (And.intro x y))))

/-- Every rational unit vector has a nonzero homogeneous Cayley representative. -/
theorem cayley_surjective (x y : IntRatio)
    (unit : IntRatio.Equivalent ((x.mul x).add (y.mul y)) (IntRatio.ofInt Int.one)) :
    Exists fun (p : Int) => Exists fun (q : Int) =>
      And (Nonzero p q) (And (IntRatio.Equivalent (cayleyX p q) x) (IntRatio.Equivalent (cayleyY p q) y)) :=
  let P := fun (x y : IntRatio) => IntRatio.Equivalent ((x.mul x).add (y.mul y)) (IntRatio.ofInt Int.one) →
    Exists fun (p : Int) => Exists fun (q : Int) =>
      And (Nonzero p q) (And (IntRatio.Equivalent (cayleyX p q) x) (IntRatio.Equivalent (cayleyY p q) y))
  (IntRatio.rec (motive := fun x => P x y) (fun h => False.elim h)
    (fun a b => IntRatio.rec (motive := fun y => P (IntRatio.fraction a b) y)
      (fun h => False.elim h)
      (fun c d h =>
        let x := IntRatio.fraction a b
        let y := IntRatio.fraction c d
        let n := b.succ.mul d.succ
        let A := a.mul (IntRatio.denominator d)
        let B := c.mul (IntRatio.denominator b)
        have hn : Not (Eq n Nat.zero) := Nat.succ_ne_zero (IntRatio.mulDenPred b d)
        have xa : IntRatio.Equivalent (IntRatio.value A n) x := IntRatio.value_scale a b.succ d
        have yb : IntRatio.Equivalent (IntRatio.value B n) y :=
          Eq.subst (fun k => IntRatio.Equivalent (IntRatio.value B k) y)
            (Nat.mul_comm d.succ b.succ) (IntRatio.value_scale c d.succ b)
        have squares := IntRatio.add_congr (IntRatio.mul_congr xa xa) (IntRatio.mul_congr yb yb)
        have combine := Eq.map₂ IntRatio.add
          (IntRatio.value_mul A A n n) (IntRatio.value_mul B B n n)
        have N : Not (Eq (n.mul n) Nat.zero) := fun e => (Nat.mul_eq_zero.mp e).elim hn hn
        have cross := (IntRatio.value_cross_iff ((Int.square A).add (Int.square B)) Int.one
          (n.mul n) Nat.one N (Nat.succ_ne_zero Nat.zero)).mp
          ((IntRatio.value_add_same (Int.square A) (Int.square B) (n.mul n)).symm.trans
            (Eq.subst (fun r => IntRatio.Equivalent r (IntRatio.ofInt Int.one)) combine (squares.trans h)))
        have unit : Eq ((Int.square A).add (Int.square B)) (Int.square (Int.ofNat n)) :=
          (Int.mul_one ((Int.square A).add (Int.square B))).symm.trans
            (cross.trans (Int.one_mul (Int.square (Int.ofNat n))))
        (cayley_of_common_denominator A B n hn unit).elim (fun p exist => exist.elim (fun q obs =>
          Exists.intro p (Exists.intro q (And.intro obs.left
            (And.intro (obs.right.left.trans xa) (obs.right.right.trans yb))))))) y) x) unit

/-- Equality of homogeneous coordinates in the rational projective line. -/
def ProjectivelyEquivalent (p q r s : Int) : Prop :=
  And (Nonzero p q) (And (Nonzero r s) (Eq (p.mul s) (r.mul q)))

/-- The Cayley coordinates identify precisely the same rational projective point. -/
theorem cayley_equivalent_iff (p q r s : Int) (h₁ : Nonzero p q) (h₂ : Nonzero r s) :
    Iff (And (IntRatio.Equivalent (cayleyX p q) (cayleyX r s))
      (IntRatio.Equivalent (cayleyY p q) (cayleyY r s))) (ProjectivelyEquivalent p q r s) :=
  let D := Int.ofNat (normSq p q)
  let E := Int.ofNat (normSq r s)
  let twoNonzero := Int.ofNat_succ_ne_zero Nat.one
  let circleAgreement := fun (p q r s : Int) =>
    And (IntRatio.Equivalent (cayleyX p q) (cayleyX r s))
      (IntRatio.Equivalent (cayleyY p q) (cayleyY r s))
  have dNonzero : Not (Eq D Int.zero) := fun h => normSq_nonzero h₁ (Int.ofNat_inj.mp h)
  have eNonzero : Not (Eq E Int.zero) := fun h => normSq_nonzero h₂ (Int.ofNat_inj.mp h)
  have cancelTwo : ∀ a b : Int, Eq ((Int.two.mul a).mul E) ((Int.two.mul b).mul D) →
      Eq (a.mul E) (b.mul D) :=
    fun a b h => Int.eq_of_mul_eq_mul_left twoNonzero
      ((Int.mul_assoc Int.two a E).symm.trans (h.trans (Int.mul_assoc Int.two b D)))
  Iff.intro
    (fun h =>
      let X := (Int.square q).sub (Int.square p)
      let Y := (Int.square s).sub (Int.square r)
      have hx := (IntRatio.value_cross_iff X Y _ _ (normSq_nonzero h₁) (normSq_nonzero h₂)).mp h.left
      have hy := (IntRatio.value_cross_iff _ _ _ _ (normSq_nonzero h₁) (normSq_nonzero h₂)).mp h.right
      have dPlus : Eq (D.add X) (Int.two.mul (Int.square q)) :=
        (congrArg (fun t : Int => t.add X)
          ((Coordinates.mk p q).normSq_cast.trans (Int.add_comm (Int.square p) (Int.square q)))).trans
          (chord_factor (Int.square q) (Int.square p)).left
      have ePlus : Eq (E.add Y) (Int.two.mul (Int.square s)) :=
        (congrArg (fun t : Int => t.add Y)
          ((Coordinates.mk r s).normSq_cast.trans (Int.add_comm (Int.square r) (Int.square s)))).trans
          (chord_factor (Int.square s) (Int.square r)).left
      have squared := cancelTwo (Int.square q) (Int.square s)
        ((congrArg (fun z : Int => z.mul E) dPlus.symm).trans
          ((Int.add_mul D X E).trans
            ((Eq.map₂ Int.add (Int.mul_comm D E) hx).trans
              ((Int.add_mul E Y D).symm.trans (congrArg (fun z : Int => z.mul D) ePlus)))))
      have pqDouble : Eq ((p.mul q).add (q.mul p)) (Int.two.mul (p.mul q)) :=
        (cayley_y_numerator p q).trans (Int.mul_assoc Int.two p q)
      have rsDouble : Eq ((r.mul s).add (s.mul r)) (Int.two.mul (r.mul s)) :=
        (cayley_y_numerator r s).trans (Int.mul_assoc Int.two r s)
      have mixed := cancelTwo (p.mul q) (r.mul s)
        ((congrArg (fun t : Int => t.mul E) pqDouble.symm).trans
          (hy.trans (congrArg (fun t : Int => t.mul D) rsDouble)))
      have cross : Eq (p.mul s) (r.mul q) :=
        (Int.eq_zero_or_ne_zero q).elim
        (fun hq =>
          have squareZero : Eq (Int.square s) Int.zero :=
            Int.eq_of_mul_eq_mul_right dNonzero
              (squared.symm.trans ((congrArg (fun x : Int => (Int.square x).mul E) hq).trans
                ((Int.zero_mul E).trans (Int.zero_mul D).symm)))
          have hs : Eq s Int.zero := (Int.mul_eq_zero.mp squareZero).elim (fun h => h) (fun h => h)
          (congrArg p.mul hs).trans
            ((Int.mul_zero p).trans ((Int.mul_zero r).symm.trans (congrArg r.mul hq.symm))))
        (fun hq =>
          have hs : Not (Eq s Int.zero) := fun hs =>
            have squareZero : Eq (Int.square q) Int.zero :=
              Int.eq_of_mul_eq_mul_right eNonzero
                (squared.trans ((congrArg (fun x : Int => (Int.square x).mul D) hs).trans
                  ((Int.zero_mul D).trans (Int.zero_mul E).symm)))
            (Int.mul_eq_zero.mp squareZero).elim hq hq
          have product : Eq ((p.mul q).mul (Int.square s)) ((r.mul s).mul (Int.square q)) :=
            Int.eq_of_mul_eq_mul_right eNonzero
              ((Int.mul_right_comm (p.mul q) (Int.square s) E).trans
                ((congrArg (fun t : Int => t.mul (Int.square s)) mixed).trans
                  ((Int.mul_assoc (r.mul s) D (Int.square s)).trans
                    ((congrArg (r.mul s).mul
                      ((Int.mul_comm D (Int.square s)).trans squared.symm)).trans
                      (Int.mul_assoc (r.mul s) (Int.square q) E).symm))))
          Int.eq_of_mul_eq_mul_right (Int.mul_ne_zero hq hs)
            ((Int.mul_mul_mul_comm p s q s).trans
              (product.trans ((Int.mul_mul_mul_comm r s q q).trans
                (congrArg (r.mul q).mul (Int.mul_comm s q))))))
      And.intro h₁ (And.intro h₂ cross))
    (fun agreement =>
      have h : Eq (p.mul s) (r.mul q) := agreement.right.right
      have zeroLeft : Eq q Int.zero → circleAgreement p q r s :=
        fun hq =>
          have hp : Not (Eq p Int.zero) :=
            fun hp => h₁.elim (fun np => np hp) (fun nq => nq hq)
          have hs : Eq s Int.zero :=
            Int.eq_of_mul_eq_mul_left hp
              (h.trans ((congrArg r.mul hq).trans ((Int.mul_zero r).trans (Int.mul_zero p).symm)))
          have hr : Not (Eq r Int.zero) :=
            fun hr => h₂.elim (fun nr => nr hr) (fun ns => ns hs)
          let a := (cayley_antipodal_closure p hp).right.right
          let b := (cayley_antipodal_closure r hr).right.right
          Eq.subst (fun q => circleAgreement p q r s) hq.symm
            (Eq.subst (circleAgreement p Int.zero r) hs.symm
              (And.intro (a.left.trans b.left.symm) (a.right.trans b.right.symm)))
      (Int.eq_zero_or_ne_zero q).elim zeroLeft (fun hq =>
        have hs : Not (Eq s Int.zero) := fun hs =>
          have hr : Eq r Int.zero := Int.eq_of_mul_eq_mul_right hq
            (h.symm.trans ((congrArg p.mul hs).trans ((Int.mul_zero p).trans (Int.zero_mul q).symm)))
          h₂.elim (fun nr => nr hr) (fun ns => ns hs)
        have first := (Int.mul_comm s p).trans (h.trans (Int.mul_comm r q))
        have second := Int.mul_comm s q
        have a := cayley_scale p q s hs
        have b := cayley_scale r s q hq
        And.intro
          (a.left.symm.trans (Eq.subst (fun t => IntRatio.Equivalent t (cayleyX r s))
            (Eq.map₂ cayleyX first second).symm b.left))
          (a.right.symm.trans (Eq.subst (fun t => IntRatio.Equivalent t (cayleyY r s))
            (Eq.map₂ cayleyY first second).symm b.right))))

end Omega.Projective.Circle

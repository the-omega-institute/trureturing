/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Calculus.DFiniteJet.Coefficients

/-!
Omega original.

The Cayley circle coordinates as formal series. The common denominator
`1 + η²` gives a first-order system whose coefficients are determined by the
initial point `(1, 0)`.
-/

noncomputable section

@[expose] public section

namespace Omega.JetSeq

/-- The formal rational function `(1 - η²) / (1 + η²)`. -/
def CayleyCos : JetSeq := Nat.rec IntRatio.one
  (fun k _ => IntRatio.ofInt (Int.two.mul (trigNumerator k.succ).cos))

/-- The formal rational function `2η / (1 + η²)`. -/
def CayleySin : JetSeq := fun k => IntRatio.ofInt (Int.two.mul (trigNumerator k).sin)

theorem cayleyCos_finite : Finite CayleyCos :=
  Nat.rec (motive := fun k => IntRatio.Finite (CayleyCos k)) True.intro (fun _ _ => True.intro)

theorem cayleySin_finite : Finite CayleySin := fun _ => True.intro

theorem cayleyCos_zero : Eq (CayleyCos Nat.zero) IntRatio.one := Eq.refl

theorem cayleySin_zero : Eq (CayleySin Nat.zero) IntRatio.zero := Eq.refl

private theorem ofInt_add (a b : Int) :
    Eq ((IntRatio.ofInt a).add (IntRatio.ofInt b)) (IntRatio.ofInt (a.add b)) :=
  congrArg IntRatio.ofInt (Eq.map₂ Int.add (Int.mul_one a) (Int.mul_one b))

private theorem neg_add_eq_zero (a : Int) :
    IntRatio.Equivalent ((IntRatio.ofInt a.neg).add (IntRatio.ofInt a)) IntRatio.zero :=
  IntRatio.ofInt_congr ((Eq.map₂ Int.add (Int.mul_one a.neg) (Int.mul_one a)).trans
    (Int.add_left_neg a))

private theorem two_neg_add_eq_zero (a : Int) :
    IntRatio.Equivalent
      ((IntRatio.ofInt (Int.two.mul a.neg)).add (IntRatio.ofInt (Int.two.mul a))) IntRatio.zero :=
  (IntRatio.add_congr_left (IntRatio.ofInt_congr (Int.mul_neg Int.two a)) _).trans
    (neg_add_eq_zero (Int.two.mul a))

private theorem cayley_cos_numerator_zero (k : Nat) :
    IntRatio.Equivalent (add one (neg (mul eta eta)) k.succ.succ.succ) IntRatio.zero :=
  IntRatio.add_congr (IntRatio.equivalent_refl IntRatio.zero)
    (IntRatio.neg_congr (mul_eta finite_eta k.succ.succ.succ))

/-- Clearing the common denominator gives the Cayley cosine numerator. -/
theorem cayleyCos_rational :
    Equivalent (mul CayleyCos oneAddEtaSq) (add one (neg (mul eta eta))) :=
  Nat.rec (motive := fun k =>
    IntRatio.Equivalent (mul CayleyCos oneAddEtaSq k) (add one (neg (mul eta eta)) k))
    (IntRatio.equivalent_refl IntRatio.one)
    (fun n _ => Nat.rec (motive := fun n =>
      IntRatio.Equivalent (mul CayleyCos oneAddEtaSq n.succ) (add one (neg (mul eta eta)) n.succ))
      (IntRatio.equivalent_refl IntRatio.zero)
      (fun j _ => Nat.rec (motive := fun j =>
        IntRatio.Equivalent (mul CayleyCos oneAddEtaSq j.succ.succ)
          (add one (neg (mul eta eta)) j.succ.succ))
        (IntRatio.equivalent_refl (IntRatio.ofInt Int.one.neg))
        (fun k _ => (mul_oneAddEtaSq_succ_succ cayleyCos_finite k.succ).trans
          ((two_neg_add_eq_zero (trigNumerator k.succ).cos).trans
            (cayley_cos_numerator_zero k).symm)) j) n)

/-- Clearing the common denominator gives the Cayley sine numerator. -/
theorem cayleySin_rational : Equivalent (mul CayleySin oneAddEtaSq) (smul IntRatio.two eta) :=
  Nat.rec (motive := fun k => IntRatio.Equivalent (mul CayleySin oneAddEtaSq k) (smul IntRatio.two eta k))
    (IntRatio.equivalent_refl IntRatio.zero)
    (fun n _ => Nat.rec (motive := fun n =>
      IntRatio.Equivalent (mul CayleySin oneAddEtaSq n.succ) (smul IntRatio.two eta n.succ))
      (IntRatio.equivalent_refl IntRatio.two)
      (fun k _ => (mul_oneAddEtaSq_succ_succ cayleySin_finite k).trans
        (two_neg_add_eq_zero (trigNumerator k).sin)) n)

/-- Multiplying the derivative by `1 + η²` clears the arctangent denominator. -/
theorem atan_ode : Equivalent (mul (deriv Atan) oneAddEtaSq) one :=
  Nat.rec (motive := fun k => IntRatio.Equivalent (mul (deriv Atan) oneAddEtaSq k) (one k))
    ((mul_oneAddEtaSq_zero (finite_deriv atan_finite)).trans (deriv_atan Nat.zero))
    (fun n _ => Nat.rec (motive := fun n =>
      IntRatio.Equivalent (mul (deriv Atan) oneAddEtaSq n.succ) (one n.succ))
      ((mul_oneAddEtaSq_one (finite_deriv atan_finite)).trans (deriv_atan Nat.one))
      (fun k _ => (mul_oneAddEtaSq_succ_succ (finite_deriv atan_finite) k).trans
        ((IntRatio.add_congr (deriv_atan k.succ.succ) (deriv_atan k)).trans
          (neg_add_eq_zero (trigNumerator k).cos))) n)

private theorem weighted_shift (k : Nat) (z : Int) :
    IntRatio.Equivalent
      (((IntRatio.ofNat k.succ.succ.succ).mul (IntRatio.ofInt (Int.two.mul z))).add
        ((IntRatio.ofNat k.succ).mul (IntRatio.ofInt (Int.two.mul z.neg))))
      (IntRatio.ofInt (Int.two.mul (Int.two.mul z))) :=
  let lowerWeight := Int.ofNat k.succ
  let upperWeight := Int.ofNat k.succ.succ.succ
  let term := Int.two.mul z
  have reduce : Eq ((upperWeight.mul term).add (lowerWeight.mul term.neg)) (Int.two.mul term) :=
    ((congrArg (fun x : Int => x.add (lowerWeight.mul term.neg)) (Int.add_mul lowerWeight Int.two term)).trans
      ((congrArg (fun x : Int => ((lowerWeight.mul term).add (Int.two.mul term)).add x)
        (Int.mul_neg lowerWeight term)).trans
        ((Int.add_right_comm (lowerWeight.mul term) (Int.two.mul term) (lowerWeight.mul term).neg).trans
          ((congrArg (fun x : Int => x.add (Int.two.mul term)) (Int.add_right_neg (lowerWeight.mul term))).trans
            (Int.zero_add (Int.two.mul term))))))
  have lower := congrArg (fun x : Int => lowerWeight.mul x) (Int.mul_neg Int.two z)
  Eq.subst (fun x => IntRatio.Equivalent x (IntRatio.ofInt (Int.two.mul term)))
    (ofInt_add (upperWeight.mul term) (lowerWeight.mul (Int.two.mul z.neg))).symm
    (IntRatio.ofInt_congr ((congrArg (Int.add (upperWeight.mul term)) lower).trans reduce))

private theorem cayley_cos_shift (k : Nat) :
    IntRatio.Equivalent ((deriv CayleyCos k.succ.succ).add (deriv CayleyCos k))
      (smul IntRatio.two.neg CayleySin k.succ.succ) :=
  let numer := (trigNumerator k.succ).cos
  have opposite : Eq numer (trigNumerator k.succ.succ.succ).cos.neg :=
    (Int.neg_neg numer).symm
  (Eq.subst (fun x => IntRatio.Equivalent
    ((deriv CayleyCos k.succ.succ).add
      ((IntRatio.ofNat k.succ).mul (IntRatio.ofInt (Int.two.mul x))))
    (IntRatio.ofInt (Int.two.mul (Int.two.mul (trigNumerator k.succ.succ.succ).cos))))
    opposite.symm (weighted_shift k (trigNumerator k.succ.succ.succ).cos)).trans
    (IntRatio.ofInt_congr ((congrArg (Int.mul Int.two)
      (Int.mul_neg Int.two (trigNumerator k.succ.succ).sin)).trans
      ((Int.mul_neg Int.two (Int.two.mul (trigNumerator k.succ.succ).sin)).trans
        (Int.neg_mul Int.two (Int.two.mul (trigNumerator k.succ.succ).sin)).symm)))

private theorem cayley_sin_shift (k : Nat) :
    IntRatio.Equivalent ((deriv CayleySin k.succ.succ).add (deriv CayleySin k))
      (smul IntRatio.two CayleyCos k.succ.succ) :=
  let numer := (trigNumerator k.succ).sin
  Eq.subst (fun x => IntRatio.Equivalent
    ((deriv CayleySin k.succ.succ).add
      ((IntRatio.ofNat k.succ).mul (IntRatio.ofInt (Int.two.mul x))))
    (smul IntRatio.two CayleyCos k.succ.succ))
    (Int.neg_neg numer) (weighted_shift k (trigNumerator k.succ.succ.succ).sin)

/-- The first Cayley equation is `(1 + η²) C' = -2 S`. -/
theorem cayley_cos_ode :
    Equivalent (mul (deriv CayleyCos) oneAddEtaSq) (smul IntRatio.two.neg CayleySin) :=
  Nat.rec (motive := fun k =>
    IntRatio.Equivalent (mul (deriv CayleyCos) oneAddEtaSq k) (smul IntRatio.two.neg CayleySin k))
    (IntRatio.equivalent_refl IntRatio.zero)
    (fun n _ => Nat.rec (motive := fun n =>
      IntRatio.Equivalent (mul (deriv CayleyCos) oneAddEtaSq n.succ)
        (smul IntRatio.two.neg CayleySin n.succ))
      (IntRatio.equivalent_refl (IntRatio.ofInt (Int.two.mul Int.two).neg))
      (fun k _ => (mul_oneAddEtaSq_succ_succ (finite_deriv cayleyCos_finite) k).trans
        (cayley_cos_shift k)) n)

/-- The second Cayley equation is `(1 + η²) S' = 2 C`. -/
theorem cayley_sin_ode :
    Equivalent (mul (deriv CayleySin) oneAddEtaSq) (smul IntRatio.two CayleyCos) :=
  Nat.rec (motive := fun k =>
    IntRatio.Equivalent (mul (deriv CayleySin) oneAddEtaSq k) (smul IntRatio.two CayleyCos k))
    (IntRatio.equivalent_refl IntRatio.two)
    (fun n _ => Nat.rec (motive := fun n =>
      IntRatio.Equivalent (mul (deriv CayleySin) oneAddEtaSq n.succ)
        (smul IntRatio.two CayleyCos n.succ))
      (IntRatio.equivalent_refl IntRatio.zero)
      (fun k _ => (mul_oneAddEtaSq_succ_succ (finite_deriv cayleySin_finite) k).trans
        (cayley_sin_shift k)) n)

private theorem add_cancel_right {a b c : IntRatio} (hc : IntRatio.Finite c)
    (h : IntRatio.Equivalent (a.add c) (b.add c)) : IntRatio.Equivalent a b :=
  have remove : ∀ x : IntRatio, IntRatio.Equivalent ((x.add c).add c.neg) x :=
    fun x => (IntRatio.add_assoc x c c.neg).trans
      ((IntRatio.add_congr (IntRatio.equivalent_refl x) (IntRatio.add_right_neg hc)).trans
        (IntRatio.add_zero x))
  (remove a).symm.trans ((IntRatio.add_congr_left h c.neg).trans (remove b))

private theorem coefficient_from_polynomial_deriv {f g : JetSeq} (hf : Finite f) (hg : Finite g)
    (k : Nat) (lower : IntRatio.Equivalent (f k.pred) (g k.pred))
    (h : IntRatio.Equivalent (mul (deriv f) oneAddEtaSq k) (mul (deriv g) oneAddEtaSq k)) :
    IntRatio.Equivalent (f k.succ) (g k.succ) :=
  have atZero := (mul_oneAddEtaSq_zero (finite_deriv hf)).symm
  have atOne := (mul_oneAddEtaSq_one (finite_deriv hf)).symm
  IntRatio.mul_cancel_left (IntRatio.unit_ofNat_succ k)
    (Nat.rec (motive := fun j => IntRatio.Equivalent (f j.pred) (g j.pred) →
      IntRatio.Equivalent (mul (deriv f) oneAddEtaSq j) (mul (deriv g) oneAddEtaSq j) →
      IntRatio.Equivalent (deriv f j) (deriv g j))
      (fun _ h => atZero.trans (h.trans (mul_oneAddEtaSq_zero (finite_deriv hg))))
      (fun n _ => Nat.rec (motive := fun j => IntRatio.Equivalent (f j) (g j) →
        IntRatio.Equivalent (mul (deriv f) oneAddEtaSq j.succ) (mul (deriv g) oneAddEtaSq j.succ) →
        IntRatio.Equivalent (deriv f j.succ) (deriv g j.succ))
        (fun _ h => atOne.trans (h.trans (mul_oneAddEtaSq_one (finite_deriv hg))))
        (fun i _ lower h =>
          have split := (mul_oneAddEtaSq_succ_succ (finite_deriv hf) i).symm.trans
            (h.trans (mul_oneAddEtaSq_succ_succ (finite_deriv hg) i))
          have earlier := IntRatio.mul_congr
            (IntRatio.equivalent_refl (IntRatio.ofNat i.succ)) lower
          add_cancel_right (finite_deriv hg i)
            ((IntRatio.add_congr (IntRatio.equivalent_refl (deriv f i.succ.succ)) earlier.symm).trans
              split)) n) k lower h)

private theorem finite_initial_value_induction (N : Nat) {P : Nat → Prop} (initial : P Nat.zero)
    (step : ∀ k, Nat.lt k N → P k → P k.pred → P k.succ) : ∀ k, Nat.le k N → P k :=
  fun k => (Nat.rec (motive := fun k =>
    And (Nat.le k N → P k) (Nat.le k.succ N → P k.succ))
    (And.intro (fun _ => initial) (fun hk => step Nat.zero hk initial initial))
    (fun k ih => And.intro ih.right (fun hk => step k.succ hk
      (ih.right (Nat.le_trans (Nat.le.step (Nat.le.refl k.succ)) hk))
      (ih.left (Nat.le_trans (Nat.le.step (Nat.le.step (Nat.le.refl k))) hk)))) k).left

/-- A degree-`N` Cayley solution is fixed by its constant coefficients and the equations below degree `N`. -/
private theorem cayley_unique_at_of_finite (N : Nat) {f g : JetSeq} (hf : Finite f) (hg : Finite g)
    (f0 : IntRatio.Equivalent (f Nat.zero) IntRatio.one)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero)
    (odeF : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv f) oneAddEtaSq k)
      (smul IntRatio.two.neg g k))
    (odeG : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv g) oneAddEtaSq k)
      (smul IntRatio.two f k)) :
    And (EquivalentAt N f CayleyCos) (EquivalentAt N g CayleySin) :=
  let Matches := fun k => And (IntRatio.Equivalent (f k) (CayleyCos k))
    (IntRatio.Equivalent (g k) (CayleySin k))
  have first : Matches Nat.zero := And.intro f0 g0
  have step : ∀ k, Nat.lt k N → Matches k → Matches k.pred → Matches k.succ :=
    fun k hk current lower =>
      have sameF := (odeF k hk).trans ((IntRatio.mul_congr
        (IntRatio.equivalent_refl IntRatio.two.neg) current.right).trans (cayley_cos_ode k).symm)
      have sameG := (odeG k hk).trans ((IntRatio.mul_congr
        (IntRatio.equivalent_refl IntRatio.two) current.left).trans (cayley_sin_ode k).symm)
      And.intro (coefficient_from_polynomial_deriv hf cayleyCos_finite k lower.left sameF)
        (coefficient_from_polynomial_deriv hg cayleySin_finite k lower.right sameG)
  have reach := finite_initial_value_induction N first step
  And.intro (fun k hk => (reach k hk).left) (fun k hk => (reach k hk).right)

private theorem finite_of_equivalent {a b : IntRatio} (h : IntRatio.Equivalent a b) (hb : b.Finite) : a.Finite :=
  (IntRatio.rec (motive := fun a => IntRatio.Equivalent a b → a.Finite)
    (IntRatio.rec (motive := fun b => b.Finite → IntRatio.Equivalent IntRatio.undefined b → False)
      (fun fb _ => fb) (fun _ _ _ eq => eq) b hb)
    (fun _ _ _ => True.intro) a) h

private theorem finite_of_add_left {a b : IntRatio} (h : (a.add b).Finite) : a.Finite :=
  (IntRatio.rec (motive := fun a => (a.add b).Finite → a.Finite)
    (fun p => p) (fun _ _ _ => True.intro) a) h

private theorem finite_of_add_right {a b : IntRatio} (h : (a.add b).Finite) : b.Finite :=
  finite_of_add_left (a := b) (b := a) (finite_of_equivalent (IntRatio.add_comm b a) h)

private theorem finite_of_mul_left {a b : IntRatio} (h : (a.mul b).Finite) : a.Finite :=
  (IntRatio.rec (motive := fun a => (a.mul b).Finite → a.Finite)
    (fun p => p) (fun _ _ _ => True.intro) a) h

private theorem finite_of_mul_right {a b : IntRatio} (h : (a.mul b).Finite) : b.Finite :=
  finite_of_mul_left (a := b) (b := a) (finite_of_equivalent (IntRatio.mul_comm b a) h)

private theorem finite_of_mul_deriv {f q : JetSeq} (k : Nat) (h : (mul (deriv f) q k).Finite) :
    (f k.succ).Finite :=
  (Nat.rec (motive := fun j => (mul (deriv f) q j).Finite → (f j.succ).Finite)
    (fun h => finite_of_mul_right (h := finite_of_mul_left (h := h)))
    (fun j _ h =>
      have s := finite_of_equivalent (mul_succ_right (deriv f) q j).symm h
      have term := finite_of_add_right (a := mul (deriv f) (tail q) j)
        (b := (deriv f j.succ).mul (q Nat.zero)) s
      have derivative := finite_of_mul_left (a := deriv f j.succ) (b := q Nat.zero) term
      finite_of_mul_right (a := IntRatio.ofNat j.succ.succ) (b := f j.succ.succ) derivative) k) h

/-- Extend the finite part of a stream by filling undefined coefficients with zero. -/
private def replace_undefined (f : JetSeq) : JetSeq :=
  fun k => IntRatio.rec (motive := fun _ => IntRatio) IntRatio.zero IntRatio.fraction (f k)

private theorem finite_replace_undefined (f : JetSeq) : Finite (replace_undefined f) :=
  fun k => IntRatio.rec (motive := fun x => (IntRatio.rec (motive := fun _ => IntRatio) IntRatio.zero IntRatio.fraction x).Finite)
    True.intro (fun _ _ => True.intro) (f k)

private theorem replace_undefined_agrees (f : JetSeq) (k : Nat) (h : (f k).Finite) :
    IntRatio.Equivalent (f k) (replace_undefined f k) :=
  (IntRatio.rec (motive := fun x => x.Finite →
    IntRatio.Equivalent x (IntRatio.rec (motive := fun _ => IntRatio) IntRatio.zero IntRatio.fraction x))
    (fun x => False.elim x) (fun a b _ => IntRatio.equivalent_refl (IntRatio.fraction a b)) (f k)) h

private theorem cayley_prefix_finite (N : Nat) {f g : JetSeq}
    (f0 : IntRatio.Equivalent (f Nat.zero) IntRatio.one)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero)
    (odeF : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv f) oneAddEtaSq k)
      (smul IntRatio.two.neg g k))
    (odeG : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv g) oneAddEtaSq k)
      (smul IntRatio.two f k)) :
    ∀ k, Nat.le k N → And (f k).Finite (g k).Finite :=
  Nat.rec (motive := fun k => Nat.le k N → And (f k).Finite (g k).Finite)
    (fun _ => And.intro (finite_of_equivalent f0 True.intro) (finite_of_equivalent g0 True.intro))
    (fun k ih hk =>
      have lower := ih (Nat.le_trans (Nat.le.step (Nat.le.refl k)) hk)
      And.intro
        (finite_of_mul_deriv k (finite_of_equivalent (odeF k hk) (IntRatio.finite_mul True.intro lower.right)))
        (finite_of_mul_deriv k (finite_of_equivalent (odeG k hk) (IntRatio.finite_mul True.intro lower.left))))

/-- The Cayley initial values and the equations below degree `N` determine the coefficients through degree `N`. -/
theorem cayley_unique_at (N : Nat) {f g : JetSeq}
    (f0 : IntRatio.Equivalent (f Nat.zero) IntRatio.one)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero)
    (odeF : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv f) oneAddEtaSq k)
      (smul IntRatio.two.neg g k))
    (odeG : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv g) oneAddEtaSq k)
      (smul IntRatio.two f k)) :
    And (EquivalentAt N f CayleyCos) (EquivalentAt N g CayleySin) :=
  have finite := cayley_prefix_finite N f0 g0 odeF odeG
  have fok : EquivalentAt N f (replace_undefined f) := fun k hk => replace_undefined_agrees f k (finite k hk).left
  have gok : EquivalentAt N g (replace_undefined g) := fun k hk => replace_undefined_agrees g k (finite k hk).right
  have transfer : ∀ {u v : JetSeq} {rate : IntRatio}, EquivalentAt N u (replace_undefined u) →
      EquivalentAt N v (replace_undefined v) →
      (∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv u) oneAddEtaSq k) (smul rate v k)) →
      ∀ k, Nat.lt k N →
        IntRatio.Equivalent (mul (deriv (replace_undefined u)) oneAddEtaSq k) (smul rate (replace_undefined v) k) :=
    fun {u _v rate} uok vok ode k hk =>
      have agree : EquivalentAt k (deriv u) (deriv (replace_undefined u)) := fun j hj =>
        IntRatio.mul_congr (IntRatio.equivalent_refl _) (uok j.succ
          (Nat.le_trans (Nat.succ_le_succ hj) hk))
      have lhs := mul_congr_at k agree ((equivalent_refl oneAddEtaSq).at k) k (Nat.le.refl k)
      have rhs := IntRatio.mul_congr (IntRatio.equivalent_refl rate)
        (vok k (Nat.le_trans (Nat.le.step (Nat.le.refl k)) hk))
      lhs.symm.trans ((ode k hk).trans rhs)
  have solved := cayley_unique_at_of_finite N
    (finite_replace_undefined f) (finite_replace_undefined g) ((fok _ (Nat.zero_le N)).symm.trans f0)
    ((gok _ (Nat.zero_le N)).symm.trans g0) (transfer fok gok odeF) (transfer gok fok odeG)
  And.intro (fun k hk => (fok k hk).trans (solved.left k hk))
    (fun k hk => (gok k hk).trans (solved.right k hk))


/-- A degree-`N` arctangent solution is fixed by its constant coefficient and its differential equation. -/
theorem atan_unique_at (N : Nat) {f : JetSeq} (hf : Finite f)
    (f0 : IntRatio.Equivalent (f Nat.zero) IntRatio.zero)
    (ode : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv f) oneAddEtaSq k) (one k)) :
    EquivalentAt N f Atan :=
  let Matches := fun k => IntRatio.Equivalent (f k) (Atan k)
  have step : ∀ k, Nat.lt k N → Matches k.pred → Matches k.succ :=
    fun k hk lower => coefficient_from_polynomial_deriv hf atan_finite k lower
      ((ode k hk).trans (atan_ode k).symm)
  finite_initial_value_induction N (P := Matches) f0 (fun k hk _ => step k hk)

end Omega.JetSeq

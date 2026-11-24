/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Calculus.Jet2.Scalar

/-!
Omega original.

Coefficient streams, their finite Cauchy product, and formal differentiation.
-/

noncomputable section

@[expose] public section

namespace Omega

def JetSeq := Nat → IntRatio

namespace JetSeq

def Equivalent (f g : JetSeq) : Prop :=
  ∀ k, IntRatio.Equivalent (f k) (g k)

/-- Matching coefficients through degree `N`, inclusive. -/
def EquivalentAt (N : Nat) (f g : JetSeq) : Prop :=
  ∀ k, Nat.le k N → IntRatio.Equivalent (f k) (g k)

/-- Every coefficient is a fraction with a positive denominator. -/
def Finite (f : JetSeq) : Prop :=
  ∀ k, IntRatio.Finite (f k)

theorem equivalent_refl (f : JetSeq) : Equivalent f f :=
  fun k => IntRatio.equivalent_refl (f k)

theorem Equivalent.symm {f g : JetSeq} (h : Equivalent f g) : Equivalent g f :=
  fun k => (h k).symm

theorem Equivalent.trans {f g h : JetSeq} (hfg : Equivalent f g) (hgh : Equivalent g h) :
    Equivalent f h :=
  fun k => (hfg k).trans (hgh k)

theorem Equivalent.at {f g : JetSeq} (h : Equivalent f g) (N : Nat) : EquivalentAt N f g :=
  fun k _ => h k

def zero : JetSeq := fun _ => IntRatio.zero

def constant (c : IntRatio) : JetSeq :=
  Nat.rec c (fun _ _ => IntRatio.zero)

def one : JetSeq := constant IntRatio.one

def tail (f : JetSeq) : JetSeq := fun k => f k.succ

/-- Shift the stream up by one degree, with zero constant coefficient. -/
def shift (f : JetSeq) : JetSeq :=
  Nat.rec IntRatio.zero (fun k _ => f k)

def eta : JetSeq := shift one

def add (f g : JetSeq) : JetSeq := fun k => (f k).add (g k)

def neg (f : JetSeq) : JetSeq := fun k => (f k).neg

def smul (a : IntRatio) (f : JetSeq) : JetSeq := fun k => a.mul (f k)

/-- Sum the products `f(i) * g(k - i)` for `0 ≤ i ≤ k`, starting at `i = 0`. -/
def mul (f g : JetSeq) (k : Nat) : IntRatio :=
  (Nat.rec (motive := fun _ => JetSeq → JetSeq → IntRatio)
    (fun f g => (f Nat.zero).mul (g Nat.zero))
    (fun n smaller f g => ((f Nat.zero).mul (g n.succ)).add (smaller (tail f) g))
    k) f g

/-- The formal derivative has coefficient `(k + 1) * f(k + 1)` at degree `k`. -/
def deriv (f : JetSeq) (k : Nat) : IntRatio := (IntRatio.ofNat k.succ).mul (f k.succ)

def oneAddEtaSq : JetSeq := add one (mul eta eta)

theorem mul_zero (f g : JetSeq) :
    Eq (mul f g Nat.zero) ((f Nat.zero).mul (g Nat.zero)) :=
  Eq.refl

theorem mul_succ (f g : JetSeq) (k : Nat) :
    Eq (mul f g k.succ) (((f Nat.zero).mul (g k.succ)).add (mul (tail f) g k)) :=
  Eq.refl

theorem add_congr {f g h i : JetSeq} (hf : Equivalent f h) (hg : Equivalent g i) :
    Equivalent (add f g) (add h i) :=
  fun k => IntRatio.add_congr (hf k) (hg k)

theorem neg_congr {f g : JetSeq} (h : Equivalent f g) : Equivalent (neg f) (neg g) :=
  fun k => IntRatio.neg_congr (h k)

theorem smul_congr {a b : IntRatio} {f g : JetSeq}
    (ha : IntRatio.Equivalent a b) (h : Equivalent f g) :
    Equivalent (smul a f) (smul b g) :=
  fun k => IntRatio.mul_congr ha (h k)

theorem deriv_congr {f g : JetSeq} (h : Equivalent f g) : Equivalent (deriv f) (deriv g) :=
  fun k => IntRatio.mul_congr (IntRatio.equivalent_refl _) (h k.succ)

theorem mul_congr_at {f g h i : JetSeq} (N : Nat)
    (hf : EquivalentAt N f h) (hg : EquivalentAt N g i) :
    EquivalentAt N (mul f g) (mul h i) :=
  have coefficient : ∀ k f g h i, EquivalentAt k f h → EquivalentAt k g i →
      IntRatio.Equivalent (mul f g k) (mul h i k) :=
    fun k => Nat.rec (motive := fun k => ∀ f g h i, EquivalentAt k f h → EquivalentAt k g i →
        IntRatio.Equivalent (mul f g k) (mul h i k))
      (fun _ _ _ _ hf hg => IntRatio.mul_congr (hf Nat.zero (Nat.zero_le _))
        (hg Nat.zero (Nat.zero_le _)))
      (fun k ih _ _ _ _ hf hg =>
        IntRatio.add_congr
          (IntRatio.mul_congr (hf Nat.zero (Nat.zero_le _)) (hg k.succ (Nat.le.refl _)))
          (ih _ _ _ _ (fun j hj => hf j.succ (Nat.succ_le_succ hj))
            (fun j hj => hg j (Nat.le.step hj)))) k
  fun k hk => coefficient k f g h i
    (fun j hj => hf j (Nat.le_trans hj hk)) (fun j hj => hg j (Nat.le_trans hj hk))

theorem mul_congr {f g h i : JetSeq} (hf : Equivalent f h) (hg : Equivalent g i) :
    Equivalent (mul f g) (mul h i) :=
  fun k => mul_congr_at k (hf.at k) (hg.at k) k (Nat.le.refl k)

theorem finite_zero : Finite zero :=
  fun _ => IntRatio.finite_ofNat Nat.zero

theorem finite_constant {c : IntRatio} (hc : IntRatio.Finite c) : Finite (constant c) :=
  Nat.rec (motive := fun k => IntRatio.Finite (constant c k))
    hc (fun _ _ => IntRatio.finite_ofNat Nat.zero)

theorem finite_one : Finite one := finite_constant (IntRatio.finite_ofNat Nat.one)

theorem finite_shift {f : JetSeq} (hf : Finite f) : Finite (shift f) :=
  Nat.rec (motive := fun k => IntRatio.Finite (shift f k))
    (IntRatio.finite_ofNat Nat.zero) (fun k _ => hf k)

theorem finite_eta : Finite eta := finite_shift finite_one

theorem finite_add {f g : JetSeq} (hf : Finite f) (hg : Finite g) : Finite (add f g) :=
  fun k => IntRatio.finite_add (hf k) (hg k)

theorem finite_neg {f : JetSeq} (hf : Finite f) : Finite (neg f) :=
  fun k => IntRatio.finite_neg (hf k)

theorem finite_smul {a : IntRatio} {f : JetSeq} (ha : IntRatio.Finite a) (hf : Finite f) :
    Finite (smul a f) :=
  fun k => IntRatio.finite_mul ha (hf k)

theorem finite_mul {f g : JetSeq} (hf : Finite f) (hg : Finite g) : Finite (mul f g) :=
  fun k => Nat.rec (motive := fun n => ∀ f, Finite f → IntRatio.Finite (mul f g n))
    (fun _ hf => IntRatio.finite_mul (hf Nat.zero) (hg Nat.zero))
    (fun n ih _ hf => IntRatio.finite_add (IntRatio.finite_mul (hf Nat.zero) (hg n.succ))
      (ih _ (fun j => hf j.succ))) k f hf

theorem finite_deriv {f : JetSeq} (hf : Finite f) : Finite (deriv f) :=
  fun k => IntRatio.finite_mul (IntRatio.finite_ofNat k.succ) (hf k.succ)

theorem finite_oneAddEtaSq : Finite oneAddEtaSq :=
  finite_add finite_one (finite_mul finite_eta finite_eta)

theorem mul_succ_right (f g : JetSeq) (k : Nat) :
    IntRatio.Equivalent (mul f g k.succ)
      ((mul f (tail g) k).add ((f k.succ).mul (g Nat.zero))) :=
  Nat.rec (motive := fun n => ∀ f, IntRatio.Equivalent (mul f g n.succ)
      ((mul f (tail g) n).add ((f n.succ).mul (g Nat.zero))))
    (fun f => IntRatio.equivalent_refl (mul f g Nat.one))
    (fun n ih f =>
      (IntRatio.add_congr (IntRatio.equivalent_refl _) (ih (tail f))).trans
        (IntRatio.add_assoc ((f Nat.zero).mul (g n.succ.succ)) (mul (tail f) (tail g) n)
          ((f n.succ.succ).mul (g Nat.zero))).symm) k f

theorem mul_comm (f g : JetSeq) : Equivalent (mul f g) (mul g f) :=
  fun k => Nat.rec (motive := fun n => ∀ f g, IntRatio.Equivalent (mul f g n) (mul g f n))
    (fun f g => IntRatio.mul_comm (f Nat.zero) (g Nat.zero))
    (fun n ih f g =>
      (IntRatio.add_congr (IntRatio.mul_comm (f Nat.zero) (g n.succ)) (ih (tail f) g)).trans
        ((IntRatio.add_comm ((g n.succ).mul (f Nat.zero)) (mul g (tail f) n)).trans
          (mul_succ_right g f n).symm)) k f g

theorem mul_add (f g h : JetSeq) : Equivalent (mul f (add g h)) (add (mul f g) (mul f h)) :=
  fun k => Nat.rec (motive := fun n => ∀ f,
      IntRatio.Equivalent (mul f (add g h) n) (add (mul f g) (mul f h) n))
    (fun f => IntRatio.mul_add (f Nat.zero) (g Nat.zero) (h Nat.zero))
    (fun n ih f =>
      (IntRatio.add_congr (IntRatio.mul_add (f Nat.zero) (g n.succ) (h n.succ))
        (ih (tail f))).trans
        (IntRatio.add_add_add_comm ((f Nat.zero).mul (g n.succ)) ((f Nat.zero).mul (h n.succ))
          (mul (tail f) g n) (mul (tail f) h n))) k f

theorem add_mul (f g h : JetSeq) : Equivalent (mul (add f g) h) (add (mul f h) (mul g h)) :=
  (mul_comm (add f g) h).trans
    ((mul_add h f g).trans (add_congr (mul_comm h f) (mul_comm h g)))

theorem mul_neg (f g : JetSeq) : Equivalent (mul f (neg g)) (neg (mul f g)) :=
  fun k => Nat.rec (motive := fun n => ∀ f,
      IntRatio.Equivalent (mul f (neg g) n) (neg (mul f g) n))
    (fun f => IntRatio.mul_neg (f Nat.zero) (g Nat.zero))
    (fun n ih f =>
      (IntRatio.add_congr (IntRatio.mul_neg (f Nat.zero) (g n.succ)) (ih (tail f))).trans
        (IntRatio.neg_add ((f Nat.zero).mul (g n.succ)) (mul (tail f) g n)).symm) k f

theorem smul_mul (a : IntRatio) (f g : JetSeq) : Equivalent (mul (smul a f) g) (smul a (mul f g)) :=
  fun k => Nat.rec (motive := fun n => ∀ f,
      IntRatio.Equivalent (mul (smul a f) g n) (smul a (mul f g) n))
    (fun f => IntRatio.mul_assoc a (f Nat.zero) (g Nat.zero))
    (fun n ih f =>
      (IntRatio.add_congr (IntRatio.mul_assoc a (f Nat.zero) (g n.succ)) (ih (tail f))).trans
        (IntRatio.mul_add a ((f Nat.zero).mul (g n.succ)) (mul (tail f) g n)).symm) k f

theorem mul_smul (a : IntRatio) (f g : JetSeq) : Equivalent (mul f (smul a g)) (smul a (mul f g)) :=
  (mul_comm f (smul a g)).trans
    ((smul_mul a g f).trans (smul_congr (IntRatio.equivalent_refl a) (mul_comm g f)))

theorem mul_assoc (f g h : JetSeq) : Equivalent (mul (mul f g) h) (mul f (mul g h)) :=
  fun k => Nat.rec (motive := fun n => ∀ f g,
      IntRatio.Equivalent (mul (mul f g) h n) (mul f (mul g h) n))
    (fun f g => IntRatio.mul_assoc (f Nat.zero) (g Nat.zero) (h Nat.zero))
    (fun n ih f g =>
      let a := f Nat.zero
      let first := a.mul ((g Nat.zero).mul (h n.succ))
      let second := a.mul (mul (tail g) h n)
      let third := mul (tail f) (mul g h) n
      have splitTail : Equivalent (tail (mul f g)) (add (smul a (tail g)) (mul (tail f) g)) :=
        fun j => IntRatio.equivalent_refl (mul f g j.succ)
      have tailProduct : IntRatio.Equivalent (mul (tail (mul f g)) h n)
          (second.add third) :=
        (mul_congr splitTail (equivalent_refl h) n).trans
          ((add_mul (smul a (tail g)) (mul (tail f) g) h n).trans
            (IntRatio.add_congr (smul_mul a (tail g) h n) (ih (tail f) g)))
      (IntRatio.add_congr (IntRatio.mul_assoc a (g Nat.zero) (h n.succ)) tailProduct).trans
        ((IntRatio.add_assoc first second third).symm.trans
          (IntRatio.add_congr
            (IntRatio.mul_add a ((g Nat.zero).mul (h n.succ)) (mul (tail g) h n)).symm
            (IntRatio.equivalent_refl third)))) k f g

theorem zero_mul {f : JetSeq} (hf : Finite f) : Equivalent (mul zero f) zero :=
  Nat.rec (motive := fun n => IntRatio.Equivalent (mul zero f n) (zero n))
    (IntRatio.zero_mul (hf Nat.zero))
    (fun n ih =>
      (IntRatio.add_congr (IntRatio.zero_mul (hf n.succ)) ih).trans
        (IntRatio.add_zero IntRatio.zero))

theorem one_mul {f : JetSeq} (hf : Finite f) : Equivalent (mul one f) f :=
  Nat.rec (motive := fun n => IntRatio.Equivalent (mul one f n) (f n))
    ((IntRatio.mul_comm IntRatio.one (f Nat.zero)).trans (IntRatio.mul_one (f Nat.zero)))
    (fun n _ =>
      (IntRatio.add_congr
        ((IntRatio.mul_comm IntRatio.one (f n.succ)).trans (IntRatio.mul_one (f n.succ)))
        (zero_mul hf n)).trans (IntRatio.add_zero (f n.succ)))

theorem mul_one {f : JetSeq} (hf : Finite f) : Equivalent (mul f one) f :=
  (mul_comm f one).trans (one_mul hf)

theorem mul_shift {f : JetSeq} (hf : Finite f) (g : JetSeq) :
    Equivalent (mul f (shift g)) (shift (mul f g)) :=
  Nat.rec (motive := fun n =>
    IntRatio.Equivalent (mul f (shift g) n) (shift (mul f g) n))
    (IntRatio.mul_zero (hf Nat.zero))
    (fun n _ => (mul_succ_right f (shift g) n).trans
      ((IntRatio.add_congr (IntRatio.equivalent_refl (mul f g n))
        (IntRatio.mul_zero (hf n.succ))).trans (IntRatio.add_zero (mul f g n))))

theorem mul_eta {f : JetSeq} (hf : Finite f) : Equivalent (mul f eta) (shift f) :=
  (mul_shift hf one).trans (Nat.rec (motive := fun n =>
    IntRatio.Equivalent (shift (mul f one) n) (shift f n))
    (IntRatio.equivalent_refl IntRatio.zero) (fun n _ => mul_one hf n))

theorem mul_eta_sq {f : JetSeq} (hf : Finite f) :
    Equivalent (mul f (mul eta eta)) (shift (shift f)) :=
  have shifted : Equivalent (mul (mul f eta) eta) (shift (shift f)) :=
    (mul_congr (mul_eta hf) (equivalent_refl eta)).trans (mul_eta (finite_shift hf))
  (mul_assoc f eta eta).symm.trans shifted

theorem mul_oneAddEtaSq {f : JetSeq} (hf : Finite f) :
    Equivalent (mul f oneAddEtaSq) (add f (shift (shift f))) :=
  (mul_add f one (mul eta eta)).trans (add_congr (mul_one hf) (mul_eta_sq hf))

theorem mul_oneAddEtaSq_zero {f : JetSeq} (hf : Finite f) :
    IntRatio.Equivalent (mul f oneAddEtaSq Nat.zero) (f Nat.zero) :=
  (mul_oneAddEtaSq hf Nat.zero).trans (IntRatio.add_zero (f Nat.zero))

theorem mul_oneAddEtaSq_one {f : JetSeq} (hf : Finite f) :
    IntRatio.Equivalent (mul f oneAddEtaSq Nat.one) (f Nat.one) :=
  (mul_oneAddEtaSq hf Nat.one).trans (IntRatio.add_zero (f Nat.one))

theorem mul_oneAddEtaSq_succ_succ {f : JetSeq} (hf : Finite f) (k : Nat) :
    IntRatio.Equivalent (mul f oneAddEtaSq k.succ.succ) ((f k.succ.succ).add (f k)) :=
  mul_oneAddEtaSq hf k.succ.succ

theorem deriv_add (f g : JetSeq) : Equivalent (deriv (add f g)) (add (deriv f) (deriv g)) :=
  fun k => IntRatio.mul_add (IntRatio.ofNat k.succ) (f k.succ) (g k.succ)

theorem deriv_neg (f : JetSeq) : Equivalent (deriv (neg f)) (neg (deriv f)) :=
  fun k => IntRatio.mul_neg (IntRatio.ofNat k.succ) (f k.succ)

private theorem mul_swap_left (a b c : IntRatio) :
    IntRatio.Equivalent (a.mul (b.mul c)) (b.mul (a.mul c)) :=
  (IntRatio.mul_assoc a b c).symm.trans
    ((IntRatio.mul_congr_left (IntRatio.mul_comm a b) c).trans (IntRatio.mul_assoc b a c))

theorem deriv_smul (a : IntRatio) (f : JetSeq) :
    Equivalent (deriv (smul a f)) (smul a (deriv f)) :=
  fun k => mul_swap_left (IntRatio.ofNat k.succ) a (f k.succ)

private theorem ofNat_succ_mul (n : Nat) (x : IntRatio) :
    IntRatio.Equivalent ((IntRatio.ofNat n.succ).mul x) (((IntRatio.ofNat n).mul x).add x) :=
  have expand : IntRatio.Equivalent (((IntRatio.ofNat n).add IntRatio.one).mul x)
      (((IntRatio.ofNat n).mul x).add x) :=
    (IntRatio.add_mul (IntRatio.ofNat n) IntRatio.one x).trans
      (IntRatio.add_congr (IntRatio.equivalent_refl _) (IntRatio.one_mul x))
  Eq.subst (fun a : IntRatio => IntRatio.Equivalent (a.mul x) (((IntRatio.ofNat n).mul x).add x))
    (IntRatio.ofNat_add n Nat.one) expand

private theorem tail_deriv (f : JetSeq) :
    Equivalent (tail (deriv f)) (add (deriv (tail f)) (tail (tail f))) :=
  fun k => ofNat_succ_mul k.succ (f k.succ.succ)

private theorem leibniz_reorder (a b c d e : IntRatio) :
    IntRatio.Equivalent (a.add ((b.add c).add (d.add e)))
      ((d.add (b.add e)).add (a.add c)) :=
  have left : IntRatio.Equivalent (a.add (b.add c)) ((a.add c).add b) :=
    (IntRatio.add_assoc a b c).symm.trans (IntRatio.add_right_comm a b c)
  (IntRatio.add_assoc a (b.add c) (d.add e)).symm.trans
    ((IntRatio.add_congr_left left (d.add e)).trans
      ((IntRatio.add_add_add_comm (a.add c) b d e).trans
        ((IntRatio.add_assoc (a.add c) d (b.add e)).trans
          (IntRatio.add_comm (a.add c) (d.add (b.add e))))))

/-- Leibniz's rule at every coefficient of a Cauchy product. -/
theorem deriv_mul (f g : JetSeq) :
    Equivalent (deriv (mul f g)) (add (mul (deriv f) g) (mul f (deriv g))) :=
  fun k => Nat.rec (motive := fun n => ∀ f, IntRatio.Equivalent (deriv (mul f g) n)
      (add (mul (deriv f) g) (mul f (deriv g)) n))
    (fun f =>
      have first : IntRatio.Equivalent (mul (deriv f) g Nat.zero) ((f Nat.one).mul (g Nat.zero)) :=
        IntRatio.mul_congr_left (IntRatio.one_mul (f Nat.one)) (g Nat.zero)
      have second : IntRatio.Equivalent (mul f (deriv g) Nat.zero) ((f Nat.zero).mul (g Nat.one)) :=
        IntRatio.mul_congr (IntRatio.equivalent_refl _) (IntRatio.one_mul (g Nat.one))
      (IntRatio.one_mul (mul f g Nat.one)).trans
        ((IntRatio.add_comm ((f Nat.zero).mul (g Nat.one)) ((f Nat.one).mul (g Nat.zero))).trans
          (IntRatio.add_congr first second).symm))
    (fun n ih f =>
      let rightHead := (f Nat.zero).mul (deriv g n.succ)
      let leftTail := mul (deriv (tail f)) g n
      let rightTail := mul (tail f) (deriv g) n
      let leftHead := (f Nat.one).mul (g n.succ)
      let doubleTail := mul (tail (tail f)) g n
      let weight := IntRatio.ofNat n.succ.succ
      have expandLeft : IntRatio.Equivalent (deriv (mul f g) n.succ)
          (rightHead.add ((leftTail.add rightTail).add (leftHead.add doubleTail))) :=
        (IntRatio.mul_add weight ((f Nat.zero).mul (g n.succ.succ)) (mul (tail f) g n.succ)).trans
          (IntRatio.add_congr (mul_swap_left weight (f Nat.zero) (g n.succ.succ))
            ((ofNat_succ_mul n.succ (mul (tail f) g n.succ)).trans
              (IntRatio.add_congr_left (ih (tail f)) (mul (tail f) g n.succ))))
      have expandTail : IntRatio.Equivalent (mul (tail (deriv f)) g n) (leftTail.add doubleTail) :=
        (mul_congr (tail_deriv f) (equivalent_refl g) n).trans
          (add_mul (deriv (tail f)) (tail (tail f)) g n)
      have expandRight : IntRatio.Equivalent (add (mul (deriv f) g) (mul f (deriv g)) n.succ)
          ((leftHead.add (leftTail.add doubleTail)).add (rightHead.add rightTail)) :=
        IntRatio.add_congr (IntRatio.add_congr
          (IntRatio.mul_congr_left (IntRatio.one_mul (f Nat.one)) (g n.succ)) expandTail)
          (IntRatio.equivalent_refl (rightHead.add rightTail))
      expandLeft.trans
        ((leibniz_reorder rightHead leftTail rightTail leftHead doubleTail).trans expandRight.symm)) k f

theorem deriv_mul_equivAt (N : Nat) (f g : JetSeq) :
    EquivalentAt N (deriv (mul f g)) (add (mul (deriv f) g) (mul f (deriv g))) :=
  (deriv_mul f g).at N

theorem deriv_congr_at {f g : JetSeq} (N : Nat) (h : EquivalentAt N.succ f g) :
    EquivalentAt N (deriv f) (deriv g) :=
  fun k hk => IntRatio.mul_congr (IntRatio.equivalent_refl _) (h k.succ (Nat.succ_le_succ hk))

theorem constant_of_deriv_zero {f : JetSeq} (h : Equivalent (deriv f) zero) :
    Equivalent f (constant (f Nat.zero)) :=
  Nat.rec (motive := fun k => IntRatio.Equivalent (f k) (constant (f Nat.zero) k))
    (IntRatio.equivalent_refl _)
    (fun k _ => IntRatio.mul_cancel_left (IntRatio.unit_ofNat_succ k)
      ((h k).trans (IntRatio.mul_zero (IntRatio.finite_ofNat k.succ)).symm))

end JetSeq
end Omega

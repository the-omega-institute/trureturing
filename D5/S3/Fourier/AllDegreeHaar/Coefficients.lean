/- GID: D5/S3/Fourier/AllDegreeHaar/Coefficients
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Integer coefficient lists with convolution and equality at every degree. -/

module
prelude
import all OmegaInit.Prelude
public import D5.S3.Fourier.PiFreeHaar.Moments
public import D5.S3.Fourier.PiFreeHaar.Hecke

/-!
Omega original.

Integer coefficient lists with convolution and equality at every degree.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.AllDegreeHaar

open PiFreeHaar
inductive Poly where
  | nil
  | cons (head : Int) (tail : Poly)

namespace Poly

def get (p : Poly) (k : Nat) : Int :=
  (Poly.rec (motive := fun _ => Nat → Int) (fun _ => Int.zero)
    (fun a _ tail k => Nat.rec a (fun k _ => tail k) k) p) k

def add (p q : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly) (fun q => q)
    (fun a p tail q => Poly.rec (.cons a p)
      (fun b q _ => .cons (a.add b) (tail q)) q) p q

def scale (a : Int) (p : Poly) : Poly :=
  Poly.rec .nil (fun b _ tail => .cons (a.mul b) tail) p

def shift (p : Poly) : Poly := .cons Int.zero p

def mul (p q : Poly) : Poly :=
  Poly.rec .nil (fun a _ tail => (scale a q).add (shift tail)) p

def neg (p : Poly) : Poly := scale Int.one.neg p

def sub (p q : Poly) : Poly := p.add q.neg

def Same (p q : Poly) : Prop := ∀ k, Eq (p.get k) (q.get k)

theorem Same.trans {p q r : Poly} (h : Same p q) (g : Same q r) : Same p r :=
  fun k => (h k).trans (g k)

theorem Same.symm {p q : Poly} (h : Same p q) : Same q p :=
  fun k => (h k).symm

theorem same_refl (p : Poly) : Same p p := fun _ => rfl

theorem cons_same {a b : Int} {p q : Poly} (h : Eq a b) (g : Same p q) :
    Same (.cons a p) (.cons b q) :=
  fun k => Nat.rec (motive := fun k => Eq ((Poly.cons a p).get k) ((Poly.cons b q).get k))
    h (fun k _ => g k) k

theorem get_add (p q : Poly) (k : Nat) : Eq ((p.add q).get k) ((p.get k).add (q.get k)) :=
  let law := fun p q k => Eq ((add p q).get k) ((Poly.get p k).add (Poly.get q k))
  (Poly.rec (motive := fun p => ∀ q k, law p q k)
    (fun q k => (Int.zero_add (q.get k)).symm)
    (fun a p ih q => Poly.rec (motive := fun q => ∀ k, law (.cons a p) q k)
      (fun k => (Int.add_zero ((Poly.cons a p).get k)).symm)
      (fun b q _ k => Nat.rec (motive := law (.cons a p) (.cons b q))
        rfl (fun k _ => ih q k) k) q) p) q k

theorem get_scale (a : Int) (p : Poly) (k : Nat) :
    Eq ((scale a p).get k) (a.mul (p.get k)) :=
  let law := fun p k => Eq ((scale a p).get k) (a.mul (Poly.get p k))
  (Poly.rec (motive := fun p => ∀ k, law p k)
    (fun _ => (Int.mul_zero a).symm)
    (fun b p ih k => Nat.rec (motive := law (.cons b p))
      rfl (fun k _ => ih k) k) p) k

theorem get_neg (p : Poly) (k : Nat) : Eq (p.neg.get k) (p.get k).neg :=
  (get_scale Int.one.neg p k).trans
    ((Int.neg_mul Int.one (p.get k)).trans (congrArg Int.neg (Int.one_mul (p.get k))))

theorem get_sub (p q : Poly) (k : Nat) :
    Eq ((p.sub q).get k) ((p.get k).sub (q.get k)) :=
  (get_add p q.neg k).trans (congrArg (p.get k).add (get_neg q k))

theorem add_congr {p q r s : Poly} (h : Same p q) (g : Same r s) :
    Same (p.add r) (q.add s) :=
  fun k => (get_add p r k).trans ((Eq.map₂ Int.add (h k) (g k)).trans (get_add q s k).symm)

theorem scale_congr (a : Int) {p q : Poly} (h : Same p q) :
    Same (scale a p) (scale a q) :=
  fun k => (get_scale a p k).trans ((congrArg a.mul (h k)).trans (get_scale a q k).symm)

theorem shift_congr {p q : Poly} (h : Same p q) : Same p.shift q.shift :=
  cons_same rfl h

theorem sub_congr {p q r s : Poly} (h : Same p q) (g : Same r s) :
    Same (p.sub r) (q.sub s) := add_congr h (scale_congr Int.one.neg g)

theorem add_assoc (p q r : Poly) : Same ((p.add q).add r) (p.add (q.add r)) :=
  fun k => (get_add (p.add q) r k).trans
    ((congrArg (fun (a : Int) => a.add (r.get k)) (get_add p q k)).trans
    ((Int.add_assoc (p.get k) (q.get k) (r.get k)).trans
    ((congrArg (p.get k).add (get_add q r k).symm).trans (get_add p (q.add r) k).symm)))

theorem add_comm (p q : Poly) : Same (p.add q) (q.add p) :=
  fun k => (get_add p q k).trans ((Int.add_comm (p.get k) (q.get k)).trans (get_add q p k).symm)

theorem add_nil (p : Poly) : Same (p.add .nil) p :=
  fun k => (get_add p .nil k).trans (Int.add_zero (p.get k))

theorem scale_zero (p : Poly) : Same (scale Int.zero p) .nil :=
  fun k => (get_scale Int.zero p k).trans (Int.zero_mul (p.get k))

theorem scale_one (p : Poly) : Same (scale Int.one p) p :=
  fun k => (get_scale Int.one p k).trans (Int.one_mul (p.get k))

theorem scale_add (a : Int) (p q : Poly) :
    Same (scale a (p.add q)) ((scale a p).add (scale a q)) :=
  fun k => (get_scale a (p.add q) k).trans
    ((congrArg a.mul (get_add p q k)).trans
    ((Int.mul_add a (p.get k) (q.get k)).trans
      ((Eq.map₂ Int.add (get_scale a p k).symm (get_scale a q k).symm).trans
        (get_add (scale a p) (scale a q) k).symm)))

theorem add_scale (a b : Int) (p : Poly) :
    Same (scale (a.add b) p) ((scale a p).add (scale b p)) :=
  fun k => (get_scale (a.add b) p k).trans
    ((Int.add_mul a b (p.get k)).trans
      ((Eq.map₂ Int.add (get_scale a p k).symm (get_scale b p k).symm).trans
        (get_add (scale a p) (scale b p) k).symm))

theorem scale_scale (a b : Int) (p : Poly) :
    Same (scale a (scale b p)) (scale b (scale a p)) :=
  fun k => (get_scale a (scale b p) k).trans
    ((congrArg a.mul (get_scale b p k)).trans
      ((Int.mul_assoc a b (p.get k)).symm.trans
        ((congrArg (fun (x : Int) => x.mul (p.get k)) (Int.mul_comm a b)).trans
          ((Int.mul_assoc b a (p.get k)).trans
            ((congrArg b.mul (get_scale a p k).symm).trans (get_scale b (scale a p) k).symm)))))

theorem shift_nil : Same (shift .nil) .nil :=
  fun k => Nat.rec (motive := fun k => Eq ((shift .nil).get k) Int.zero)
    rfl (fun _ _ => rfl) k

theorem shift_add (p q : Poly) : Same (shift (p.add q)) ((shift p).add (shift q)) :=
  cons_same (Int.add_zero Int.zero).symm (same_refl _)

theorem scale_shift (a : Int) (p : Poly) : Same (scale a (shift p)) (shift (scale a p)) :=
  cons_same (Int.mul_zero a) (same_refl _)

theorem add_interchange (p q r s : Poly) :
    Same ((p.add q).add (r.add s)) ((p.add r).add (q.add s)) :=
  ((add_assoc p q (r.add s)).trans
    (add_congr (same_refl p) ((add_assoc q r s).symm.trans
      ((add_congr (add_comm q r) (same_refl s)).trans (add_assoc r q s))))).trans
    (add_assoc p r (q.add s)).symm

theorem mul_nil (p : Poly) : Same (p.mul .nil) .nil :=
  Poly.rec (motive := fun p => Same (mul p .nil) .nil) (same_refl _)
    (fun _ _ ih => (shift_congr ih).trans shift_nil) p

theorem mul_shift_left (p q : Poly) : Same ((shift p).mul q) (shift (p.mul q)) :=
  (add_congr (scale_zero q) (same_refl _))

theorem mul_cons_right (p : Poly) (a : Int) (q : Poly) :
    Same (p.mul (.cons a q)) ((scale a p).add (shift (p.mul q))) :=
  Poly.rec (motive := fun p => Same (mul p (.cons a q)) ((scale a p).add (shift (mul p q))))
    shift_nil.symm
    (fun b p ih =>
      cons_same (congrArg (fun (x : Int) => x.add Int.zero) (Int.mul_comm b a))
        ((add_congr (same_refl (scale b q)) ih).trans
          ((add_assoc (scale b q) (scale a p) (shift (p.mul q))).symm.trans
            ((add_congr (add_comm (scale b q) (scale a p)) (same_refl _)).trans
              (add_assoc (scale a p) (scale b q) (shift (p.mul q))))))) p

theorem mul_comm (p q : Poly) : Same (p.mul q) (q.mul p) :=
  (Poly.rec (motive := fun p => ∀ q, Same (mul p q) (mul q p))
    (fun q => (mul_nil q).symm)
    (fun a p ih q => (add_congr (same_refl _) (shift_congr (ih q))).trans
      (mul_cons_right q a p).symm) p) q

theorem mul_add (p q r : Poly) : Same (p.mul (q.add r)) ((p.mul q).add (p.mul r)) :=
  Poly.rec (motive := fun p => Same (mul p (q.add r)) ((mul p q).add (mul p r)))
    (same_refl _)
    (fun a p ih =>
      (add_congr (scale_add a q r) ((shift_congr ih).trans (shift_add (p.mul q) (p.mul r)))).trans
        (add_interchange (scale a q) (scale a r) (shift (p.mul q)) (shift (p.mul r)))) p

theorem mul_scale (a : Int) (p q : Poly) : Same (p.mul (scale a q)) (scale a (p.mul q)) :=
  Poly.rec (motive := fun p => Same (mul p (scale a q)) (scale a (mul p q)))
    (same_refl _)
    (fun b p ih =>
      (add_congr (scale_scale b a q) ((shift_congr ih).trans (scale_shift a (p.mul q)).symm)).trans
        (scale_add a (scale b q) (shift (p.mul q))).symm) p

theorem mul_sub_left (p q r : Poly) : Same ((p.sub q).mul r) ((p.mul r).sub (q.mul r)) :=
  (mul_comm (p.sub q) r).trans ((mul_add r p q.neg).trans
    (add_congr (mul_comm r p)
        ((mul_scale Int.one.neg r q).trans (scale_congr Int.one.neg (mul_comm r q)))))

theorem shift_mul_right (p q : Poly) : Same (p.mul q.shift) (p.mul q).shift :=
  (mul_comm p q.shift).trans ((mul_shift_left q p).trans (shift_congr (mul_comm q p)))

def ratios (p : Poly) : CoefficientList :=
  Poly.rec .nil (fun a _ q => .cons (IntRatio.ofInt a) q) p

private theorem integral_denominator : Eq Nat.zero (IntRatio.mulDenPred .zero .zero) :=
  ((Nat.add_zero _).trans (Nat.mul_zero Nat.one)).symm

theorem ratios_add (p q : Poly) : Eq (ratios (p.add q)) ((ratios p).add (ratios q)) :=
  (Poly.rec (motive := fun p => ∀ q, Eq (ratios (p.add q)) ((ratios p).add (ratios q)))
    (fun _ => rfl)
    (fun a p ih q => Poly.rec
      (motive := fun q => Eq (ratios ((cons a p).add q)) ((ratios (cons a p)).add (ratios q)))
      rfl
      (fun b q _ => Eq.map₂ CoefficientList.cons
        (Eq.map₂ IntRatio.fraction (Eq.map₂ Int.add (Int.mul_one a).symm (Int.mul_one b).symm)
          integral_denominator)
        (ih q)) q) p) q

theorem ratios_scale (a : Int) (p : Poly) :
    Eq (ratios (scale a p)) ((ratios p).scale (IntRatio.ofInt a)) :=
  Poly.rec (motive := fun p => Eq (ratios (scale a p)) ((ratios p).scale (IntRatio.ofInt a)))
    rfl (fun b _ ih => Eq.map₂ CoefficientList.cons (congrArg (IntRatio.fraction (a.mul b)) integral_denominator) ih) p

theorem ratios_mul (p q : Poly) : Eq (ratios (p.mul q)) ((ratios p).mul (ratios q)) :=
  Poly.rec (motive := fun p => Eq (ratios (p.mul q)) ((ratios p).mul (ratios q))) rfl
    (fun a p ih => (ratios_add (scale a q) (shift (p.mul q))).trans
      (Eq.map₂ CoefficientList.add (ratios_scale a q) (congrArg (CoefficientList.cons _) ih))) p

def ratioCoeff (p : CoefficientList) (k : Nat) : IntRatio :=
  (CoefficientList.rec (motive := fun _ => Nat → IntRatio) (fun _ => IntRatio.ofInt Int.zero)
    (fun a _ tail k => Nat.rec a (fun k _ => tail k) k) p) k

def RatioSame (p q : CoefficientList) : Prop :=
  ∀ k, IntRatio.Equivalent (ratioCoeff p k) (ratioCoeff q k)

theorem ratios_coeff (p : Poly) (k : Nat) :
    Eq (ratioCoeff (ratios p) k) (IntRatio.ofInt (p.get k)) :=
  (Poly.rec (motive := fun p => ∀ k, Eq (ratioCoeff (ratios p) k) (IntRatio.ofInt (p.get k)))
    (fun _ => rfl)
    (fun a p ih k => Nat.rec
      (motive := fun k => Eq (ratioCoeff (ratios (.cons a p)) k)
        (IntRatio.ofInt ((Poly.cons a p).get k)))
      rfl (fun k _ => ih k) k) p) k

theorem ratio_same {p q : Poly} (h : Same p q) : RatioSame (ratios p) (ratios q) :=
  fun k => Eq.subst (motive := fun a => IntRatio.Equivalent a (ratioCoeff (ratios q) k))
    (ratios_coeff p k).symm (Eq.subst
      (motive := fun b => IntRatio.Equivalent (IntRatio.ofInt (p.get k)) b) (ratios_coeff q k).symm
      (IntRatio.ofInt_congr (h k)))

end Poly
end Omega.Harmonic.AllDegreeHaar

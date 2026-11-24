module
prelude
public import OmegaMath.Geometry.BargmannGram.Identities
import OmegaMath.Geometry.BargmannGram.Polynomial

/-!
Omega original.

Each nonzero signed scale cancels against the corresponding norm square in the
projective fidelity and the cyclic three-point invariant.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

open Polynomial

private theorem cancel_square (k num original : Int) (d e : Nat)
    (hk : Not (Eq k Int.zero))
    (hnum : Eq num (original.mul (Int.square k)))
    (hden : Eq e (d.mul (k.natAbs.mul k.natAbs))) :
    IntRatio.Equivalent (IntRatio.value num e) (IntRatio.value original d) :=
  let n := k.natAbs.mul k.natAbs
  have h := fun hz => hk (Int.natAbs_eq_zero.mp
    (((Nat.mul_eq_zero (a := k.natAbs) (b := k.natAbs)).mp hz).elim (fun h => h) (fun h => h)))
  have congr : Eq (IntRatio.value num e) (IntRatio.value (original.mul (Int.ofNat n)) (d.mul n)) :=
    Eq.map₂ IntRatio.value (hnum.trans (congrArg original.mul Int.natAbs_mul_self.symm)) hden
  Eq.subst (fun r => IntRatio.Equivalent r (IntRatio.value original d)) congr.symm
    (IntRatio.value_scale_of_ne_zero original d n h)

private theorem norm_scale_factor (k : Int) (a b : Quad4) :
    Eq ((Quad4.scale k a).normSq.mul b.normSq)
      ((a.normSq.mul b.normSq).mul (k.natAbs.mul k.natAbs)) :=
  let n := k.natAbs.mul k.natAbs
  (congrArg (fun x : Nat => x.mul b.normSq)
    ((Quad4.normSq_scale k a).trans (Nat.mul_assoc k.natAbs k.natAbs a.normSq).symm)).trans
    ((Nat.mul_assoc n a.normSq b.normSq).trans (Nat.mul_comm n (a.normSq.mul b.normSq)))

private theorem kappa_scale_left (k : Int) (a b : Quad4) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (kappa (Quad4.scale k a) b) (kappa a b) :=
  cancel_square k _ _ _ _ hk
    ((congrArg Int.square (Quad4.dot_scale_left k a b)).trans
      ((Int.square_mul k (a.dot b)).trans (Int.mul_comm (Int.square k) (Int.square (a.dot b)))))
    (norm_scale_factor k a b)

private theorem kappa_comm (a b : Quad4) : Eq (kappa a b) (kappa b a) :=
  Eq.map₂ IntRatio.value (congrArg Int.square (a.dot_comm b)) (Nat.mul_comm a.normSq b.normSq)

theorem kappa_scale (a b : Quad4) (k l : Int)
    (hk : Not (Eq k Int.zero)) (hl : Not (Eq l Int.zero)) :
    IntRatio.Equivalent (kappa (Quad4.scale k a) (Quad4.scale l b)) (kappa a b) :=
  (kappa_scale_left k a (Quad4.scale l b) hk).trans
    (Eq.subst (fun x => IntRatio.Equivalent x (kappa a b)) (kappa_comm a (Quad4.scale l b)).symm
      (Eq.subst (fun x => IntRatio.Equivalent (kappa (Quad4.scale l b) a) x)
        (kappa_comm b a) (kappa_scale_left l b a hl)))

private theorem bargmann_scale_first (a b c : Quad4) (k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (bargmann3 (Quad4.scale k a) b c) (bargmann3 a b c) :=
  let p := a.dot b
  let q := b.dot c
  let r := c.dot a
  let v := Expr.bind k (Expr.bind p (Expr.bind q (Expr.bind r (fun _ => Int.zero))))
  let K := Expr.var Nat.zero
  let P := Expr.var Nat.zero.succ
  let Q := Expr.var Nat.zero.succ.succ
  let R := Expr.var Nat.zero.succ.succ.succ
  have numer := (Eq.map₂ Int.mul (congrArg (fun (x : Int) => x.mul q) (Quad4.dot_scale_left k a b))
    (Quad4.dot_scale_right k c a)).trans
      (Expr.certify v (((K.mul P).mul Q).mul (K.mul R)) (((P.mul Q).mul R).mul K.sq) Eq.refl)
  have denom := (congrArg (fun x : Nat => x.mul c.normSq) (norm_scale_factor k a b)).trans
    (Nat.mul_right_comm (a.normSq.mul b.normSq) (k.natAbs.mul k.natAbs) c.normSq)
  cancel_square k _ _ _ _ hk numer denom

private theorem bargmann_rotate (a b c : Quad4) : Eq (bargmann3 a b c) (bargmann3 b c a) :=
  let p := a.dot b
  let q := b.dot c
  let r := c.dot a
  Eq.map₂ IntRatio.value
    ((Int.mul_assoc p q r).trans (Int.mul_comm p (q.mul r)))
    ((Nat.mul_assoc a.normSq b.normSq c.normSq).trans (Nat.mul_comm a.normSq (b.normSq.mul c.normSq)))

private theorem bargmann_scale_second (a b c : Quad4) (k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (bargmann3 a (Quad4.scale k b) c) (bargmann3 a b c) :=
  Eq.subst (fun x => IntRatio.Equivalent x (bargmann3 a b c))
    (bargmann_rotate a (Quad4.scale k b) c).symm
    (Eq.subst (fun x => IntRatio.Equivalent (bargmann3 (Quad4.scale k b) c a) x)
      (bargmann_rotate a b c).symm (bargmann_scale_first b c a k hk))

private theorem bargmann_scale_third (a b c : Quad4) (k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (bargmann3 a b (Quad4.scale k c)) (bargmann3 a b c) :=
  Eq.subst (fun x => IntRatio.Equivalent x (bargmann3 a b c))
    (bargmann_rotate a b (Quad4.scale k c)).symm
    (Eq.subst (fun x => IntRatio.Equivalent (bargmann3 b (Quad4.scale k c) a) x)
      (bargmann_rotate a b c).symm (bargmann_scale_second b c a k hk))

theorem bargmann3_scale (a b c : Quad4) (k l m : Int)
    (hk : Not (Eq k Int.zero)) (hl : Not (Eq l Int.zero)) (hm : Not (Eq m Int.zero)) :
    IntRatio.Equivalent (bargmann3 (Quad4.scale k a) (Quad4.scale l b) (Quad4.scale m c))
      (bargmann3 a b c) :=
  (bargmann_scale_first a (Quad4.scale l b) (Quad4.scale m c) k hk).trans
    ((bargmann_scale_second a b (Quad4.scale m c) l hl).trans (bargmann_scale_third a b c m hm))

theorem detGram3_scale (a b c : Quad4) (k l m : Int)
    (hk : Not (Eq k Int.zero)) (hl : Not (Eq l Int.zero)) (hm : Not (Eq m Int.zero)) :
    IntRatio.Equivalent (detGram3 (Quad4.scale k a) (Quad4.scale l b) (Quad4.scale m c))
      (detGram3 a b c) :=
  IntRatio.sub_congr
    (IntRatio.add_congr (IntRatio.equivalent_refl _) (IntRatio.mul_congr
      (IntRatio.equivalent_refl _) (bargmann3_scale a b c k l m hk hl hm)))
    (IntRatio.add_congr (IntRatio.add_congr (kappa_scale a b k l hk hl) (kappa_scale b c l m hl hm))
      (kappa_scale c a m k hm hk))

end Omega.Geometry.BargmannGram

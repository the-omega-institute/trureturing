module
prelude
public import OmegaMath.Geometry.BargmannGram.Determinant
public import OmegaMath.Geometry.BargmannGram.Scaling
import OmegaMath.Geometry.BargmannGram.Fractions

/-!
Omega original.

Bargmann invariants and projective great-circle doubling on integer quaternions.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

def doublingReadout (a b : Quad4) : IntRatio :=
  ((IntRatio.ofInt Int.two).mul (kappa a b)).sub (IntRatio.ofInt Int.one)

theorem geodesic_doubling_kappa (a b : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) :
    IntRatio.Equivalent (kappa a (triad b a b))
      ((doublingReadout a b).mul (doublingReadout a b)) :=
  let A := a.normSq
  let B := b.normSq
  let D := A.mul B
  let p := a.dot b
  let n := (Int.two.mul (Int.square p)).sub (Int.ofNat D)
  let target := IntRatio.value n D
  have hD := nat_mul_ne_zero (a.normSq_ne_zero ha) (b.normSq_ne_zero hb)
  have castD : Eq (Int.ofNat D) ((b.dot b).mul (a.dot a)) :=
    (Eq.map₂ Int.mul a.normSq_cast b.normSq_cast).trans (Int.mul_comm (a.dot a) (b.dot b))
  have dotC : Eq (a.dot (triad b a b)) n :=
    (dot_triad_left a b).trans (congrArg (Int.two.mul (Int.square p)).sub castD.symm)
  have denominator : Eq (A.mul (triad b a b).normSq) (D.mul D) :=
    (congrArg A.mul (normSq_triad a b)).trans
      ((Nat.mul_assoc A D B).symm.trans
        ((congrArg (fun (n : Nat) => n.mul B) (Nat.mul_comm A D)).trans (Nat.mul_assoc D A B)))
  have fidelity : Eq (kappa a (triad b a b)) (target.mul target) :=
    (Eq.map₂ IntRatio.value (congrArg Int.square dotC) denominator).trans
      (IntRatio.value_mul n n D D).symm
  have scale : Eq ((IntRatio.ofInt Int.two).mul (kappa a b))
      (IntRatio.value (Int.two.mul (Int.square p)) D) :=
    value_mul_int Int.two (Int.square p) D
  have unit : IntRatio.Equivalent (IntRatio.ofInt Int.one) (IntRatio.value (Int.ofNat D) D) :=
    (value_const Int.one D hD).trans
      (Eq.subst (fun s => IntRatio.Equivalent (IntRatio.value (Int.one.mul (Int.ofNat D)) D)
        (IntRatio.value s D)) (Int.one_mul (Int.ofNat D)) (IntRatio.equivalent_refl _))
  have readout : IntRatio.Equivalent (doublingReadout a b) target :=
    (IntRatio.sub_congr
      (Eq.subst (fun x => IntRatio.Equivalent x (IntRatio.value (Int.two.mul (Int.square p)) D))
        scale.symm (IntRatio.equivalent_refl _)) unit).trans (value_sub_same _ _ D)
  Eq.subst (fun r => IntRatio.Equivalent r ((doublingReadout a b).mul (doublingReadout a b)))
    fidelity.symm (IntRatio.mul_congr readout.symm readout.symm)

end Omega.Geometry.BargmannGram

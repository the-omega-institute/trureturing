/- GID: D5/S3/Geometry/BargmannGram/PureTetrahedron
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Rational pure quaternion coordinates exclude a regular tetrahedral triple. -/

module
prelude
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude
public import D5.S3.Geometry.BargmannGram.Identities
import D5.S3.Arith.Euclidean.SquareObstruction
import D5.S3.Geometry.BargmannGram.Polynomial

/-!
Omega original.

Three unit vectors with pairwise inner product `-1/3` cannot have rational
coordinates in the pure-imaginary quaternion subspace.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

open Polynomial

private abbrev four : Nat := Nat.one.succ.succ.succ
private abbrev three : Nat := Nat.one.succ.succ
private abbrev sixteen : Nat := four.mul four
private abbrev fortyEight : Nat := three.mul sixteen

private def gramSize (a b c : Quad4) : Int :=
  gramNumerator (a.dot a) (b.dot b) (c.dot c) (a.dot b) (b.dot c) (c.dot a)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem gram_of_equal_negative_pairing (t : Nat) :
    Eq (gramNumerator (Int.ofNat (three.mul t)) (Int.ofNat (three.mul t))
      (Int.ofNat (three.mul t)) (Int.ofNat t).neg (Int.ofNat t).neg (Int.ofNat t).neg)
      (Int.ofNat (sixteen.mul ((t.mul t).mul t))) :=
  let value := Expr.var Nat.zero
  let diag := (Expr.const (Int.ofNat three)).mul value
  let off := value.neg
  let gram := (((diag.mul diag).mul diag).add ((Expr.const Int.two).mul
    ((off.mul off).mul off))).sub
      (((off.sq.mul diag).add (off.sq.mul diag)).add (off.sq.mul diag))
  Expr.certify (Expr.bind (Int.ofNat t) (fun _ => Int.zero)) gram
    ((Expr.const (Int.ofNat sixteen)).mul (value.sq.mul value)) rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem square_relation (determinant scale denominator : Nat)
    (hgram : Eq (determinant.mul determinant) (sixteen.mul ((scale.mul scale).mul scale)))
    (hscale : Eq (denominator.mul denominator) (three.mul scale)) :
    Eq ((three.mul determinant).mul (three.mul determinant))
      (three.mul (((four.mul scale).mul denominator).mul ((four.mul scale).mul denominator))) :=
  let d := Expr.var Nat.zero
  let t := Expr.var Nat.one
  let n := Expr.var Nat.one.succ
  let threeExpr := Expr.const (Int.ofNat three)
  let fourExpr := Expr.const (Int.ofNat four)
  let nine := three.mul three
  let nineExpr := Expr.const (Int.ofNat nine)
  let sixteenExpr := Expr.const (Int.ofNat sixteen)
  let fortyEightExpr := Expr.const (Int.ofNat fortyEight)
  let environment := Expr.bind (Int.ofNat determinant)
    (Expr.bind (Int.ofNat scale) (Expr.bind (Int.ofNat denominator) (fun _ => Int.zero)))
  have left := Expr.certify environment ((threeExpr.mul d).sq) (nineExpr.mul d.sq) rfl
  have right := Expr.certify environment (threeExpr.mul (((fourExpr.mul t).mul n).sq))
    ((fortyEightExpr.mul t.sq).mul n.sq) rfl
  have cubic := Expr.certify environment (nineExpr.mul (sixteenExpr.mul (t.sq.mul t)))
    ((fortyEightExpr.mul t.sq).mul (threeExpr.mul t)) rfl
  Int.ofNat_inj.mp (left.trans ((congrArg (Int.mul (Int.ofNat nine))
    (congrArg Int.ofNat hgram)).trans (cubic.trans
      ((congrArg (Int.mul (Int.ofNat (fortyEight.mul (scale.mul scale))))
        (congrArg Int.ofNat hscale.symm)).trans right.symm))))

/-- No three vectors in the pure-imaginary coordinates have the tetrahedral Gram matrix
after rational normalization with a common nonzero denominator. -/
theorem no_pure_tetrahedral_gram (a b c : Quad4) (denominator : Nat)
    (hden : Not (Eq denominator Nat.zero))
    (ha : Eq a.w Int.zero) (hb : Eq b.w Int.zero) (hc : Eq c.w Int.zero)
    (haa : Eq (a.dot a) (Int.ofNat (denominator.mul denominator)))
    (hbb : Eq (b.dot b) (Int.ofNat (denominator.mul denominator)))
    (hcc : Eq (c.dot c) (Int.ofNat (denominator.mul denominator)))
    (hab : Eq ((Int.ofNat Nat.one.succ.succ).mul (a.dot b))
      (Int.ofNat (denominator.mul denominator)).neg)
    (hbc : Eq ((Int.ofNat Nat.one.succ.succ).mul (b.dot c))
      (Int.ofNat (denominator.mul denominator)).neg)
    (hca : Eq ((Int.ofNat Nat.one.succ.succ).mul (c.dot a))
      (Int.ofNat (denominator.mul denominator)).neg) :
    False :=
  let scale := (a.dot b).natAbs
  let diagonal := Int.ofNat (three.mul scale)
  let off := (Int.ofNat scale).neg
  have hscale : Eq (denominator.mul denominator) (three.mul scale) :=
    ((Int.natAbs_neg (Int.ofNat (denominator.mul denominator))).symm.trans
      ((congrArg Int.natAbs hab).symm.trans (Int.natAbs_mul (Int.ofNat three) (a.dot b))))
  have hscale_ne : Not (Eq scale Nat.zero) := fun h =>
    (Nat.mul_eq_zero.mp (hscale.trans ((congrArg (Nat.mul three) h).trans (Nat.mul_zero three)))).elim hden hden
  have hoff : Eq ((Int.ofNat three).mul off) (Int.ofNat (denominator.mul denominator)).neg :=
    (Int.mul_neg (Int.ofNat three) (Int.ofNat scale)).trans
      (congrArg (fun n => (Int.ofNat n).neg) hscale.symm)
  have cancel {x : Int}
      (h : Eq ((Int.ofNat three).mul x) (Int.ofNat (denominator.mul denominator)).neg) :
      Eq x off :=
    Int.eq_of_mul_eq_mul_left (fun h0 => Nat.succ_ne_zero Nat.one.succ (Int.ofNat_inj.mp h0))
      (h.trans hoff.symm)
  have hdiag : Eq (Int.ofNat (denominator.mul denominator)) diagonal :=
    congrArg Int.ofNat hscale
  have hvalues : Eq (gramSize a b c)
      (gramNumerator diagonal diagonal diagonal off off off) :=
    (congrArg (fun x => gramNumerator x (b.dot b) (c.dot c) (a.dot b) (b.dot c) (c.dot a))
      (haa.trans hdiag)).trans
    ((congrArg (fun x => gramNumerator diagonal x (c.dot c) (a.dot b) (b.dot c) (c.dot a))
      (hbb.trans hdiag)).trans
    ((congrArg (fun x => gramNumerator diagonal diagonal x (a.dot b) (b.dot c) (c.dot a))
      (hcc.trans hdiag)).trans
    ((congrArg (fun x => gramNumerator diagonal diagonal diagonal x (b.dot c) (c.dot a))
      (cancel hab)).trans
    ((congrArg (fun x => gramNumerator diagonal diagonal diagonal off x (c.dot a))
      (cancel hbc)).trans
    (congrArg (gramNumerator diagonal diagonal diagonal off off) (cancel hca))))))
  (pure_gram_numerator_is_square a b c ha hb hc).elim fun determinant hsquare =>
    have hgram := Int.ofNat_inj.mp (Int.natAbs_mul_self.trans
      (hsquare.symm.trans (hvalues.trans (gram_of_equal_negative_pairing scale))))
    let divisor := (four.mul scale).mul denominator
    have hdivisor : Not (Eq divisor Nat.zero) :=
      fun h => (Nat.mul_eq_zero.mp h).elim
        (fun h0 => (Nat.mul_eq_zero.mp h0).elim (Nat.succ_ne_zero _) hscale_ne) hden
    Arithmetic.no_square_eq_three_mul_square (three.mul determinant.natAbs)
      divisor hdivisor (square_relation determinant.natAbs scale denominator hgram hscale)

end Omega.Geometry.BargmannGram

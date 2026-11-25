/- GID: D5/S3/PrimeForms/FixedFormDiscriminant
   generality: G
   mirror-B: D5/B/S3/PrimeForms/FixedFormDiscriminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discriminant of the fixed-point quadratic form of a 2×2 integer matrix equals tr²−4·det; for determinant −1 it is tr²+4, and for the pinned odd core of trace 12j it is 4(36j²+1), exactly four times the negative-Pell discriminant. -/

module
prelude
public import OmegaMath.Matrix.Mat2.Discriminant

/-! The fixed-form discriminant for determinant minus one and the trace-twelve specialization. -/

noncomputable section
@[expose] public section

namespace D5.S3.PrimeForms.FixedFormDiscriminant

open Omega

/-- The discriminant of the fixed-point quadratic form of a 2×2 integer matrix
`[[a, b], [c, d]]`: the fixed-point equation `x = (ax+b)/(cx+d)` has quadratic
`c·x² + (d−a)·x − b`, whose discriminant is `(d−a)² + 4bc`. -/
def fixedFormDiscriminant (a b c d : Int) : Int := Omega.Matrix.fixedFormDiscriminant a b c d

/-- The fixed-form discriminant equals `tr² − 4·det`. -/
theorem fixedFormDiscriminant_eq (a b c d : Int) :
    Eq (fixedFormDiscriminant a b c d)
      ((a.add d).square.sub ((Int.ofNat Nat.one.succ.succ.succ).mul ((a.mul d).sub (b.mul c)))) :=
  Omega.Matrix.fixedFormDiscriminant_eq a b c d

/-- Core discriminant lemma (E.53): for a matrix of determinant `−1`, the fixed-form
discriminant is `tr² + 4`. -/
theorem det_neg_one_fixed_form_disc (a b c d : Int) (h : Eq ((a.mul d).sub (b.mul c)) Int.one.neg) :
    Eq (fixedFormDiscriminant a b c d) ((a.add d).square.add (Int.ofNat Nat.one.succ.succ.succ)) :=
  Omega.Matrix.det_neg_one_fixedFormDiscriminant a b c d h

/-- Pinned odd core (trace `12j`, determinant `−1`): the fixed-form discriminant is
`4·(36j² + 1)`, exactly four times the negative-Pell discriminant `d_j = 36j² + 1`. -/
theorem pinned_core_disc (a b c d j : Int) (h : Eq ((a.mul d).sub (b.mul c)) Int.one.neg)
    (htr : Eq (a.add d) (((Int.ofNat Nat.one.succ.succ.succ).mul
      (Int.ofNat Nat.one.succ.succ)).mul j)) :
    Eq (fixedFormDiscriminant a b c d)
      (Int.mul (Int.ofNat Nat.one.succ.succ.succ)
        (Int.add (Int.mul (Int.mul (Int.mul (Int.ofNat Nat.one.succ.succ.succ)
          (Int.ofNat Nat.one.succ.succ)) (Int.ofNat Nat.one.succ.succ)) j.square) Int.one)) :=
  let four := Int.ofNat Nat.one.succ.succ.succ
  let three := Int.ofNat Nat.one.succ.succ
  let twelve := four.mul three
  let thirtySix := twelve.mul three
  have coefficient : Eq twelve.square (four.mul thirtySix) :=
    (Int.mul_assoc four three twelve).trans (congrArg four.mul (Int.mul_comm three twelve))
  have traceEq := congrArg (fun x : Int => x.square.add four) htr
  (det_neg_one_fixed_form_disc a b c d h).trans
    (traceEq.trans ((congrArg (fun x : Int => x.add four) (Int.square_mul twelve j)).trans
      ((congrArg (fun x : Int => (x.mul j.square).add four) coefficient).trans
        ((congrArg (fun x : Int => x.add four) (Int.mul_assoc four thirtySix j.square)).trans
          ((congrArg (four.mul (thirtySix.mul j.square)).add (Int.mul_one four).symm).trans
            (Int.mul_add four (thirtySix.mul j.square) Int.one).symm)))))

end D5.S3.PrimeForms.FixedFormDiscriminant

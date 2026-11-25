/- GID: D5/S3/Fourier/AllDegreeHaar
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Orthonormality of even characters for the factorial moment functional. -/

module
prelude
public import D5.S3.Fourier.AllDegreeHaar.Integration
import D5.S3.Fourier.AllDegreeHaar.MomentTable

/-!
Omega original.

All even-character products and their orthonormality for the exact factorial
moment functional on the squared scalar coordinate of the three-sphere.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.AllDegreeHaar

open PiFreeHaar
open IntRatio (Equivalent)

/-- Coefficients in ascending degree order for the character of degree `2r`. -/
def evenCharPoly (r : Nat) : CoefficientList := (Characters.character r).ratios

/-- Sum of the even characters from `|m - n|` through `m + n`, inclusive. -/
def evenCharProductSum (m n : Nat) : CoefficientList :=
  (Characters.sum (Characters.gap m n) (Characters.span m n)).ratios

/-- Character multiplication, with omitted coefficients interpreted as zero. -/
theorem evenChar_product_sum (m n : Nat) :
    Poly.RatioSame ((evenCharPoly m).mul (evenCharPoly n)) (evenCharProductSum m n) :=
  Eq.subst (motive := fun p => Poly.RatioSame p (evenCharProductSum m n))
    (Poly.ratios_mul (Characters.character m) (Characters.character n))
    (Poly.ratio_same (Characters.product m n))

/-- The indicator of degree zero. -/
def zeroDelta (r : Nat) : IntRatio :=
  Nat.rec (IntRatio.ofInt Int.one) (fun _ _ => IntRatio.ofInt Int.zero) r

/-- The Kronecker delta, computed by removing matching successors. -/
def degreeDelta (m n : Nat) : IntRatio := zeroDelta (Characters.gap m n)

private def ShiftedMoment (r : Nat) : Prop :=
  ∀ j, Equivalent (Integration.integral j (Characters.character r)) (MomentTable.expected j r)

private theorem shifted_moment (r : Nat) : ShiftedMoment r :=
  (Nat.rec (motive := fun r => And (ShiftedMoment r) (ShiftedMoment r.succ))
    (And.intro (fun j => (Integration.integral_one j).trans (MomentTable.base j))
      (fun j => (Integration.integral_first j).trans (MomentTable.first j)))
    (fun r h => And.intro h.right (fun j =>
      let next := Characters.character r.succ
      let prev := Characters.character r
      (Integration.integral_sub j (Characters.recurrence next) prev).trans
        ((IntRatio.sub_congr ((Integration.integral_recurrence j next).trans
          (IntRatio.sub_congr (IntRatio.mul_congr (IntRatio.equivalent_refl _) (h.right j.succ))
            (IntRatio.mul_congr (IntRatio.equivalent_refl _) (h.right j)))) (h.left j)).trans
          (MomentTable.step j r)))) r).left

/-- Haar expectation of every even character. -/
theorem haar_evenChar_expectation (r : Nat) :
    Equivalent (haarKappaPoly (evenCharPoly r)) (zeroDelta r) :=
  (shifted_moment r Nat.zero).trans (MomentTable.axis r)

private theorem sum_expectation (start span : Nat) :
    Equivalent (Integration.integral Nat.zero (Characters.sum start span)) (zeroDelta start) :=
  (Nat.rec (motive := fun span => ∀ start,
    Equivalent (Integration.integral Nat.zero (Characters.sum start span)) (zeroDelta start))
    haar_evenChar_expectation
    (fun k ih start =>
      (Integration.integral_add Nat.zero (Characters.character start) (Characters.sum start.succ k)).trans
        ((IntRatio.add_congr (haar_evenChar_expectation start) (ih start.succ)).trans
          (IntRatio.add_zero (zeroDelta start)))) span) start

/-- All-degree even-character orthonormality for the rational Haar functional. -/
theorem all_degree_peter_weyl_orthonormal (m n : Nat) :
    Equivalent (haarInner (evenCharPoly m) (evenCharPoly n)) (degreeDelta m n) :=
  Eq.subst (motive := fun p => Equivalent (haarKappaPoly p) (degreeDelta m n))
    (Poly.ratios_mul (Characters.character m) (Characters.character n))
    ((Integration.integral_congr (Characters.product m n) Nat.zero).trans
      (sum_expectation (Characters.gap m n) (Characters.span m n)))

end Omega.Harmonic.AllDegreeHaar

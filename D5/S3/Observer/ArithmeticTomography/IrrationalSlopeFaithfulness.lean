/- GID: D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An irrational linear slope faithfully encodes every integer pair. -/

import Mathlib.NumberTheory.Real.Irrational

/- Library-search audit trail (2026-08-28):
   * Repository searches for an irrational-slope injectivity theorem and for the
     body `alpha * integer + integer` found no exact D5 owner.
   * Pinned Mathlib provides `Irrational.mul_intCast` and
     `Irrational.ne_int`; both are applied directly below.
   * No pinned-Mathlib theorem packages this pair-observer statement. -/

namespace D5.S3.Observer.ArithmeticTomography.IrrationalSlopeFaithfulness

/-- Every irrational real slope makes the linear observer on integer pairs injective. -/
theorem irrational_slope_observer_injective (alpha : Real)
    (irrational : Irrational alpha) :
    Function.Injective
      (fun x : Int × Int => alpha * (x.1 : Real) + (x.2 : Real)) := by
  intro x y observed
  have first_coordinate : x.1 = y.1 := by
    by_contra different
    have scaled_irrational :
        Irrational (alpha * ((x.1 - y.1 : Int) : Real)) :=
      irrational.mul_intCast (sub_ne_zero.mpr different)
    have scaled_integer :
        alpha * ((x.1 - y.1 : Int) : Real) =
          ((y.2 - x.2 : Int) : Real) := by
      push_cast
      linarith
    exact scaled_irrational.ne_int (y.2 - x.2) scaled_integer
  apply Prod.ext
  · exact first_coordinate
  · have second_cast : (x.2 : Real) = (y.2 : Real) := by
      change alpha * (x.1 : Real) + (x.2 : Real) =
        alpha * (y.1 : Real) + (y.2 : Real) at observed
      rw [first_coordinate] at observed
      linarith
    exact_mod_cast second_cast

#print axioms irrational_slope_observer_injective

end D5.S3.Observer.ArithmeticTomography.IrrationalSlopeFaithfulness

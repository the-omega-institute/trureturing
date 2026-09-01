/- GID: D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaObservation/ChristoffelAtomFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive atoms give polynomial energies and Christoffel costs a positive floor. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/- Library-search audit trail (2026-09-02):
   * Repository searches for Christoffel evaluation costs, polynomial infima,
     singleton-mass energy floors, and the defining body shape found no exact
     D5 owner. The nearby zeta-observation family contains no such primitive.
   * Pinned Mathlib contains no Christoffel definition or whole-theorem hit.
     `MeasureTheory.lintegral_singleton` and `lintegral_mono_set` are the exact
     singleton evaluation and measure-monotonicity steps used below.
   * The cost is constructed directly from polynomial degree, evaluation, the
     squared complex norm, the measure integral, and an infimum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ZetaObservation.ChristoffelAtomFloor

open MeasureTheory Set
open scoped ENNReal

/-- The least extended nonnegative energy of a complex polynomial of degree at
most `degree` that takes the value one at `point`. -/
def christoffelEvaluationCost
    (measure : Measure Complex) (point : Complex) (degree : Nat) : ENNReal :=
  ⨅ polynomial :
      {polynomial : Polynomial Complex //
        polynomial.natDegree ≤ degree ∧ polynomial.eval point = 1},
    ∫⁻ z, ENNReal.ofReal (Complex.normSq (polynomial.1.eval z)) ∂measure

/-- A positive atom supplies the exact point-mass contribution to every
normalized polynomial energy. Consequently every degree-bounded Christoffel
evaluation cost is bounded below by that atom and is strictly positive. -/
theorem christoffel_atom_floor
    (measure : Measure Complex) (point : Complex) (mass : ENNReal)
    (atomMass : measure {point} = mass) (massPositive : 0 < mass) :
    (∀ polynomial : Polynomial Complex, polynomial.eval point = 1 →
      (mass * ENNReal.ofReal (Complex.normSq (polynomial.eval point)) ≤
        ∫⁻ z, ENNReal.ofReal (Complex.normSq (polynomial.eval z)) ∂measure) ∧
      mass * ENNReal.ofReal (Complex.normSq (polynomial.eval point)) = mass) ∧
    ∀ degree : Nat,
      mass ≤ christoffelEvaluationCost measure point degree ∧
      0 < christoffelEvaluationCost measure point degree := by
  have energyLowerBound (polynomial : Polynomial Complex) :
      mass * ENNReal.ofReal (Complex.normSq (polynomial.eval point)) ≤
        ∫⁻ z, ENNReal.ofReal (Complex.normSq (polynomial.eval z)) ∂measure := by
    calc
      mass * ENNReal.ofReal (Complex.normSq (polynomial.eval point)) =
          ENNReal.ofReal (Complex.normSq (polynomial.eval point)) *
            measure {point} := by rw [atomMass, mul_comm]
      _ = ∫⁻ z in {point},
          ENNReal.ofReal (Complex.normSq (polynomial.eval z)) ∂measure := by
        symm
        exact lintegral_singleton _ _
      _ ≤ ∫⁻ z in Set.univ,
          ENNReal.ofReal (Complex.normSq (polynomial.eval z)) ∂measure :=
        lintegral_mono_set (Set.subset_univ _)
      _ = ∫⁻ z,
          ENNReal.ofReal (Complex.normSq (polynomial.eval z)) ∂measure := by
        simp
  constructor
  · intro polynomial normalizedAtPoint
    exact ⟨energyLowerBound polynomial, by simp [normalizedAtPoint]⟩
  · intro degree
    have floorBound :
        mass ≤ christoffelEvaluationCost measure point degree := by
      unfold christoffelEvaluationCost
      refine le_iInf fun polynomial => ?_
      simpa [polynomial.2.2] using energyLowerBound polynomial.1
    exact ⟨floorBound, lt_of_lt_of_le massPositive floorBound⟩

#print axioms christoffel_atom_floor

end D5.S3.Analytic.ZetaObservation.ChristoffelAtomFloor

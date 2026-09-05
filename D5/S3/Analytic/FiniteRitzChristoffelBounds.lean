/- GID: D5/S3/Analytic/FiniteRitzChristoffelBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/FiniteRitzChristoffelBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Attained reduced-energy minima give sharp two-sided bounds for Ritz errors. -/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

/-!
# Finite Ritz--Christoffel bounds

This module isolates the variational algebra behind the Christoffel error bar.
The trial type can be a finite-dimensional polynomial space after normalization
at the top spectral atom.  `reducedEnergy` is the weighted Christoffel energy,
while `tailMass` is the remaining squared norm.  A positive spectral gap gives
the comparison `gap * tailMass <= reducedEnergy`.

The source also claimed a specific superfactorial asymptotic for zeta-zero
data.  That rate needs zero-density and orthogonal-polynomial asymptotics not
present in the atom, so it is deliberately not asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.FiniteRitzChristoffelBounds

open Set

/-- The error of a normalized trial after restoring the top atom's mass. -/
def variationalRitzError {Trial : Type*}
    (atomMass : Real) (tailMass reducedEnergy : Trial -> Real)
    (trial : Trial) : Real :=
  reducedEnergy trial / (atomMass + tailMass trial)

/-- The relative correction dictated by the top atom and the spectral gap. -/
def christoffelRelativeCorrection
    (christoffelCost atomMass spectralGap : Real) : Real :=
  christoffelCost / (atomMass * spectralGap)

/-- If the Christoffel energy and Ritz error attain their variational minima,
then gap control gives the two-sided Christoffel error bar.  The last two
equalities exhibit configurations attaining the upper and lower bounds. -/
theorem finite_ritz_christoffel_bounds
    {Trial : Type*}
    (atomMass spectralGap christoffelCost ritzError : Real)
    (tailMass reducedEnergy : Trial -> Real)
    (atomMassPositive : 0 < atomMass)
    (spectralGapPositive : 0 < spectralGap)
    (tailMassNonnegative : forall trial, 0 <= tailMass trial)
    (reducedEnergyNonnegative : forall trial, 0 <= reducedEnergy trial)
    (spectralGapControl : forall trial,
      spectralGap * tailMass trial <= reducedEnergy trial)
    (christoffelMinimum : IsLeast (Set.range reducedEnergy) christoffelCost)
    (ritzMinimum : IsLeast
      (Set.range (variationalRitzError atomMass tailMass reducedEnergy))
      ritzError) :
    0 <= christoffelRelativeCorrection
        christoffelCost atomMass spectralGap /\
      christoffelCost /
          (atomMass *
            (1 + christoffelRelativeCorrection
              christoffelCost atomMass spectralGap)) <= ritzError /\
      ritzError <= christoffelCost / atomMass /\
      variationalRitzError atomMass
          (fun _ : Unit => 0) (fun _ => christoffelCost) () =
        christoffelCost / atomMass /\
      variationalRitzError atomMass
          (fun _ : Unit => christoffelCost / spectralGap)
          (fun _ => christoffelCost) () =
        christoffelCost /
          (atomMass *
            (1 + christoffelRelativeCorrection
              christoffelCost atomMass spectralGap)) := by
  obtain ⟨christoffelTrial, christoffelTrialEnergy⟩ := christoffelMinimum.1
  have christoffelCostNonnegative : 0 <= christoffelCost := by
    rw [← christoffelTrialEnergy]
    exact reducedEnergyNonnegative christoffelTrial
  have atomGapPositive : 0 < atomMass * spectralGap :=
    mul_pos atomMassPositive spectralGapPositive
  have correctionNonnegative :
      0 <= christoffelRelativeCorrection
        christoffelCost atomMass spectralGap := by
    exact div_nonneg christoffelCostNonnegative atomGapPositive.le
  have correctedDenominator :
      atomMass *
          (1 + christoffelRelativeCorrection
            christoffelCost atomMass spectralGap) =
        atomMass + christoffelCost / spectralGap := by
    unfold christoffelRelativeCorrection
    field_simp [atomMassPositive.ne', spectralGapPositive.ne']
  have lowerBoundForEveryTrial (trial : Trial) :
      christoffelCost / (atomMass + christoffelCost / spectralGap) <=
        variationalRitzError atomMass tailMass reducedEnergy trial := by
    have trialEnergyNonnegative : 0 <= reducedEnergy trial :=
      reducedEnergyNonnegative trial
    have minimumEnergy : christoffelCost <= reducedEnergy trial :=
      christoffelMinimum.2 (Set.mem_range_self trial)
    have tailControlled :
        tailMass trial <= reducedEnergy trial / spectralGap := by
      rw [le_div_iff₀ spectralGapPositive]
      simpa [mul_comm] using spectralGapControl trial
    have minimumDenominatorPositive :
        0 < atomMass + christoffelCost / spectralGap := by
      positivity
    have trialComparisonDenominatorPositive :
        0 < atomMass + reducedEnergy trial / spectralGap := by
      positivity
    have trialDenominatorPositive : 0 < atomMass + tailMass trial := by
      linarith [tailMassNonnegative trial]
    have energyMonotonicity :
        christoffelCost / (atomMass + christoffelCost / spectralGap) <=
          reducedEnergy trial /
            (atomMass + reducedEnergy trial / spectralGap) := by
      rw [div_le_div_iff₀ minimumDenominatorPositive
        trialComparisonDenominatorPositive]
      calc
        christoffelCost *
              (atomMass + reducedEnergy trial / spectralGap) =
            christoffelCost * atomMass +
              (christoffelCost * reducedEnergy trial) / spectralGap := by
                ring
        _ <= reducedEnergy trial * atomMass +
              (christoffelCost * reducedEnergy trial) / spectralGap := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right minimumEnergy atomMassPositive.le)
                  (le_refl _)
        _ = reducedEnergy trial *
              (atomMass + christoffelCost / spectralGap) := by
                ring
    calc
      christoffelCost / (atomMass + christoffelCost / spectralGap) <=
          reducedEnergy trial /
            (atomMass + reducedEnergy trial / spectralGap) :=
        energyMonotonicity
      _ <= reducedEnergy trial / (atomMass + tailMass trial) :=
        div_le_div_of_nonneg_left trialEnergyNonnegative
          trialDenominatorPositive (by linarith [tailControlled])
      _ = variationalRitzError atomMass tailMass reducedEnergy trial := rfl
  have lowerBound :
      christoffelCost /
          (atomMass *
            (1 + christoffelRelativeCorrection
              christoffelCost atomMass spectralGap)) <= ritzError := by
    obtain ⟨ritzTrial, ritzTrialError⟩ := ritzMinimum.1
    rw [correctedDenominator, ← ritzTrialError]
    exact lowerBoundForEveryTrial ritzTrial
  have upperBound : ritzError <= christoffelCost / atomMass := by
    calc
      ritzError <=
          variationalRitzError atomMass tailMass reducedEnergy
            christoffelTrial :=
        ritzMinimum.2 (Set.mem_range_self christoffelTrial)
      _ <= reducedEnergy christoffelTrial / atomMass := by
        exact div_le_div_of_nonneg_left
          (reducedEnergyNonnegative christoffelTrial) atomMassPositive
          (le_add_of_nonneg_right (tailMassNonnegative christoffelTrial))
      _ = christoffelCost / atomMass := by
        rw [christoffelTrialEnergy]
  have upperSharp :
      variationalRitzError atomMass
          (fun _ : Unit => 0) (fun _ => christoffelCost) () =
        christoffelCost / atomMass := by
    simp [variationalRitzError]
  have lowerSharp :
      variationalRitzError atomMass
          (fun _ : Unit => christoffelCost / spectralGap)
          (fun _ => christoffelCost) () =
        christoffelCost /
          (atomMass *
            (1 + christoffelRelativeCorrection
              christoffelCost atomMass spectralGap)) := by
    rw [correctedDenominator]
    rfl
  exact ⟨correctionNonnegative, lowerBound, upperBound, upperSharp, lowerSharp⟩

#print axioms finite_ritz_christoffel_bounds

end D5.S3.Analytic.FiniteRitzChristoffelBounds

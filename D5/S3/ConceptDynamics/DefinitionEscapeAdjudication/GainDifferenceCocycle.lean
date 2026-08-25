/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/GainDifferenceCocycle
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/GainDifferenceCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gain differences have zero self-value and satisfy a three-point cocycle. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoWeakPreorder
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs

/- Library-search audit trail (2026-08-26):
   * `rg -n -i 'gainDifference|gain_difference|GainVector|gain.*self.*zero|
     self.*difference.*zero|three[-_ ]point.*cocycle|cocycle.*gain|
     difference.*cocycle|sub_add_sub_cancel' D5 --glob '*.lean'` found the
     frozen `GainVector` declaration and unrelated scalar cocycle uses, but no
     gain-difference definition or theorem stating either target law.
   * `rg -n -i 'GainVector|gainDifference|gain_difference|heterogeneous.*cocycle|
     five.*coordinate.*cocycle|difference.*self.*cocycle'
     .lake/packages/mathlib/Mathlib --glob '*.lean'` returned no hit.
   * Pinned Mathlib supplies the scalar identities `sub_self` and
     `sub_add_sub_cancel`; the proof below applies them independently in each
     coordinate rather than reproving them. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

private theorem gainVector_ext
    {Information Residual Transfer Cost Risk : Type u}
    {x y : GainVector Information Residual Transfer Cost Risk}
    (hInformation : x.information = y.information)
    (hResidual : x.residualCapture = y.residualCapture)
    (hTransfer : x.transfer = y.transfer)
    (hCost : x.lifecycleCost = y.lifecycleCost)
    (hRisk : x.risk = y.risk) : x = y := by
  cases x
  cases y
  cases hInformation
  cases hResidual
  cases hTransfer
  cases hCost
  cases hRisk
  rfl

/-- The zero gain vector is zero independently in all five heterogeneous
coordinates. -/
instance gainVectorZero
    {Information Residual Transfer Cost Risk : Type u}
    [Zero Information] [Zero Residual] [Zero Transfer] [Zero Cost] [Zero Risk] :
    Zero (GainVector Information Residual Transfer Cost Risk) where
  zero :=
    { information := 0
      residualCapture := 0
      transfer := 0
      lifecycleCost := 0
      risk := 0 }

/-- Gain vectors add independently in all five heterogeneous coordinates. -/
instance gainVectorAdd
    {Information Residual Transfer Cost Risk : Type u}
    [Add Information] [Add Residual] [Add Transfer] [Add Cost] [Add Risk] :
    Add (GainVector Information Residual Transfer Cost Risk) where
  add x y :=
    { information := x.information + y.information
      residualCapture := x.residualCapture + y.residualCapture
      transfer := x.transfer + y.transfer
      lifecycleCost := x.lifecycleCost + y.lifecycleCost
      risk := x.risk + y.risk }

/-- The coordinatewise difference between the absolute gain vectors of two
actions. -/
def gainDifference
    {Action Information Residual Transfer Cost Risk : Type u}
    [Sub Information] [Sub Residual] [Sub Transfer] [Sub Cost] [Sub Risk]
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (a b : Action) : GainVector Information Residual Transfer Cost Risk :=
  { information := (value a).information - (value b).information
    residualCapture :=
      (value a).residualCapture - (value b).residualCapture
    transfer := (value a).transfer - (value b).transfer
    lifecycleCost := (value a).lifecycleCost - (value b).lifecycleCost
    risk := (value a).risk - (value b).risk }

/-- When every gain coordinate is an additive group, self-difference is the
zero gain vector and every direct difference is the sum of the two successive
differences through an intermediate action. -/
theorem gain_difference_self_zero_and_cocycle
    {Action Information Residual Transfer Cost Risk : Type u}
    [AddGroup Information] [AddGroup Residual] [AddGroup Transfer]
    [AddGroup Cost] [AddGroup Risk]
    (value : Action -> GainVector Information Residual Transfer Cost Risk) :
    (forall a, gainDifference value a a = 0) /\
      (forall a b c, gainDifference value a c =
        gainDifference value a b + gainDifference value b c) := by
  constructor
  · intro a
    apply gainVector_ext
    · change (value a).information - (value a).information =
        (0 : Information)
      exact sub_self _
    · change (value a).residualCapture - (value a).residualCapture =
        (0 : Residual)
      exact sub_self _
    · change (value a).transfer - (value a).transfer = (0 : Transfer)
      exact sub_self _
    · change (value a).lifecycleCost - (value a).lifecycleCost = (0 : Cost)
      exact sub_self _
    · change (value a).risk - (value a).risk = (0 : Risk)
      exact sub_self _
  · intro a b c
    apply gainVector_ext
    · change (value a).information - (value c).information =
        ((value a).information - (value b).information) +
          ((value b).information - (value c).information)
      exact (sub_add_sub_cancel _ _ _).symm
    · change (value a).residualCapture - (value c).residualCapture =
        ((value a).residualCapture - (value b).residualCapture) +
          ((value b).residualCapture - (value c).residualCapture)
      exact (sub_add_sub_cancel _ _ _).symm
    · change (value a).transfer - (value c).transfer =
        ((value a).transfer - (value b).transfer) +
          ((value b).transfer - (value c).transfer)
      exact (sub_add_sub_cancel _ _ _).symm
    · change (value a).lifecycleCost - (value c).lifecycleCost =
        ((value a).lifecycleCost - (value b).lifecycleCost) +
          ((value b).lifecycleCost - (value c).lifecycleCost)
      exact (sub_add_sub_cancel _ _ _).symm
    · change (value a).risk - (value c).risk =
        ((value a).risk - (value b).risk) +
          ((value b).risk - (value c).risk)
      exact (sub_add_sub_cancel _ _ _).symm

/-- A finite inhabited action domain with integer coordinates where the
universal laws hold and one gain difference is genuinely nonzero. -/
example :
    exists value : Bool -> GainVector Int Int Int Int Int,
      ((forall a, gainDifference value a a = 0) /\
        (forall a b c, gainDifference value a c =
          gainDifference value a b + gainDifference value b c)) /\
      gainDifference value true false =
        { information := 1
          residualCapture := 1
          transfer := 1
          lifecycleCost := 1
          risk := 1 } := by
  let value : Bool -> GainVector Int Int Int Int Int := fun action =>
    if action then
      { information := 1
        residualCapture := 1
        transfer := 1
        lifecycleCost := 1
        risk := 1 }
    else
      { information := 0
        residualCapture := 0
        transfer := 0
        lifecycleCost := 0
        risk := 0 }
  refine ⟨value, gain_difference_self_zero_and_cocycle value, ?_⟩
  simp [value, gainDifference]

#print axioms gain_difference_self_zero_and_cocycle

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

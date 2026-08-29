/- GID: D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite-difference completion velocity is a Newton predictor and exactly recovers root displacement for affine layer changes. -/

import D5.S3.Analytic.ZetaCompletionFlow.NewtonCompletionField

/-!
The displayed finite-difference quotient predicts a zero displacement.  Equality
with an actual zero branch needs a realization or remainder theorem.  The affine
model below is the exact case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaCompletionFlow.DiscreteCompletionVelocity

universe u

variable {K : Type u} [Field K]

/-- One-layer finite difference evaluated at a state. -/
def completionLayerDifference (Fnext F : K → K) (s : K) : K :=
  Fnext s - F s

/-- Discrete zero-displacement predictor. -/
def predictedDiscreteVelocity
    (F Fnext dF : K → K) (s : K) : K :=
  -completionLayerDifference Fnext F s / dF s

/-- At a current root, the layer difference is simply the next layer's
residual at that point. -/
theorem completion_layer_difference_at_root
    {F Fnext : K → K} {root : K} (hRoot : F root = 0) :
    completionLayerDifference Fnext F root = Fnext root := by
  simp [completionLayerDifference, hRoot]

/-- Root-specialized form of the discrete predictor. -/
theorem predicted_discrete_velocity_at_root
    {F Fnext dF : K → K} {root : K} (hRoot : F root = 0) :
    predictedDiscreteVelocity F Fnext dF root =
      -Fnext root / dF root := by
  simp [predictedDiscreteVelocity, completionLayerDifference, hRoot]

/-- At a regular current root, a zero predictor is equivalent to the next layer
also vanishing at the same point. -/
theorem predicted_discrete_velocity_eq_zero_iff
    {F Fnext dF : K → K} {root : K}
    (hRoot : F root = 0) (hRegular : dF root ≠ 0) :
    predictedDiscreteVelocity F Fnext dF root = 0 ↔
      Fnext root = 0 := by
  rw [predicted_discrete_velocity_at_root hRoot]
  simp [hRegular]

/-- Exact affine layer model: shifting the root by `delta` produces predicted
velocity `delta`. -/
theorem affine_layer_predicted_velocity
    {a root delta : K} (hA : a ≠ 0) :
    predictedDiscreteVelocity
        (fun z => a * (z - root))
        (fun z => a * (z - (root + delta)))
        (fun _ => a)
        root = delta := by
  unfold predictedDiscreteVelocity completionLayerDifference
  field_simp [hA]
  ring

/-- The affine prediction agrees with the actual next-layer root. -/
theorem affine_layer_prediction_realized
    {a root delta : K} (hA : a ≠ 0) :
    let Fnext : K → K := fun z => a * (z - (root + delta))
    let velocity := predictedDiscreteVelocity
      (fun z => a * (z - root)) Fnext (fun _ => a) root
    Fnext (root + velocity) = 0 := by
  dsimp
  rw [affine_layer_predicted_velocity hA]
  ring

/-- Common nonzero rescaling of both layers and the derivative field leaves the
prediction unchanged. -/
theorem predicted_discrete_velocity_scale_invariant
    (c : K) (F Fnext dF : K → K) (s : K)
    (hC : c ≠ 0) (hRegular : dF s ≠ 0) :
    predictedDiscreteVelocity
        (fun z => c * F z)
        (fun z => c * Fnext z)
        (fun z => c * dF z) s =
      predictedDiscreteVelocity F Fnext dF s := by
  unfold predictedDiscreteVelocity completionLayerDifference
  field_simp [hC, hRegular]
  ring

#print axioms completion_layer_difference_at_root
#print axioms predicted_discrete_velocity_at_root
#print axioms predicted_discrete_velocity_eq_zero_iff
#print axioms affine_layer_predicted_velocity
#print axioms affine_layer_prediction_realized
#print axioms predicted_discrete_velocity_scale_invariant

end D5.S3.Analytic.ZetaCompletionFlow.DiscreteCompletionVelocity

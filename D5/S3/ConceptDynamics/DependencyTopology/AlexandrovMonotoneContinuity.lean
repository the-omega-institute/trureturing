/- GID: D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Maps between upper Alexandrov spaces are continuous exactly when they are monotone. -/

import D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.AlexandrovMonotoneContinuity

open D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology

/-- Monotonicity between two explicitly supplied relations. -/
def RelationMonotone
    {X Y : Type*} (relationX : X → X → Prop) (relationY : Y → Y → Prop)
    (map : X → Y) : Prop :=
  ∀ ⦃x y⦄, relationX x y → relationY (map x) (map y)

/-- For upper-set Alexandrov topologies, continuity is exactly order
monotonicity. -/
theorem continuous_upperSetTopology_iff_monotone
    {X Y : Type*}
    (relationX : X → X → Prop) (relationY : Y → Y → Prop)
    [Std.Refl relationX] [IsTrans X relationX]
    [Std.Refl relationY] [IsTrans Y relationY]
    (map : X → Y) :
    @Continuous X Y (upperSetTopology relationX)
        (upperSetTopology relationY) map ↔
      RelationMonotone relationX relationY map := by
  constructor
  · intro mapContinuous x y hxy
    rw [continuous_def] at mapContinuous
    have targetOpen :
        @IsOpen Y (upperSetTopology relationY) (upset relationY (map x)) :=
      upset_isOpen relationY (map x)
    have preimageOpen :
        @IsOpen X (upperSetTopology relationX)
          (map ⁻¹' upset relationY (map x)) :=
      mapContinuous (upset relationY (map x)) targetOpen
    have xInPreimage : x ∈ map ⁻¹' upset relationY (map x) := by
      exact refl (map x)
    exact preimageOpen xInPreimage hxy
  · intro monotone
    rw [continuous_def]
    intro targetSet targetOpen
    intro x y xInPreimage hxy
    exact targetOpen xInPreimage (monotone hxy)

/-- A monotone map of dependency preorders transports all upper-open future
regions continuously. -/
theorem monotone_continuous_dependencyTopology
    {X Y : Type*}
    (edgeX : X → X → Prop) (edgeY : Y → Y → Prop)
    (map : X → Y)
    (monotone : RelationMonotone
      (D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder.Reachable edgeX)
      (D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder.Reachable edgeY)
      map) :
    @Continuous X Y (dependencyTopology edgeX) (dependencyTopology edgeY) map :=
  (continuous_upperSetTopology_iff_monotone
    (D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder.Reachable edgeX)
    (D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder.Reachable edgeY)
    map).2 monotone

#print axioms continuous_upperSetTopology_iff_monotone

end D5.S3.ConceptDynamics.DependencyTopology.AlexandrovMonotoneContinuity

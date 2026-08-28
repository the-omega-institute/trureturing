/- GID: D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict edge depth yields a closed Alexandrov sublevel filtration. -/

import D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.DepthClosedFiltration
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
open D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology

def DepthCompatible {V : Type*} (edge : V -> V -> Prop) (depth : V -> Nat) : Prop :=
  forall ⦃u v⦄, edge u v -> depth u < depth v

theorem depth_strict_of_strictReachable
    {V : Type*} {edge : V -> V -> Prop} {depth : V -> Nat}
    (compatible : DepthCompatible edge depth) {u v : V}
    (path : StrictReachable edge u v) : depth u < depth v := by
  induction path with
  | single edgeStep => exact compatible edgeStep
  | tail previous edgeStep inductionHypothesis =>
      exact lt_trans inductionHypothesis (compatible edgeStep)

theorem depth_mono_of_reachable
    {V : Type*} {edge : V -> V -> Prop} {depth : V -> Nat}
    (compatible : DepthCompatible edge depth) {u v : V}
    (path : Reachable edge u v) : depth u ≤ depth v := by
  induction path with
  | refl => exact le_rfl
  | tail previous edgeStep inductionHypothesis =>
      exact le_trans inductionHypothesis (Nat.le_of_lt (compatible edgeStep))

def depthSublevel {V : Type*} (depth : V -> Nat) (level : Nat) : Set V :=
  {v | depth v ≤ level}

def depthSuperlevel {V : Type*} (depth : V -> Nat) (level : Nat) : Set V :=
  {v | level < depth v}

theorem depthSuperlevel_isOpen
    {V : Type*} {edge : V -> V -> Prop} {depth : V -> Nat}
    (compatible : DepthCompatible edge depth) (level : Nat) :
    @IsOpen V (upperSetTopology (Reachable edge)) (depthSuperlevel depth level) := by
  intro u v hu huv
  change level < depth u at hu
  change level < depth v
  exact lt_of_lt_of_le hu (depth_mono_of_reachable compatible huv)

theorem depthSublevel_isClosed
    {V : Type*} {edge : V -> V -> Prop} {depth : V -> Nat}
    (compatible : DepthCompatible edge depth) (level : Nat) :
    @IsClosed V (upperSetTopology (Reachable edge)) (depthSublevel depth level) := by
  letI : TopologicalSpace V := upperSetTopology (Reachable edge)
  have superlevelOpen := depthSuperlevel_isOpen compatible level
  have complementClosed := superlevelOpen.isClosed_compl
  simpa only [depthSuperlevel, depthSublevel, Set.compl_setOf, not_lt] using
    complementClosed

theorem depthSublevel_mono
    {V : Type*} (depth : V -> Nat) {lower upper : Nat} (levels : lower ≤ upper) :
    depthSublevel depth lower ⊆ depthSublevel depth upper := by
  intro v hv
  exact le_trans hv levels

theorem edge_depth_ne
    {V : Type*} {edge : V -> V -> Prop} {depth : V -> Nat}
    (compatible : DepthCompatible edge depth) {u v : V} (huv : edge u v) :
    depth u ≠ depth v := ne_of_lt (compatible huv)

#print axioms depthSublevel_isClosed
#print axioms depth_strict_of_strictReachable
end D5.S3.ConceptDynamics.DependencyTopology.DepthClosedFiltration

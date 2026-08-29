/- GID: D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-state locality and unchanged dependencies preserve an artifact property. -/

import Mathlib.Data.Set.Insert

/- Library-search audit trail (2026-08-29):
   * Exact and shape searches for two-state locality, changed artifacts,
     cross-state read over-approximations, and incremental preservation in
     `D5/S0/Rewriting`, `D5/S1/FixedPoints`, and `D5/S3/ConceptDynamics` found
     no theorem with this state-indexed read-set interface.
   * `CommitInterfaceSealPreservation` confines committed artifacts to a sealed
     closure, while `TargetLaunderingCriterion` detects protected-coordinate
     changes; neither relates two states through their actual read sets.
   * Pinned Mathlib v4.31.0 supplies `Set.disjoint_left` and the set union and
     subset membership laws used below, but no domain theorem packaging the
     locality argument. The proof therefore composes those library facts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.TwoStateLocalityIncrementalPreservation

/-- Artifacts whose bytes differ between two states. -/
def Changed {State Artifact Value : Type*}
    (bytes : State -> Artifact -> Value) (s t : State) : Set Artifact :=
  {artifact | Not (bytes s artifact = bytes t artifact)}

/-- A property is local when byte equality on an artifact and both states'
actual read sets makes the property's truth value equal in those states. -/
def Local {State Artifact Value : Type*}
    (bytes : State -> Artifact -> Value)
    (reads : State -> Artifact -> Set Artifact)
    (property : State -> Artifact -> Prop) : Prop :=
  forall s t x,
    (forall artifact, artifact ∈ ({x} ∪ reads s x ∪ reads t x) ->
      bytes s artifact = bytes t artifact) ->
    Iff (property s x) (property t x)

/-- If a cross-state dependency set contains both actual read sets, then an
unchanged artifact with no changed dependency preserves every local property. -/
theorem two_state_locality_yields_incremental_preservation
    {State Artifact Value : Type*}
    (bytes : State -> Artifact -> Value)
    (reads : State -> Artifact -> Set Artifact)
    (property : State -> Artifact -> Prop)
    (locality : Local bytes reads property)
    (s t : State)
    (dep : Artifact -> Set Artifact)
    (overapproximates : forall x, reads s x ∪ reads t x ⊆ dep x)
    (x : Artifact)
    (unchanged : x ∉ Changed bytes s t)
    (dependenciesUnchanged : Disjoint (dep x) (Changed bytes s t)) :
    Iff (property s x) (property t x) := by
  have selfEqual : bytes s x = bytes t x := by
    by_contra differs
    exact unchanged differs
  have equalOfDependency {artifact : Artifact} (inDep : artifact ∈ dep x) :
      bytes s artifact = bytes t artifact := by
    by_contra differs
    exact Set.disjoint_left.1 dependenciesUnchanged inDep differs
  apply locality s t x
  intro artifact relevant
  rcases relevant with (isSelf | readInS) | readInT
  · have : artifact = x := by simpa using isSelf
    subst artifact
    exact selfEqual
  · exact equalOfDependency (overapproximates x (Set.mem_union_left _ readInS))
  · exact equalOfDependency (overapproximates x (Set.mem_union_right _ readInT))

#print axioms two_state_locality_yields_incremental_preservation

end D5.S3.ConceptDynamics.Governance.TwoStateLocalityIncrementalPreservation

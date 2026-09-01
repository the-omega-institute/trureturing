# Commuting Space-Time Action

## Abstract

Commuting spatial and temporal permutation actions combine into a product-monoid action.

**Definition 1.1 (Commuting space-time representation).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.SpaceTimeAction`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.SpaceTimeAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Spatial and temporal monoids act by permutations on one state space and commute pointwise.

**Definition 1.2 (Joint space-time action).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A spatial action is applied after the temporal action of the paired parameter.

**Definition 1.3 (Joint orbit).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointOrbit`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint orbit contains every state reachable by one product space-time parameter.

**Theorem 1.4 (Identity fixes every state).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct_one`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two identity parameters act as the identity permutation.

**Theorem 1.5 (Product parameters compose).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct_mul`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commutation of the component actions makes joint action respect product-monoid multiplication.

**Theorem 1.6 (Pure space and time actions commute).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.pure_space_time_commute`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.pure_space_time_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint embeddings of a spatial parameter and a temporal parameter commute on every state.

**Theorem 1.7 (Componentwise fixed states are jointly fixed).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.joint_fixed_of_component_fixed`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.joint_fixed_of_component_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state fixed by both selected components is fixed by their joint action.

**Theorem 1.8 (Every state lies in its orbit).**

Lean statement: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.self_mem_jointOrbit`

*Formalization.* `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.self_mem_jointOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity space-time parameter witnesses reflexivity of the orbit relation.

## References

- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.SpaceTimeAction`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointOrbit`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct_one`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.jointAct_mul`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.pure_space_time_commute`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.joint_fixed_of_component_fixed`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.self_mem_jointOrbit`

# Time-Translation Stabilizer

## Abstract

Time-translation symmetries form a stabilizer subgroup, and symmetry breaking is strict loss of stabilizing parameters.

**Definition 1.1 (Time stabilizer subgroup).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeStabilizer`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeStabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The temporal group elements fixing one state form a subgroup.

**Definition 1.2 (Lost time symmetry).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.LostTimeSymmetry`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.LostTimeSymmetry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A temporal parameter fixes the earlier state and moves the later state.

**Definition 1.3 (Time-symmetry breaking).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.TimeSymmetryBreaksFrom`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.TimeSymmetryBreaksFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The later stabilizer is contained in the earlier one and at least one earlier symmetry is lost.

**Theorem 1.4 (Stabilizer membership is fixedness).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.mem_timeStabilizer_iff`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.mem_timeStabilizer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A time parameter belongs to the stabilizer exactly when its permutation fixes the state.

**Theorem 1.5 (Every break has a lost symmetry).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeSymmetryBreaksFrom_has_witness`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeSymmetryBreaksFrom_has_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The breaking predicate contains an explicit time-translation witness.

**Theorem 1.6 (Lost symmetry as fixed and moved equations).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.lostTimeSymmetry_iff`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.lostTimeSymmetry_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lost stabilizer is exactly a fixed-before and moved-after pair of equations.

**Theorem 1.7 (No self-breaking).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.no_timeSymmetryBreaksFrom_self`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.no_timeSymmetryBreaksFrom_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state cannot strictly lose a stabilizer relative to itself.

**Theorem 1.8 (Universal fixedness prevents breaking).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.no_timeSymmetryBreaksFrom_of_all_fixed`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.no_timeSymmetryBreaksFrom_of_all_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If all temporal parameters fix both states, no lost symmetry exists.

**Theorem 1.9 (Constructing a time-symmetry break).**

Lean statement: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeSymmetryBreaksFrom_intro`

*Formalization.* `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeSymmetryBreaksFrom_intro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilizer inclusion together with one fixed-before and moved-after witness proves breaking.

## References

- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeStabilizer`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.LostTimeSymmetry`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.TimeSymmetryBreaksFrom`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.mem_timeStabilizer_iff`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeSymmetryBreaksFrom_has_witness`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.lostTimeSymmetry_iff`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.no_timeSymmetryBreaksFrom_self`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.no_timeSymmetryBreaksFrom_of_all_fixed`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.timeSymmetryBreaksFrom_intro`
- Dependency: [D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction](CommutingSpaceTimeAction.md)

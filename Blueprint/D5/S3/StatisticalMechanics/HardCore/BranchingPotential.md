# BranchingPotential

## Abstract

Geometric hard-core branching, exact certificates and their precise scope.

**Definition 1.1 (Weighted children).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.childWeight`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.childWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Absent children contribute zero. Each direction is counted separately, even when multiple directions reach one state.

**Definition 1.2 (Controlled descendants).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.pathCount`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.pathCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The policy sees both the current state and the complete newest-first direction history. Depth zero counts the current node once.

**Theorem 1.3 (A positive super-potential bounds all depths).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.upper_of_superpotential`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.upper_of_superpotential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer one-step inequalities for the selected actions imply an explicit all-depth upper bound by induction. The concrete geometric controller is supplied in RadiusThreeCertificates.

**Theorem 1.4 (A bounded sub-potential bounds all depths from below).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.lower_of_subpotential`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.lower_of_subpotential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weights may vanish on dead states. A cap on every weight and row inequalities at every history imply the lower bound. Requiring all actions at every state makes the result uniform over history-dependent policies.

The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.childWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.lower_of_subpotential`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.pathCount`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/BranchingPotential.upper_of_superpotential`

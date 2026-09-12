# MUB Mode Symmetry Budget

## Abstract

Three-mode collision, mixing, and centered-square coordinates obey exact budgets.

**Definition 1.1 (Three-mode collision coordinate).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCollision`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCollision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real triple p, the collision coordinate is the sum of the squares of its three entries.

**Definition 1.2 (Three-mode mixing coordinate).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real triple p, mixing is one minus its collision coordinate.

**Definition 1.3 (Displacement from uniform weights).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCenteredSquare`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCenteredSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real triple p, the centered square is the sum of the squared differences between its entries and one-third.

**Theorem 1.4 (Mixing from pair products).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_eq_pairProducts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_eq_pairProducts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a real triple sums to one, its mixing equals twice the sum of its three distinct pair products.

**Theorem 1.5 (Nonnegative probability mixing).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative real triple whose entries sum to one has nonnegative mixing.

**Theorem 1.6 (Collision lower bound).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.one_third_le_threeModeCollision`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.one_third_le_threeModeCollision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any real triple whose entries sum to one has collision at least one-third.

**Theorem 1.7 (Mixing upper bound).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_le_two_thirds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_le_two_thirds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any real triple whose entries sum to one has mixing at most two-thirds.

**Theorem 1.8 (Centered collision excess).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCenteredSquare_eq_collision_sub_one_third`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCenteredSquare_eq_collision_sub_one_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real triple whose entries sum to one, its centered square equals its collision minus one-third.

**Theorem 1.9 (Equality characterizes uniform weights).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_eq_two_thirds_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_eq_two_thirds_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real triple whose entries sum to one, mixing equals two-thirds if and only if each entry is one-third.

**Definition 1.10 (Collision across six rows).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCollisionTotal`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCollisionTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For six real triples, total collision is the sum of their three-mode collision coordinates.

**Definition 1.11 (Mixing across six rows).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For six real triples, total mixing is the sum of their three-mode mixing coordinates.

**Definition 1.12 (Centered squares across six rows).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCenteredSquareTotal`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCenteredSquareTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For six real triples, the total centered square is the sum of their squared displacements from uniform three-mode weights.

**Definition 1.13 (Algebraic affinity coordinate).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeAffinityTotal`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeAffinityTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For six real triples, affinity is total collision minus two, divided by two. This is an algebraic coordinate; identifying it with chordal subspace affinity requires the projector-plane bridge.

**Theorem 1.14 (Total mixing and collision identity).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_eq_six_sub_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_eq_six_sub_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any six real triples, total mixing equals six minus total collision.

**Theorem 1.15 (Six-row centered collision excess).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCenteredSquareTotal_eq_collision_sub_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCenteredSquareTotal_eq_collision_sub_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each of six real triples sums to one, the total centered square equals total collision minus two.

**Theorem 1.16 (Affinity as half the centered square).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeAffinityTotal_eq_half_centeredSquare`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeAffinityTotal_eq_half_centeredSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each of six real triples sums to one, affinity equals one-half of the total centered square.

**Theorem 1.17 (Mixing and affinity identity).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_eq_four_sub_two_mul_affinity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_eq_four_sub_two_mul_affinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any six real triples, total mixing equals four minus twice the affinity coordinate.

**Theorem 1.18 (Total probability mixing interval).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_mem_Icc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_mem_Icc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For six nonnegative real triples each summing to one, total mixing lies in the closed interval from zero to four.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeAffinityTotal`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeAffinityTotal_eq_half_centeredSquare`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCenteredSquareTotal`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCenteredSquareTotal_eq_collision_sub_two`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeCollisionTotal`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_eq_four_sub_two_mul_affinity`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_eq_six_sub_collision`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.modeMixingTotal_mem_Icc`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.one_third_le_threeModeCollision`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCenteredSquare`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCenteredSquare_eq_collision_sub_one_third`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeCollision`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_eq_pairProducts`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_eq_two_thirds_iff`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_le_two_thirds`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget.threeModeMixing_nonneg`
- Dependency: [D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre](ZaunerCompletionFibre.md)

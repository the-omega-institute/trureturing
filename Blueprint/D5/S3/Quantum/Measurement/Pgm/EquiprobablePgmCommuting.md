# EquiprobablePgmCommuting

## Abstract

Universal actual-object PGM control

**Theorem 1.1 (Every actual optimum on the five-dimensional support).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.every_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.every_optimum` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every 0<epsilon<7/18, the first four states have populations (1-epsilon)e0+epsilon e_i, i=1..4, and the fifth (1-2epsilon)e0+(epsilon/2)sum_(i=1..4)e_i. These actual diagonal trace-one PSD matrices commute. An actual POVM attains (1+3epsilon)/5. Every optimal complex POVM, including competitors with off-diagonal entries, has this score and precisely the first four nonzero effects. Complementary products with the diagonal dual slack force the fifth effect to vanish and each rare coordinate to be assigned to its unique maximizing label. This theorem is on the complete five-dimensional joint support.

**Theorem 1.2 (The complete commuting interval and exact CFC scores).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.scores_and_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.scores_and_gap` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

On every 0<epsilon<7/18, actual P_A=(1+3epsilon)/5=P_opt and P_all=1/5+32epsilon/75+4epsilon^2/[25(5-6epsilon)]. For centered eta_A=P_A-1/5 and eta=P_all-1/5 the exact gap is 3eta_A-4eta=epsilon(7-18epsilon)/[15(5-6epsilon)]>0. The endpoints are excluded. The diagonal Moore-Penrose score theorem evaluates actual CFC objects, including the zeros in individual states.

**Theorem 1.3 (Nonuniqueness of the optimal measurement).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.nonunique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.nonunique` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every epsilon>0 the displayed score optimization has two distinct actual optimal finitePOVMs, obtained by allocating the common coordinate wholly to two different first-four labels. On the physical interval they are optimal discrimination POVMs for the stated density ensemble. The common-coordinate tie explains nonuniqueness. No every-optimum activity claim is made about effects living entirely in an unused ambient kernel.

**Definition 1.4 (Complete commuting populations).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.population`

*Formalization.* `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.population` (`✓ std3`).

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

On coordinates 0..4, first-four labels i=0..3 use (1-epsilon)e0+epsilon e_(i+1); label4 uses (1-2epsilon)e0+(epsilon/2)sum_(j=1..4)e_j.

**Definition 1.5 (Actual commuting density matrices).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.states`

*Formalization.* `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.states` (`✓ std3`).

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

Each actual state is the complex diagonal matrix of population. Individual first-four states have rank two; the physical domain is 0<epsilon<7/18.

**Definition 1.6 (Actual tied-coordinate POVMs).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.effects`

*Formalization.* `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.effects` (`✓ std3`).

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

Each first-four label receives its rare coordinate; nonnegative weights summing to one allocate the common coordinate among labels. For the stated optimum construction the fifth common weight vanishes.

**Theorem 1.7 (Actual centered ratio at the commuting endpoint).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.centered_ratio_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.centered_ratio_limit` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

As epsilon decreases to zero, the ratio of the actual full advantage to the actual pair-set advantage tends to 32/45, which is strictly below 3/4. The exact interval scores determine the continuous ratio 32/45+4epsilon/[15(5-6epsilon)].

**Theorem 1.8 (Actual selected states have rank two).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.selected_ranks`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.selected_ranks` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every 0<epsilon<7/18, all first-four actual density matrices have matrix rank exactly two. They are not PD in dimension five.

**Theorem 1.9 (The actual joint support is dimension five).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.joint_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.joint_support` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every physical epsilon, spectralSupport of the actual full average equals the identity on Fin5. The individual states may be singular; the average has full five-dimensional support.

**Definition 1.10 (Fixed support inclusion into dimension eight).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.supportInclusion`

*Formalization.* `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.supportInclusion` (`✓ std3`).

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

The actual coordinate isometry includes the five support coordinates into Fin8. It introduces three unused ambient kernel coordinates.

**Definition 1.11 (Actual dimension-eight embedded states).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.embeddedStates`

*Formalization.* `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.embeddedStates` (`✓ std3`).

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

Embedded states are V rho_i V-adjoint for the fixed coordinate isometry V. They are actual PSD trace-one matrices with the original five-dimensional joint support.

**Theorem 1.12 (Every ambient optimum after support compression).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.dimension_eight_optima`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.dimension_eight_optima` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

Throughout 0<epsilon<7/18, an actual optimal dimension-eight finitePOVM exists. Every complex ambient optimum scores (1+3epsilon)/5 and its compression to the five-dimensional joint support has exactly active labels {0,1,2,3}. Every support POVM can be lifted by assigning the unused kernel to label0. No claim is made that every ambient completion has the same uncompressed nonzero labels.

**Theorem 1.13 (Embedded support, ranks and actual CFC scores).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.dimension_eight_support_and_scores`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.dimension_eight_support_and_scores` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every physical epsilon the actual full-average spectral support is diag(1,1,1,1,1,0,0,0); the first-four embedded states have rank two. Actual restricted score is (1+3epsilon)/5 and full score is 1/5+32epsilon/75+4epsilon^2/[25(5-6epsilon)]. CFC uses Moore-Penrose zero action on the three-dimensional kernel.

The construction and symmetric calculations are credited to Hyunho Cha. Mechanism attribution remains anonymous; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. CC BY 4.0 applies to the new note only. The original nonzero-effect interpretation of activity is retained, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.centered_ratio_limit`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.dimension_eight_optima`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.dimension_eight_support_and_scores`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.effects`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.embeddedStates`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.every_optimum`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.joint_support`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.nonunique`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.population`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.scores_and_gap`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.selected_ranks`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.states`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting.supportInclusion`
- Dependency: [D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmSymmetric](EquiprobablePgmSymmetric.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../../Recovery/SpectralTransposeRecovery.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](../../Reduction/IsometricCompression.md)

# EquiprobablePgmCommuting

## Abstract

Universal actual-object PGM control

**Theorem 1.1 (Every actual optimum on the five-dimensional support).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.every_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.every_optimum` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every 0<epsilon<7/18, the first four states have populations (1-epsilon)e0+epsilon e_i, i=1..4, and the fifth (1-2epsilon)e0+(epsilon/2)sum_(i=1..4)e_i. These actual diagonal trace-one PSD matrices commute. An actual POVM attains (1+3epsilon)/5. Every optimal complex POVM, including competitors with off-diagonal entries, has this score and precisely the first four nonzero effects. Complementary products with the diagonal dual slack force the fifth effect to vanish and each rare coordinate to be assigned to its unique maximizing label. This theorem is on the complete five-dimensional joint support.

**Theorem 1.2 (The complete commuting interval and exact CFC scores).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.scores_and_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.scores_and_gap` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

On every 0<epsilon<7/18, actual P_A=(1+3epsilon)/5=P_opt and P_all=1/5+32epsilon/75+4epsilon^2/[25(5-6epsilon)]. For centered eta_A=P_A-1/5 and eta=P_all-1/5 the exact gap is 3eta_A-4eta=epsilon(7-18epsilon)/[15(5-6epsilon)]>0. The endpoints are excluded. The diagonal Moore-Penrose score theorem evaluates actual CFC objects, including the zeros in individual states.

**Theorem 1.3 (Nonuniqueness of the optimal measurement).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.nonunique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.nonunique` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every epsilon>0 the displayed score optimization has two distinct actual optimal finitePOVMs, obtained by allocating the common coordinate wholly to two different first-four labels. On the physical interval they are optimal discrimination POVMs for the stated density ensemble. The common-coordinate tie explains nonuniqueness. No every-optimum activity claim is made about effects living entirely in an unused ambient kernel.

The construction and symmetric calculations are credited to Hyunho Cha. Mechanism attribution remains anonymous; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. CC BY 4.0 applies to the new note only. The original nonzero-effect interpretation of activity is retained, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.every_optimum`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.nonunique`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.scores_and_gap`
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric](EquiprobablePgmSymmetric.md)

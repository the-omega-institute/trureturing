# Unbounded centered ratios for actual mixed qubit states

## Abstract

Unbounded centered ratios for actual mixed qubit states

**Theorem 1.1 (The complete fixed-dimension family).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.family` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real 0<epsilon<=1/8, states are rho_+/-=[[1-epsilon^6,+/-epsilon^3/2],[+/-epsilon^3/2,epsilon^6]] and rho_3=diag(1-epsilon^4,epsilon^4). All are strictly positive and trace one, so in dimension two they are mixed. The actual unique optimal finitePOVM is (Q+,Q-,0), active set {0,1}, and success=(1+epsilon^3)/3. With H=(1+2epsilon^2)(3-epsilon^4(1+2epsilon^2))>3, actual eta_A=epsilon^3/(6sqrt(1-epsilon^6)) and eta_all=epsilon^4[1/(3sqrt(H))+2(1-epsilon^2)^2/(3H)]. These are identities for the existing CFC pgmScore, not definitions of surrogate scores.

**Theorem 1.2 (A uniform quantitative estimate).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.uniform_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.uniform_ratio` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

On the entire interval 0<epsilon<=1/8, the actual full centered advantage is positive and eta_A/eta_all>=3/[2(2+sqrt(3))epsilon]>3/(8epsilon). The bound is uniform; no finite sample is used.

**Theorem 1.3 (Every positive real constant at fixed (2,3,2)).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.every_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.every_constant` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real C>0 there exists 0<epsilon<=1/8 with actual strictly positive trace-one qubit states, the actual unique optimum (Q+,Q-,0), exactly two nonzero effects, eta_all>0 and eta_A>C eta_all. The proof chooses epsilon=min(1/8,3/(8C))/2 and applies the uniform estimate. Dimension, number of labels and number of active labels are fixed throughout.

**Theorem 1.4 (Centered divergence and the raw-score limit).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.score_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.score_limits` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

As epsilon tends to zero through positive reals, both actual centered advantages tend to zero, the raw score ratio P_A/P_all tends to one, and the centered ratio tends to positive infinity. This says nothing against a quantitative positive spectral-floor estimate or the general all-pure comparison, both of which remain open in the supplied sources.

Attribution remains separate: anonymous mechanism; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. Hyunho Cha is credited for the symmetric score, qubit slice and commuting constructions. CC BY 4.0 applies only to the new note. Active means nonzero effects, including rank-one effects; the source wording about positive definite effects is ambiguous. No priority or publication claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.every_constant`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.family`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.score_limits`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.uniform_ratio`
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric](EquiprobablePgmSymmetric.md)

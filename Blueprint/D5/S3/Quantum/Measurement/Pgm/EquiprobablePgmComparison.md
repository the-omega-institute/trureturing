# Actual symmetric CFC scores and active-set failure

## Abstract

Actual symmetric CFC scores and active-set failure

**Theorem 1.1 (Two-coordinate spectral inverse square root).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.inverse_sqrt_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.inverse_sqrt_two` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

The inverse square root of diag(u,v), for arbitrary nonnegative u,v including zero, is diag(sqrt(u)^(-1),sqrt(v)^(-1)). This shared CFC evaluation helper is consumed by the actual score and effect calculations; it assumes no invertibility.

**Theorem 1.2 (Both actual symmetric scores).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.symmetric_scores`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.symmetric_scores` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real a,b,c with 0<a,c<1, the actual original-prior restricted and full CFC scores of rho(a,b,c) satisfy P_{0,1}-1/3=2b^2/(3sqrt(a(1-a))) and P_all-1/3=4b^2/(3sqrt(D))+2(c-a)^2/(3D), D=(2a+c)(3-2a-c). The evaluation does not need a pair determinant hypothesis. When b^2<=a(1-a), the pair is physical, including the singular equality case; strict determinant positivity gives the full strict-PD setting. The proof evaluates the existing diagonal CFC, including its support inverse, and multiplies the actual matrices inside the existing score definition. Hyunho Cha is credited for these symmetric calculations.

**Theorem 1.3 (The strict score criterion).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.pair_failure_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.pair_failure_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every 0<a,c<1, the actual pair/full score inequality 2(P_all-1/3)<P_{0,1}-1/3 holds if and only if D>16q and b^2>2(c-a)^2sqrt(q)/(sqrt(D)(sqrt(D)-4sqrt(q))), with q=a(1-a), D=(2a+c)(3-2a-c). Either equality is nonfailure. The actual CFC scores are bound through symmetric_scores; no evaluation bridge is assumed. This scalar-equivalent test concerns the pair label set; the full optimizer theorem additionally needs that set to be active.

**Theorem 1.4 (The actual active-set failure iff).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.active_failure_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.active_failure_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every 0<a,c<1, b>0 and b^2<a(1-a), all three actual rho_i are PD trace-one states. With A the nonzero effects of the actual optimalPovm, the original strict failure (|A|-1)(P_A-1/3)>2(P_all-1/3) holds if and only if |c-a|<=b AND D>16q AND b^2>2(c-a)^2sqrt(q)/(sqrt(D)(sqrt(D)-4sqrt(q))). The pair-region conjunct is essential. With three active labels the comparison is equality. This binds the strict criterion to the exact optimizer and its active labels, over the complete strict physical domain.

**Theorem 1.5 (sqrt_inverse_square).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.sqrt_inverse_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.sqrt_inverse_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every u>=0, (sqrt(u)^(-1))^2=u^(-1), including u=0. This algebra helper is consumed by the actual symmetric CFC scores.

**Theorem 1.6 (sqrt_inverse_product).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.sqrt_inverse_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.sqrt_inverse_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For u>=0 and any real v, sqrt(u)^(-1)sqrt(v)^(-1)=sqrt(uv)^(-1). This CFC-evaluation algebra helper is consumed by the actual symmetric score calculation.

**Theorem 1.7 (Shared rationalized inverse-square-root residual).**

Lean statement: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.inverse_sqrt_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.inverse_sqrt_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u with 1-u>0, 1/sqrt(1-u)-1=u/[sqrt(1-u)(1+sqrt(1-u))]. This algebra helper is consumed by the actual qubit and loading asymptotic estimates.

Source custody: the mechanism manuscript is anonymous (3 November 2026); no license grant was supplied. The old literal byline remains Wenlin Zhang and Haobo / trureturing, and its actual rational proof is reused as EquiprobablePgmActiveSetRefutation.result. The new note is by Haobo Ma then Wenlin Zhang (4 November 2026), with CC BY 4.0 restricted to that new note. Hyunho Cha is credited for the symmetric scores and qubit/commuting constructions. The metadata URLs locate immutable repository citation records, not public manuscript originals. Activity means a nonzero effect, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open. No priority or publication claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.active_failure_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.inverse_sqrt_residual`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.inverse_sqrt_two`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.pair_failure_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.sqrt_inverse_product`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.sqrt_inverse_square`
- Truth anchor: `D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison.symmetric_scores`
- Dependency: [D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmSymmetric](EquiprobablePgmSymmetric.md)

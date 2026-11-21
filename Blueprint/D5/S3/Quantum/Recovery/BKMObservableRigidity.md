# Fixed-observable BKM rigidity

## Abstract

Fixed-observable BKM rigidity for the actual partial trace.

**Theorem 1.1 (Physical modular compression).**

Lean statement: `D5/S3/Quantum/Recovery/BKMObservableRigidity.weightedLift_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMObservableRigidity.weightedLift_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be positive definite on a finite retained space tensored with a nonempty finite environment, and let S be its right partial trace. Weight each observable on the right by the square root of its reference and vectorize column first. The identity lift transported through these coordinates is an isometry. It compresses the joint modular matrix exactly to the marginal modular matrix. The two identities follow by testing against arbitrary weighted observables and using the trace adjunction of the partial trace.

**Theorem 1.2 (Equality on a fixed Hermitian observable).**

Lean statement: `D5/S3/Quantum/Recovery/BKMObservableRigidity.bkmGap_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMObservableRigidity.bkmGap_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The marginal BKM form minus the joint BKM form on the identity lift is the integral of the retained minus joint modular power forms. At each interior exponent, this difference is a positive multiple of the integral of the joint minus retained resolvent form against a positive weight. The isometry cancels the common resolvent term and exact compression gives a nonnegative residual. A zero BKM gap forces the half-power defect to vanish by continuity in the exponent. Every positive-shift resolvent defect then vanishes by continuity in the shift. Finite spectral separation gives intertwining for every real function on the fixed weighted vector. Applying that intertwining to each power gives the reverse implication.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMObservableRigidity.bkmGap_rigidity`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMObservableRigidity.weightedLift_compression`
- Dependency: [D5/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget](../Divergence/EntropyDefectResolventIntegralBudget.md)
- Dependency: [D5/S3/Quantum/Divergence/ResolventFunctionalRigidity](../Divergence/ResolventFunctionalRigidity.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiKernelContraction](../Divergence/UmegakiKernelContraction.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinement](BKMFlagRefinement.md)

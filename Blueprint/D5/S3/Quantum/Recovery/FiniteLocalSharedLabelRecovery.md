# FiniteLocalSharedLabelRecovery

## Abstract

Actual finite local CP protocols with independent mixed ancillas have complete positive product effects on the original input. For r>0, heralded all-matrix recovery with one original correction for each actual label forces both local supports of every nonzero accepted true-history effect to have rank one; under the same r>0 hypothesis, at zero accepted probability every accepted effect vanishes.

**Theorem 1.1 (actual product-effect completeness and shared-label support rigidity).**

Lean statement: `D5/S3/Quantum/Recovery/FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>0, the actual accepted scalar lies in [0,1], and each accepted history has a nonnegative scalar action on every complex system matrix under its original correction. The effect laws include root identities, positivity, one-party child sums, unchanged inactive factors, complete descendant sums and the complex source-entry formula for arbitrary finite untouched spectator indices. True history addresses retain actual observed outcomes and the original terminal feedback label; hidden Kraus garbage remains inaccessible to physical control. Individually finite trees can have arbitrary dimensions, repeated parties, coarse outcomes, failed or zero branches and early leaves. The rank conclusion concerns true histories; merged label effects are sums. Every local Gram is trace-normalized in the whole closed Bloch ball, with zero trace exactly for the zero Gram. The root has trace weight four and zero Bloch coordinates. Actual actor child traces give finite one-coordinate barycentric splits; zero children retain weight zero and zero parents have only zero-effect descendants. The physical preparation and original coarse execution with any finite untouched reference, followed by the full output trace and I_F tensor U_y, agree with system execution on every matrix block. Accepted recovery on all complex system matrices is equivalent to recovery on every finite reference, and any zero-effect history executes as zero. Under the further strict-interior condition 1/2<r^2<2, every nonzero accepted true history has its normalized Bloch pair in K_s(r) and its physical corrected action on every finite reference is trace(E) times h(r) times the original matrix. The accepted probability equals h(r) times the sum of the actual accepted effect traces, including zero effects. The Bellman value and the uniform frontier gap are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity`
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry](FiniteLocalLatitudeGeometry.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausLeftInverseNecessity](KrausLeftInverseNecessity.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](PurifiedLocalPath.md)

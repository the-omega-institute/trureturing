# Original Gaussian Compact Uniform Cutoffs

## Abstract

Original Gaussian Compact Uniform Cutoffs

Principal square sections converge in operator norm uniformly on every smaller closed disk. The original weighted source truncations converge uniformly in the literal complex l2 carrier. Resolvent identities control both signed Neumann inverses and the inverse of one minus the square of the finite section. Squaring occurs after cutoff; no compression of the infinite square is substituted.

These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.

**Theorem 1.1 (sectionOp_tendstoUniformlyOn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionOp_tendstoUniformlyOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionOp_tendstoUniformlyOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual principal square section operators converge uniformly in operator norm on every smaller closed complex disk.

**Definition 1.2 (traceWeightedTerm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original weighted source coordinate embedded by lp.single into the existing carrier.

**Definition 1.3 (weightedCutoff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first N terms of the original weighted source on the same infinite carrier.

**Theorem 1.4 (traceWeightedTerm_tsum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm-summable embedded coordinate series equals the existing weightedSource for every nonnegative radius below one.

**Theorem 1.5 (weightedCutoff_tendstoUniformly).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_tendstoUniformly`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_tendstoUniformly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted cutoffs converge uniformly in l2 on each nonnegative compact radial interval below one.

**Theorem 1.6 (weightedCutoff_norm_le).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every weighted cutoff has norm bounded by the enclosing-radius majorant mass.

**Theorem 1.7 (traceNeumann_norm_le).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceNeumann_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceNeumann_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A norm-contractive operator has Neumann-series norm at most the reciprocal of one minus its norm bound.

**Definition 1.8 (sectionSignedResolvent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine signed finite-section Neumann inverse embedded on the original infinite carrier.

**Theorem 1.9 (sectionSignedResolvent_error).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_error`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both unit-modulus signs obey an operator-norm error estimate proportional to the actual section error.

**Theorem 1.10 (sectionSignedResolvent_tendstoUniformlyOn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_tendstoUniformlyOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_tendstoUniformlyOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine signed section inverses converge uniformly on smaller disks, including signs plus one and minus one.

**Theorem 1.11 (sectionSquareResolvent_error).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_error`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of one minus the square of the actual finite section has an explicit section-error bound.

**Theorem 1.12 (sectionSquareResolvent_tendstoUniformlyOn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_tendstoUniformlyOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_tendstoUniformlyOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite-square inverses converge uniformly on every smaller disk.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionOp_tendstoUniformlyOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_error`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_tendstoUniformlyOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_error`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_tendstoUniformlyOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceNeumann_norm_le`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm_tsum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_norm_le`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_tendstoUniformly`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace](OriginalGaussianFiniteTrace.md)

# Native finite Gaussian moments

## Abstract

Exact factorial Gaussian moments and insertion over any finite complex mode space.

The mode type is arbitrary and finite, including the empty type. The complex matrix A is arbitrary for the moment definition and symmetric for insertion. Occupations are finitely supported natural multiplicities. No positivity, nondegeneracy, operator-norm bound or analytic convergence premise is used. The covariance is bilinear, with no complex conjugation.

Factorial-weighted Gaussian coefficients and the insertion equation are classical symmetric/Bargmann Fock and Wick moment calculus. The native coefficient and the product of occupation factorials are the existing FactorialFockQuadraticEstimate.gaussianCoefficient and FactorialFockMetric.weight. No literature novelty or exact external theorem attribution is claimed. The actual lattice correction identification and the elementary zero-shared-diagonal contraction both consume this common mathematical supplier.

**Theorem 1.1 (Degree after removing an occupied occurrence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.sub_single_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.sub_single_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If d(j) is nonzero, degree(d-e_j)+1 equals degree(d). Native insertion and the actual correction and elementary contraction inductions use this helper.

**Theorem 1.2 (Factorial weight after removing an occupied occurrence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.weight_sub_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.weight_sub_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If d(j) is nonzero, weight(d) equals d(j) times weight(d-e_j). The native Gaussian recurrence and the full neutral three-leg coefficient proof use this exact factorial ratio.

**Theorem 1.3 (An occupied mode in a nonzero occupation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.occupation_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.occupation_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero occupation has an index with nonzero multiplicity. The actual correction and elementary contraction support and uniqueness inductions consume this helper.

**Definition 1.4 (Native factorial Gaussian moment).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.nativeMoment`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.nativeMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite complex matrix A and occupation d, nativeMoment(A,d) is weight(d) times gaussianCoefficient(A,d). The coefficient is the native coefficient of Q_A^(degree(d)/2)/(degree(d)/2)!, where Q_A is one half of the sum of A_ij X_i X_j.

**Theorem 1.5 (Exact native Gaussian insertion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.nativeMoment_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.nativeMoment_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every symmetric A, occupation r and mode i, nativeMoment(A,r+e_i) equals the sum over j of r_j A_ij nativeMoment(A,r-e_j). At odd predecessor degree, gaussianPiece_coefficient_step and the exact factorial ratios give the recurrence. At even predecessor degree, both sides vanish by odd Gaussian degree. Zero multiplicities contribute zero. The empty mode case remains in the quantified statement.

OriginalCorrectionGaussian.sourceMoment_eq_nativeMoment uses this recurrence to identify the actual Corr readout. ElementaryGaussianContraction uses it to prove finite shared support, the exact factorial reindexing, and the native contraction with cross block R S. This supplier alone proves no determinant sewing invariant, countable-mode limit, full corrected-field identity, physical unitarity, full VOA/CFT axioms, string dynamics or AdS/CFT correspondence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.nativeMoment`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.nativeMoment_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.occupation_nonzero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.sub_single_degree`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment.weight_sub_single`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate](FactorialFockQuadraticEstimate.md)

# Full Hermitian exclusion and orthogonal support

## Abstract

In the complete complex positive semidefinite cone, exclusion by any proper real-linear effect equals the density face annihilating the confirmed unit vector.

Let J be any finite index type with decidable equality. The carrier is the real inner product space of all complex Hermitian matrices indexed by J. Its cone consists of all positive semidefinite matrices, and its unit is the trace. The normalized base contains every positive semidefinite trace-one matrix. Effects range over every real-linear functional f satisfying 0 <= f(Y) <= trace(Y) for every positive semidefinite Y. No selected measurements or restricted effect domain is used.

**Definition 1.1 (The entire positive semidefinite cone).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.cone`

*Formalization.* `D5/S3/Quantum/Foundation/HermitianExclusionKernel.cone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cone is PointedCone.positive on the original Hermitian carrier, with its Loewner order.

**Definition 1.2 (The original trace unit).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.unit`

*Formalization.* `D5/S3/Quantum/Foundation/HermitianExclusionKernel.unit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit is the real-linear pairing with the identity matrix. HermitianMat.one_inner identifies it with the trace on every Hermitian matrix.

**Theorem 1.3 (Every positive original functional has a positive representative).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.positive_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionKernel.positive_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real-linear functional nonnegative on the entire native PSD cone is pairing with a PSD Hermitian matrix on the entire carrier. The original Riesz proof tests every native outer product. This same declaration supplies the whole-effect model application of the original state-cover theorem.

**Theorem 1.4 (The entire exclusion is an orthogonal support face).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.exclusion_iff_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionKernel.exclusion_iff_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex Euclidean vector v of norm one and every Hermitian matrix X, X belongs to the original exclusion of rankOne(v) if and only if X is positive semidefinite, trace(X)=1, and Xv=0. The exclusion quantifies over every original proper real-linear effect f, with f(rankOne(v))=1 and f(X)=0. X may have any rank, and there is no prior choice of an orthogonal face or compressed coordinate domain.

Finite-dimensional real Riesz representation writes the chosen functional as pairing with a Hermitian matrix A. Testing positivity on every outer product shows A is positive semidefinite; the upper trace bound similarly shows I-A is positive semidefinite. Acceptance of the unit vector makes (I-A)v=0, hence Av=v. Zero pairing of A and X puts the support of A in the kernel of X. Since v is in the range of A, Xv=0. This argument uses the whole mixed matrix X without replacing it by a rank-one state. Conversely, pairing with rankOne(v) is an original proper functional by positivity and the trace-product bound; it accepts rankOne(v) and vanishes on X when Xv=0.

This support characterization applies in every finite complex dimension. It does not construct affine ball coordinates, classify all original extreme points, or assert a complete three-dimensional exclusion-ball model. It makes no claim about physical preparation procedures or literature priority.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.cone`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.exclusion_iff_kernel`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.positive_representative`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.unit`
- Dependency: [D5/S3/Quantum/Foundation/FacetZeroGluing](FacetZeroGluing.md)
- Dependency: [D5/S3/Quantum/Foundation/SectionROGFrame](SectionROGFrame.md)

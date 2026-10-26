# Whole-source scalar gain identities

## Abstract

Whole-source scalar gain identities

World d retains every nonzero real gain of degree at most d, every legal source, and every real drift. No individual coefficient or sampled value is required to be nonzero. The source-linear auxiliary identity places no positivity, rank or trace restriction on S.

**Theorem 1.1 (Legal sources span the auxiliary matrix space).**

Lean statement: `D5/S3/Observer/Linear/GainRayScalarIdentity.legal_source_span`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayScalarIdentity.legal_source_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real linear span of all strictly entrywise positive rank-one trace-one 2 by 2 matrices is the whole real matrix space. The four source matrices sourceMatrix(sourceR i,sourceB i), i in Fin 4, are legal native sources: their positive chart coordinates are x=(1-sourceR i)/sourceB i and r=sourceB i/sourceR i. The determinant of their column-vectorized matrix is the existing value 1/768, so every real auxiliary matrix is their linear combination.

**Theorem 1.2 (Whole coefficients and drift split exactly).**

Lean statement: `D5/S3/Observer/Linear/GainRayScalarIdentity.output_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayScalarIdentity.output_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, World d W, chronological word w and fixed Readout d w C, C readings(W,w) equals response(d,w,C)(W.source) W.coeff plus W.drift times C times the vector of ones. The responseMatrix has entry trace(acquisition(take i w) S) times i to the power k, for original clocks i=0,...,length(w) and coefficient indices k=0,...,d. response(d,w,C) is the source-linear matrix map S to C responseMatrix(d,w,S). scalarFunctional(d,w,C)(S) is its (0,0) entry.

**Theorem 1.3 (Affine collinearity forces zero drift and a scalar linear map).**

Lean statement: `D5/S3/Observer/Linear/GainRayScalarIdentity.affine_collinearity_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayScalarIdentity.affine_collinearity_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, real linear endomorphism F of Coeff d and b:Coeff d, if for every nonzero beta and every real delta the vector F(beta)+delta*b is collinear with beta, then b=0 and F=s times the identity for some real s. This statement applies to a fixed source or to any other linear coefficient response, without a whole-source universality hypothesis. The drift argument compares delta=0 and delta=1 at a coefficient basis vector distinct from the desired output coordinate.

**Theorem 1.4 (Universal collinearity forces a source-linear scalar identity).**

Lean statement: `D5/S3/Observer/Linear/GainRayScalarIdentity.universal_scalar_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayScalarIdentity.universal_scalar_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, every word w and fixed matrix C, suppose that for every original World d W the output C readings(W,w) is collinear with W.coeff, allowing scalar zero. Then C times the vector of ones is zero, and for every real 2 by 2 auxiliary matrix S, response(d,w,C)(S)=scalarFunctional(d,w,C)(S) times the identity matrix of size d+1. Varying the arbitrary drift gives a common translation lying in every nonzero coefficient line. Two distinct coefficient directions force it to vanish. The pinned scalar-endomorphism theorem gives a scalar response for each legal source, and the legal-source span extends the identity to every S.

**Theorem 1.5 (An actual success has nonzero universal scale).**

Lean statement: `D5/S3/Observer/Linear/GainRayScalarIdentity.successful_scalar_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayScalarIdentity.successful_scalar_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,w,C satisfying drift annihilation and the stated scalar identity for every auxiliary S, and every World d W at which C succeeds, scalarFunctional(d,w,C)(W.source) is nonzero. Success requires output s W.coeff for some real s not zero, with either sign. Since W.coeff is not the zero vector, a zero universal scale would contradict that success.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayScalarIdentity.affine_collinearity_scalar`
- Truth anchor: `D5/S3/Observer/Linear/GainRayScalarIdentity.legal_source_span`
- Truth anchor: `D5/S3/Observer/Linear/GainRayScalarIdentity.output_decomposition`
- Truth anchor: `D5/S3/Observer/Linear/GainRayScalarIdentity.successful_scalar_nonzero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayScalarIdentity.universal_scalar_identity`
- Dependency: [D5/S3/Observer/CubicGain/FullWorldMeanSpan](../CubicGain/FullWorldMeanSpan.md)
- Dependency: [D5/S3/Observer/Linear/GainRaySources](GainRaySources.md)

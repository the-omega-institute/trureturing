# Whole polynomial worlds and positive source coordinates

## Abstract

Whole polynomial worlds and positive source coordinates

For any declared natural maximum degree d, Coeff d is the real vector space indexed by Fin(d+1). The polynomial gain d beta is Polynomial.ofFn(d+1,beta), with ascending ordinary coefficients. World d contains a strictly entrywise positive real 2 by 2 source of matrix rank one and trace one, a nonzero coefficient vector, and an arbitrary real drift. No individual coefficient, sampled value, root multiplicity, sign, or actual degree is constrained. Statements about the adaptive threshold additionally require d>=1.

PolynomialWorld d instead stores the same source and drift together with a nonzero real polynomial whose natural degree is at most d. coefficientEquiv reconstructs every such bounded polynomial from its ordinary coefficients. worldEquiv is an equivalence with both inverse laws, preserving the source and drift. Its nonzero condition concerns the whole polynomial.

The sourceChart(x,r) is the matrix [1,r;x,xr] divided by 1+xr. For x,r>0 it is strictly positive, rank one, and trace one. Every legal original source is exactly one such matrix, with recovered coordinates x=P10/P00 and r=P01/P00. The denominator is strictly positive. No auxiliary source restriction is introduced.

**Definition 1.1 (Ordinary coefficient equivalence).**

Lean statement: `D5/S3/Observer/Linear/GainRayWorld.coefficientEquiv`

*Formalization.* `D5/S3/Observer/Linear/GainRayWorld.coefficientEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d, coefficientEquiv d is an equivalence from Coeff d to the subtype of real polynomials p with p.natDegree<=d. Its forward map is gain d and its inverse takes the first d+1 coefficients.

**Definition 1.2 (Exact whole-world equivalence).**

Lean statement: `D5/S3/Observer/Linear/GainRayWorld.worldEquiv`

*Formalization.* `D5/S3/Observer/Linear/GainRayWorld.worldEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d, worldEquiv d is an equivalence from World d to PolynomialWorld d. It preserves source and drift and sends the coefficient vector to its whole polynomial. Both nonzero predicates and both inverse identities are proved.

**Theorem 1.3 (Legality of every positive chart point).**

Lean statement: `D5/S3/Observer/Linear/GainRayWorld.source_chart_legal`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayWorld.source_chart_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x,r in the reals, 0<x and 0<r imply LegalSource(sourceChart x r). This means every entry is positive, its matrix rank is one, and its trace is one.

**Theorem 1.4 (Every original source is represented).**

Lean statement: `D5/S3/Observer/Linear/GainRayWorld.source_chart_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayWorld.source_chart_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 2 by 2 matrix P satisfying LegalSource P there exist positive real x,r with P=sourceChart x r, x=P10/P00, and r=P01/P00. The rank-one hypothesis gives determinant zero; trace one reconstructs the positive denominator.

**Theorem 1.5 (Trace normalization preserves scalar observations).**

Lean statement: `D5/S3/Observer/Linear/GainRayWorld.normalization_read`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayWorld.normalization_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 2 by 2 R,A, every real G and drift delta, and trace(R) nonzero, (trace(R) G) trace(A (trace(R) inverse times R))+delta equals G trace(A R)+delta. Positive rank-one unnormalized worlds use the positive trace as this scale.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayWorld.coefficientEquiv`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWorld.normalization_read`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWorld.source_chart_exact`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWorld.source_chart_legal`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWorld.worldEquiv`

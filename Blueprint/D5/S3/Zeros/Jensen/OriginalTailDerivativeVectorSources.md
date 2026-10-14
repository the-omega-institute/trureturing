# The original tail parameter and source identities

## Abstract

Parameter and source identities for the complete original tail derivative vector.

**Definition 1.1 (The true fixed-degree derivative).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.originalb`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.originalb` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural n and real t,x, b_n(t,x) is the finite sum from k=0 to n of c_(n,k)*k*t^(k-1)*x^(2*k), where c_(n,k)=(-1)^k*(n)_k/(n^k*(2*k)!). The exponent k-1 is natural subtraction and the k=0 summand is zero. This is the actual partial derivative in t of the existing originalB, with n fixed.

**Definition 1.2 (A raw half-line derivative component).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawD`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,t and a real function h, rawD(n,t,h)=integral over x>0 of b_n(t,x)*h(x).

**Definition 1.3 (A raw half-line second spatial moment).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawM2`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawM2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,t,h, rawM2(n,t,h)=integral over x>0 of x^2*originalB(n,t,x)*h(x).

**Definition 1.4 (A raw adjacent-degree extraction).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawG`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,t,h, rawG=(2*n*rawD-rawM2/2)/(2*n+1).

**Definition 1.5 (The normalized full-source derivative).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullD`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,t, fullD=integral over the real line of b_n(t,x)*sourceThetaDensity(x).

**Definition 1.6 (The normalized full-source second moment).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullM2`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullM2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,t, fullM2=integral over the real line of x^2*originalB(n,t,x)*sourceThetaDensity(x).

**Definition 1.7 (The normalized full-source extraction).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullG`

*Formalization.* `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,t, fullG=(2*n*fullD-fullM2/2)/(2*n+1). There is no additional normalization.

**Lemma 1.8 (The spatial derivative estimate for the parameter response).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.spatial_derivative_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.spatial_derivative_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=1, t>0 and x>=0, put alpha=t/(2*n) and let p be the original finite polynomial with p(x)=originalB(n,t,x). Then |p'(x)|<=t*x*exp(alpha*x^2/2). The integrating factor exp(-alpha*x^2/2) converts the polynomial differential equation to an integral from zero, and the original energy bound controls its integrand. The coefficientwise identity 2*t*b_n=x*p' gives |b_n(t,x)|<=x^2*exp(alpha*x^2/2)/2, which pairs the parameter response with the weighted second residual in the complete tail derivative vector. Finite moments, five Green pairings, the common 2/Z source transports and reflected-node identities connect the same vector to the actual source. No full-source product sign or node existence follows from these identities.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullD`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullG`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.fullM2`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.originalb`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawD`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawG`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.rawM2`
- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.spatial_derivative_bound`
- Dependency: [D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals](OriginalTailDerivativeVectorResiduals.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenIntegralExtension](SourceJensenIntegralExtension.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenPositiveExtension](SourceJensenPositiveExtension.md)

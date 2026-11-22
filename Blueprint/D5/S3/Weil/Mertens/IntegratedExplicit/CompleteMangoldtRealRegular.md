# The continued complete Mangoldt transform

## Abstract

Real regularity of the meromorphic continuation of the complete Mangoldt transform

**Definition 1.1 (The normalized expression at and away from one).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.continued`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.continued` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write Z(s) for riemannZeta₁(s), the entire pole-removed zeta function, and γ for the Euler–Mascheroni constant. Put N(s)=(((1+γ)s)−1)Z(s)−Z′(s). For s≠1 the numerator of continued(s) is N(s)/(s−1), and at s=1 that quotient is filled by N′(1). In both cases the denominator of continued(s) is sZ(s).

**Theorem 1.2 (Meromorphicity, real regularity and agreement).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same function continued is meromorphic on Re(s)>0, analytic at each positive real point viewed as complex, and equals CompleteMangoldtLaurent.transform(s) at every complex s with Re(s)>1.

The identities Z(1)=1 and Z′(1)=γ give N(1)=0. Local analytic factorization makes N(s)=(s−1)G(s) near 1. Differentiation gives G(1)=N′(1), so the filled quotient is analytic at 1 as well as away from 1. Dividing by the analytic denominator gives meromorphicity. The normalized zeta function is nonzero on the positive real axis, where s is also nonzero. The normalized logarithmic derivative identity gives agreement on Re(s)>1.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.continuation`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.continued`
- Dependency: [D5/S3/Weil/Mertens/CriticalThetaTailPeak](../CriticalThetaTailPeak.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent](CompleteMangoldtLaurent.md)

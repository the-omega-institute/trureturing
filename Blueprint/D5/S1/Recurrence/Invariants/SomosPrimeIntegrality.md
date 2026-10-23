# Prime exponents characterize Somos integrality

## Abstract

The normalized rational series of the Somos family is integral exactly for prime exponents.

PowerSeries.subst takes the inner series first. The geometric series B(x)=x/(1-p*x) is written by its coefficients: coefficient zero is zero and coefficient n>0 is p to the power n-1. Natural subtraction in the exponent is truncated subtraction. Normalization A(0)=1 comes from the offset-zero entries. The proof rewrites the geometric denominator identity, lifts coefficients by Frobenius for prime p, and for composite p obtains a contradiction modulo its least prime factor.

**Definition 1.1 (The source functional equation).**

$$\forall p: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(p, A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 1) \land (X \cdot A^{p} = \operatorname{PowerSeries}.\operatorname{subst}\left(X \cdot \operatorname{PowerSeries}.\operatorname{subst}\left((X: \operatorname{PowerSeries}\left(\mathbb{Q}\right))^{p}, A\right), \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (n = 0) \operatorname{then} 0 \operatorname{else} (p: \mathbb{Q})^{(n - 1)})\right)\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2004). *OEIS A091190 and A091200: the Somos prime integrality family*. URL: <https://oeis.org/A091190>.

*Commentary.*

OEIS A091190 and A091200, COMMENTS (unpaginated): "More generally, given A(x) satisfies x*A(x)^p = B(x*A(x^p)) where B(x) = x/(1-p*x), then it appears that A(x) is an integer series only when p is prime. This is a special case of sequences with g.f.s that satisfy the more general functional equation x*A(x)^m = B(x*A(x^m)) studied by Michael Somos". The formula uses the displayed coefficient expression for B and rational coefficients for A.

**Definition 1.2 (The integrality conjecture).**

$$(\operatorname{claim}) \iff (\forall p: \mathbb{N}, (2 \le p) \implies ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(p, A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(p, A\right)) \implies ((\forall n: \mathbb{N}, \exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \iff (\operatorname{Nat}.\operatorname{Prime}\left(p\right))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2004). *OEIS A091190 and A091200: the Somos prime integrality family*. URL: <https://oeis.org/A091190>.

*Commentary.*

OEIS A091190 and A091200, COMMENTS (unpaginated): "More generally, given A(x) satisfies x*A(x)^p = B(x*A(x^p)) where B(x) = x/(1-p*x), then it appears that A(x) is an integer series only when p is prime." For each exponent at least two, the proposition asserts a solution and both directions of integrality versus primality. Integer coefficients mean that every rational coefficient equals an integer cast.

**Theorem 1.3 (Integrality holds exactly at prime exponents).**

$$\forall p: \mathbb{N}, (2 \le p) \implies ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(p, A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(p, A\right)) \implies ((\forall n: \mathbb{N}, \exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \iff (\operatorname{Nat}.\operatorname{Prime}\left(p\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2004). *OEIS A091190 and A091200: the Somos prime integrality family*. URL: <https://oeis.org/A091190>.

*Commentary.*

A triangular coefficient construction gives rational existence for every exponent at least two and integer existence for prime exponents. For a composite exponent p, choose its least prime factor q. Below degree p the residual equation implies (n+1) times coefficient n+1 equals (1+pn) times coefficient n. Integral coefficients would therefore give q! times coefficient q equal to one modulo q, contradicting divisibility of q! by q.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.result`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality](HannaPrimeSubstitutionIntegrality.md)

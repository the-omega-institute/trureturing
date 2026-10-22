# Integral Compositional Square Roots and Hanna's Parity Conjecture

## Abstract

The normalized solution of Hanna's system has integer coefficients, odd exactly at powers of two.

PowerSeries is the ring of formal power series and X is its indeterminate. The expression PowerSeries.subst(u,f) means f(u(X)); the inner series is the first argument. The coefficient operator coeff(n,A) extracts the coefficient of X to the power n. The integer m is cast to the rationals when compared with a rational coefficient.

**Definition 1.1 (The normalized generating equations).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\exists B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (A = B + 5 \cdot A^{2}) \land (\operatorname{PowerSeries}.\operatorname{subst}\left(A - A^{2}, B\right) = X))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A378258, a compositional square root and dyadic parity*. URL: <https://oeis.org/A378258>.

*Commentary.*

The unpaginated OEIS A378258 Name states: "G.f. satisfies A(x) = B(x) + 5*A(x)^2 where B(A(x) - A(x)^2) = x." The offset is one and a(1)=1. A and B have rational coefficients; the constant coefficient of A is zero and its linear coefficient is one.

**Definition 1.2 (The parity assertion).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, n = 2^{k}))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A378258, a compositional square root and dyadic parity*. URL: <https://oeis.org/A378258>.

*Commentary.*

The unpaginated OEIS A378258 Comments state: "Conjecture: a(n) is odd iff n is a power of 2." A normalized solution exists. For every normalized solution and every natural n at least one, its degree-n coefficient is an integer m, and Odd(m) holds exactly when n equals two to a natural power.

**Theorem 1.3 (Integrality and dyadic parity).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, n = 2^{k})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A378258, a compositional square root and dyadic parity*. URL: <https://oeis.org/A378258>.

*Commentary.*

Write K for CatalanCompositionSquareParity.catalanSeries, which satisfies K=X+K squared. For any integer series H divisible by X squared, successive coefficient corrections construct a normalized integer series B with B(B(X))=X+4H and B congruent to X modulo two. Each correction is even because the residual is divisible by four, and each corrected degree leaves the preceding coefficients unchanged. Apply this construction to H=X-K. Composing K with the compositional inverse of B gives an integral solution A of the two equations. Uniqueness of normalized compositional square roots over the rationals identifies every rational solution with A. Reducing A(B(X))=K modulo two gives A=K modulo two. The coefficient support of K modulo two is exactly the powers of two.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.result`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](CatalanCompositionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree](HannaHalfIterateCubicModThree.md)
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../Residue/CompositionalSquareDyadicDenominators.md)

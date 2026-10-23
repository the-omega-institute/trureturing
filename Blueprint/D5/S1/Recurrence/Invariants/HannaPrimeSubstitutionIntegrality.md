# Integral solutions for prime substitution exponents

## Abstract

Every prime exponent has a normalized integer power series satisfying Hanna's substitution equation.

PowerSeries.subst takes the inner series first. Coefficients and indices use the displayed rings and natural numbers. A zero constant coefficient and linear coefficient one express G(0)=0 and G'(0)=1. Raising the equation to the pth power expresses the source root with leading coefficient one. Modulo p, Frobenius makes every residual coefficient divisible by p; successive coefficient corrections stabilize to an integer series.

**Definition 1.1 (Hanna's prime-exponent conjecture).**

$$(\operatorname{claim}) \iff (\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies (\exists G: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(G\right) = 0) \land ((\operatorname{coeff}\left(1, G\right) = 1) \land (G^{p} = \operatorname{PowerSeries}.\operatorname{subst}\left(X^{p} + (p: \operatorname{PowerSeries}\left(\mathbb{Z}\right)) \cdot X \cdot G^{p}, G\right)))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

OEIS A271931, A271932 and A271933, COMMENTS (unpaginated): "More generally, for prime p there exists an integer series G(x) that satisfies: G(x) = G( x^p + p*x*G(x)^p )^(1/p) with G(0)=0, G'(0)=1 (conjecture)." Integer series means PowerSeries over the integers; the chosen root has linear coefficient one.

**Definition 1.2 (The substitution argument).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall p: \mathbb{N}, \forall c: R, \forall f: \operatorname{PowerSeries}\left(R\right), \operatorname{General}.\operatorname{inner}\left(p, c, f\right) = X^{p} + \operatorname{C}\left(c\right) \cdot X \cdot f^{p}$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.inner` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

The argument is X to the power p plus c times X times the pth power of f.

**Theorem 1.3 (The substitution argument has zero constant coefficient).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall p: \mathbb{N}, (0 < p) \implies (\forall c: R, \forall f: \operatorname{PowerSeries}\left(R\right), \operatorname{constantCoeff}\left(\operatorname{General}.\operatorname{inner}\left(p, c, f\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.inner_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

For a positive exponent the substitution argument has zero constant coefficient, so formal substitution is defined.

**Theorem 1.4 (Triangular coefficient lifting).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall F: \operatorname{PowerSeries}\left(R\right) \to \operatorname{PowerSeries}\left(R\right), \forall base: \operatorname{PowerSeries}\left(R\right), \forall n0: \mathbb{N}, \forall s: \mathbb{N}, \forall a: R, \forall q: R \to R, (\forall n: \mathbb{N}, (n0 \le n) \implies (\forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (\forall k: \mathbb{N}, (k < n0) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, base\right))) \implies ((\forall k: \mathbb{N}, (k < n0) \implies (\operatorname{coeff}\left(k, g\right) = \operatorname{coeff}\left(k, base\right))) \implies ((\forall k: \mathbb{N}, (k < n) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, g\right))) \implies (\forall k: \mathbb{N}, (k < n + s) \implies (\operatorname{coeff}\left(k, F\left(f\right)\right) = \operatorname{coeff}\left(k, F\left(g\right)\right))))))) \implies ((\forall n: \mathbb{N}, (n0 \le n) \implies (\forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (\forall k: \mathbb{N}, (k < n0) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, base\right))) \implies ((\forall k: \mathbb{N}, (k < n0) \implies (\operatorname{coeff}\left(k, g\right) = \operatorname{coeff}\left(k, base\right))) \implies ((\forall k: \mathbb{N}, (k < n) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, g\right))) \implies (\operatorname{coeff}\left(n + s, F\left(f\right)\right) - \operatorname{coeff}\left(n + s, F\left(g\right)\right) = a \cdot (\operatorname{coeff}\left(n, f\right) - \operatorname{coeff}\left(n, g\right))))))) \implies ((\forall f: \operatorname{PowerSeries}\left(R\right), (\forall k: \mathbb{N}, (k < n0) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, base\right))) \implies (\forall n: \mathbb{N}, a \cdot q\left(\operatorname{coeff}\left(n, F\left(f\right)\right)\right) = -\operatorname{coeff}\left(n, F\left(f\right)\right))) \implies ((\forall k: \mathbb{N}, (k < n0 + s) \implies (\operatorname{coeff}\left(k, F\left(base\right)\right) = \operatorname{coeff}\left(k, 0\right))) \implies (\exists f: \operatorname{PowerSeries}\left(R\right), (\forall k: \mathbb{N}, (k < n0) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, base\right))) \land (F\left(f\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.exists_lifted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

Suppose equal initial coefficients make residuals agree to a shifted order, their first possible difference is a times the new coefficient difference, and q cancels each residual coefficient after multiplication by a. A base residual vanishing through the initial shifted order then lifts to a series with residual zero. At each stage one coefficient is corrected; stabilization defines the limiting coefficient function.

**Theorem 1.5 (Uniqueness of the normalized solution).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall p: \mathbb{N}, (2 \le p) \implies (\forall c: R, [\operatorname{NoZeroDivisors}\left(R\right)], ((p: R) \neq 0) \implies (\forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{constantCoeff}\left(g\right) = 0) \implies ((\operatorname{coeff}\left(1, f\right) = 1) \implies ((\operatorname{coeff}\left(1, g\right) = 1) \implies ((f^{p} = \operatorname{PowerSeries}.\operatorname{subst}\left(X^{p} + \operatorname{C}\left(c\right) \cdot X \cdot f^{p}, f\right)) \implies ((g^{p} = \operatorname{PowerSeries}.\operatorname{subst}\left(X^{p} + \operatorname{C}\left(c\right) \cdot X \cdot g^{p}, g\right)) \implies (f = g))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.solution_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

Over a commutative ring without zero divisors, a nonzero exponent coefficient forces two normalized solutions to coincide. Strong induction compares their first possible coefficient difference.

**Theorem 1.6 (Integral solutions for multiples of a prime).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies (\forall c: \mathbb{Z}, ((p: \mathbb{Z}) \mid c) \implies (\exists G: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(G\right) = 0) \land ((\operatorname{coeff}\left(1, G\right) = 1) \land (G^{p} = \operatorname{PowerSeries}.\operatorname{subst}\left(X^{p} + \operatorname{C}\left(c\right) \cdot X \cdot G^{p}, G\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.exists_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

For every prime p and every integer c divisible by p, the residual is coefficientwise divisible by p. Integer division supplies the correction, and triangular lifting produces a normalized integer solution.

**Theorem 1.7 (The prime-exponent conjecture holds).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies (\exists G: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(G\right) = 0) \land ((\operatorname{coeff}\left(1, G\right) = 1) \land (G^{p} = \operatorname{PowerSeries}.\operatorname{subst}\left(X^{p} + (p: \operatorname{PowerSeries}\left(\mathbb{Z}\right)) \cdot X \cdot G^{p}, G\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271931, A271932 and A271933: prime substitution integrality*. URL: <https://oeis.org/A271931>.

*Commentary.*

Taking c=p in the integral construction proves the conjecture for every prime exponent.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.exists_integral`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.exists_lifted`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.inner`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.inner_zero`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.solution_unique`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)

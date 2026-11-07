# Hanna's OEIS A320949 Modulo-Three Conjecture

## Abstract

The OEIS A320949 coefficientwise generating equation has a rational solution whose positive coefficients are all divisible by three.

Paul D. Hanna, OEIS A320949 revision 12 (2018-11-25), states verbatim: "G.f. A(x) satisfies: Sum_{n>=0} (1+x)^(n^2) / (1 + A(x))^(n+1)  =  1." Its formula line states verbatim: "a(n) = 0 (mod 3) for n > 0 (conjecture)." The coefficient a(n) is [x^n]A(x), and the displayed example fixes A(0)=1. The infinite sum is read coefficientwise through convergent rational sums in the usual topology.

**Definition 1.1 (The nth summand).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall j \in \mathbb{N},\; \operatorname{term}\left(A, j\right) = (1 + X)^{(j)^{2}} \cdot \operatorname{inv}\left((1 + A)^{j + 1}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA320949ModThree.term` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A320949, generating function with square exponents*. URL: <https://oeis.org/A320949>.

*Commentary.*

The source summand is (1+x)^(n^2)/(1+A(x))^(n+1). Under IsGF(A), the series 1+A has constant coefficient two and the denominator (1+A)^(n+1) has constant coefficient 2^(n+1), so the denominator has a formal power-series inverse.

**Definition 1.2 (The coefficientwise generating equation).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall k \in \mathbb{N},\; \operatorname{HasSum}\left((j: \mathbb{N} \mapsto \operatorname{coeff}\left(k, \operatorname{term}\left(A, j\right)\right)), \operatorname{coeff}\left(k, 1\right)\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA320949ModThree.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A320949, generating function with square exponents*. URL: <https://oeis.org/A320949>.

*Commentary.*

IsGF(A) fixes the constant coefficient and requires, for every natural degree k, that the rational coefficient sum of the nth summands equals the coefficient of the constant series one.

**Definition 1.3 (Hanna's modulo-three conjecture).**

$$\operatorname{claim} = ((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \implies (\forall n \in \mathbb{N},\; (0 < n) \implies (\exists z \in \mathbb{Z},\; \operatorname{coeff}\left(n, A\right) = (3 \cdot z: \mathbb{Q})))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA320949ModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A320949, generating function with square exponents*. URL: <https://oeis.org/A320949>.

*Commentary.*

The proposition asserts existence of a rational solution and says that every rational solution has each positive-degree coefficient equal to an integer multiple of three. The integer witness expresses integrality rather than assuming it.

**Theorem 1.4 (The modulo-three conjecture is proved).**

$$(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \implies (\forall n \in \mathbb{N},\; (0 < n) \implies (\exists z \in \mathbb{Z},\; \operatorname{coeff}\left(n, A\right) = (3 \cdot z: \mathbb{Q}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA320949ModThree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A320949, generating function with square exponents*. URL: <https://oeis.org/A320949>.

*Commentary.*

Finite Newton expansion of the even polynomial t ↦ choose(t^2,k) gives an integral transform. HannaA301310Divisibility.falling_hasSum at m=1 forces the positive rows of that transform to vanish modulo three, and coefficientwise contraction gives a unique normalized fixed point over every commutative coefficient ring. Mapping the integral fixed point to the rationals establishes the coefficientwise equation, while reduction to ZMod(3) forces every positive coefficient to vanish there.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA320949ModThree.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA320949ModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA320949ModThree.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA320949ModThree.term`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../Residue/CompositionalSquareDyadicDenominators.md)
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../Residue/ContinuedFractionOddSquare.md)
- Dependency: [D5/S3/ArithSums/HannaA301310Divisibility](../../../S3/ArithSums/HannaA301310Divisibility.md)

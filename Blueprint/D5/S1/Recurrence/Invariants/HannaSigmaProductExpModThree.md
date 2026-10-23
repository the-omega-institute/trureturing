# Hanna's Sigma-Product Exponential Congruence

## Abstract

The A382124 and A382125 coefficients agree at the Frobenius indices modulo three.

**Definition 1.1 (The A382124 generating function).**

$$\operatorname{A}\left(\right) = \operatorname{subst}\left(\operatorname{mk}\left((fun n: \mathbb{N} \mapsto \frac{\frac{(\operatorname{sigma}\left(1, n\right): \mathbb{Q}) \cdot (\operatorname{sigma}\left(1, 2 \cdot n\right): \mathbb{Q})}{3}}{(n: \mathbb{Q})})\right), \operatorname{exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

G.f. A(x) = exp( Sum_{n>=1} sigma(n)*sigma(2*n)/3 * x^n/n ), where sigma(n) = A000203(n) is the sum of the divisors of n. The NAME is unpaginated. The formal exponential is PowerSeries.exp over the rationals, composed with the power series constructed by mk. Indices begin at zero; the zero coefficient in the input is zero. All divisions displayed here are rational divisions.

**Definition 1.2 (The A382125 generating function).**

$$\operatorname{B}\left(\right) = \operatorname{subst}\left(\operatorname{mk}\left((fun n: \mathbb{N} \mapsto \frac{(\operatorname{sigma}\left(1, n\right): \mathbb{Q}) \cdot (\operatorname{sigma}\left(1, 2 \cdot n\right): \mathbb{Q})}{(n: \mathbb{Q})})\right), \operatorname{exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.B` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

G.f. A(x) = exp( Sum_{n>=1} sigma(n)*sigma(2*n) * x^n/n ), where sigma(n) = A000203(n) is the sum of the divisors of n. The NAME is unpaginated. The formal exponential is PowerSeries.exp over the rationals, composed with the power series constructed by mk. Indices begin at zero; the zero coefficient in the input is zero. All divisions displayed here are rational divisions.

**Definition 1.3 (Hanna's congruence).**

$$\operatorname{claim}\left(\right) \iff (\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(n, \operatorname{A}\left(\right)\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n, \operatorname{B}\left(\right)\right) = (v: \mathbb{Q})) \land (u \equiv v \pmod{3})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

Conjecture: a(n) == A382125(3*n) (mod 3) for n >= 0. OEIS A382124, COMMENT (unpaginated). The two integer witnesses encode the indicated rational coefficients and their integer congruence for every natural index.

**Theorem 1.4 (Integer coefficients of A).**

$$\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, \operatorname{A}\left(\right)\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.AIntegral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

The integer sequence sigma(n) sigma(2n)/3 satisfies the Dold prime-power congruences. At the prime three, multiplicativity separates a power of three and the difference of two consecutive divisor sums supplies the needed power of three.

**Definition 1.5 (An integer lift of A).**

$$\operatorname{integerSeries}\left(\right) = \operatorname{mk}\left((fun n: \mathbb{N} \mapsto \operatorname{Classical.choose}\left(\operatorname{AIntegral}\left(n\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.integerSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

Classical.choose selects the integer coefficient whose rational image equals coefficient n of A.

**Theorem 1.6 (The cube maps to B).**

$$\operatorname{map}\left(\operatorname{Int.castRingHom}\left(\mathbb{Q}\right), \operatorname{integerSeries}\left(\right)^{3}\right) = \operatorname{B}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.integerCube_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

Multiplying the logarithmic input by three cubes its formal exponential. Mapping the integer lift to the rationals therefore identifies its cube with B.

**Theorem 1.7 (Frobenius in each residue class).**

$$\forall n: \mathbb{N}, (\operatorname{coeff}\left(3 \cdot n, \operatorname{integerSeries}\left(\right)^{3}\right) \equiv \operatorname{coeff}\left(n, \operatorname{integerSeries}\left(\right)\right) \pmod{3}) \land ((\operatorname{coeff}\left(3 \cdot n + 1, \operatorname{integerSeries}\left(\right)^{3}\right) \equiv 0 \pmod{3}) \land (\operatorname{coeff}\left(3 \cdot n + 2, \operatorname{integerSeries}\left(\right)^{3}\right) \equiv 0 \pmod{3}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.cube_residues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

Reduction to ZMod(3) turns cubing into substitution of X cubed. The coefficients in the other two residue classes vanish modulo three.

**Theorem 1.8 (The A382124 conjecture).**

$$\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(n, \operatorname{A}\left(\right)\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n, \operatorname{B}\left(\right)\right) = (v: \mathbb{Q})) \land (u \equiv v \pmod{3}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

The integer lift and its cube give the two coefficient witnesses; Frobenius proves their congruence at every index.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.A`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.AIntegral`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.B`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.cube_residues`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.integerCube_map`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.integerSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.result`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](../Algebraic/DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](../Algebraic/HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S3/Arith/Robin/PrimeFiberPropagation](../../../S3/Arith/Robin/PrimeFiberPropagation.md)

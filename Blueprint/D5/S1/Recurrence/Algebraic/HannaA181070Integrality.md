# Hanna A181070 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181070 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(n + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n, k\right): \mathbb{Q})^{k + 1}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181070, NAME (web entry, no page number): "Expansion of G.f.: A(x) = exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^(k+1)*x^k)*x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181070, NAME (web entry, no page number): "Expansion of G.f.: A(x) = exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^(k+1)*x^k)*x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181070, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Theorem 1.4 (Lifting coefficients along prime scaling).**

$$\forall U: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall p: \mathbb{N}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies ((p: \mathbb{Z})^{\operatorname{padicValNat}\left(p, n\right) + 1} \mid \operatorname{PowerSeries.coeff}\left(p \cdot k, U^{p \cdot n}\right) - \operatorname{PowerSeries.coeff}\left(k, U^{n}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.coeffLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Prime-power lifting of a series power compares coefficients at k and p times k.

**Theorem 1.5 (The variable exponent congruence).**

$$\forall p: \mathbb{N}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, \forall b: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies ((n \mid k \cdot b) \implies (\operatorname{Nat.ModEq}\left(p^{\operatorname{padicValNat}\left(p, n\right) + 1}, b^{p \cdot k + 1}, b^{k + 1}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.variableExponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

For bases coprime to p, Euler's theorem changes the exponent. For bases divisible by p, the divisibility assumption makes both powers vanish modulo the stated prime power.

**Definition 1.6 (A diagonal rational series).**

$$\forall F: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, \operatorname{L}\left(F\right) = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \frac{(F\left(n, m - n\right): \mathbb{Q})}{(n: \mathbb{Q})})\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

The coefficient in degree m is the finite diagonal sum of F(n,m-n)/n. Subtraction takes place in the natural numbers and division takes place in the rationals.

**Theorem 1.7 (A sufficient array criterion).**

$$\forall F: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (n \ne 0) \implies (n \mid k \cdot F\left(n, k\right))) \implies ((\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (n \ne 0) \implies ((p: \mathbb{Z})^{\operatorname{padicValNat}\left(p, n\right) + 1} \mid (F\left(p \cdot n, p \cdot k\right): \mathbb{Z}) - (F\left(n, k\right): \mathbb{Z})))) \implies (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{PowerSeries.subst}\left(\operatorname{L}\left(F\right), \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)\right) = (z: \mathbb{Q})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.integralGeneric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

The weighted diagonal with weight n+k satisfies Dold congruences. The Dold exponential integrality criterion then supplies an integer for each coefficient.

**Theorem 1.8 (Divisibility of coefficients of powers).**

$$\forall U: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall n: \mathbb{N}, \forall k: \mathbb{N}, (n: \mathbb{Z}) \mid (k: \mathbb{Z}) \cdot \operatorname{PowerSeries.coeff}\left(k, U^{n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.coefficientDivisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Differentiating a power expresses k times its coefficient as n times a coefficient of the derivative product.

**Theorem 1.9 (Binomial coefficient divisibility).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, n \mid k \cdot \operatorname{Nat.choose}\left(n, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.binomDiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Coefficient divisibility for the power of 1+X makes k times Nat.choose n k a multiple of n.

**Theorem 1.10 (Binomial coefficient congruence).**

$$\forall p: \mathbb{N}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \implies (\operatorname{Nat.ModEq}\left(p^{\operatorname{padicValNat}\left(p, n\right) + 1}, \operatorname{Nat.choose}\left(p \cdot n, p \cdot k\right), \operatorname{Nat.choose}\left(n, k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.binomCong` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Coefficient lifting applied to the power series 1+X gives the binomial congruence.

**Theorem 1.11 (Divisibility survives positive powers).**

$$\forall B: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, \forall e: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (n \ne 0) \implies (n \mid k \cdot B\left(n, k\right))) \implies (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (n \ne 0) \implies (n \mid k \cdot B\left(n, k\right)^{e\left(n, k\right) + 1}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.divPower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Multiplication by further powers preserves the original divisibility.

**Theorem 1.12 (Collecting an unbounded inner sum).**

$$\forall F: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, \forall m: \mathbb{N}, \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(F\left(n, k\right): \mathbb{Q})}{(n: \mathbb{Q})} else 0)\right))\right) = \operatorname{PowerSeries.coeff}\left(m, \operatorname{L}\left(F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.literalUnbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

For a fixed degree, the equation n+k=m selects exactly one inner index. The zero outer index contributes zero by rational division.

**Theorem 1.13 (Collecting a bounded inner sum).**

$$\forall F: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (n < k) \implies (F\left(n, k\right) = 0)) \implies (\forall m: \mathbb{N}, \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(n + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(F\left(n, k\right): \mathbb{Q})}{(n: \mathbb{Q})} else 0)\right))\right) = \operatorname{PowerSeries.coeff}\left(m, \operatorname{L}\left(F\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.literalBounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

If the array vanishes above k=n, restricting the inner sum to k at most n leaves every coefficient unchanged.

**Theorem 1.14 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Every coefficient of the displayed formal exponential is an integer. The prime-scaling congruence and diagonal identity reduce the assertion to the Dold exponential integrality criterion.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.L`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.binomCong`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.binomDiv`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.coeffLift`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.coefficientDivisibility`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.divPower`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.integralGeneric`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.literalBounded`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.literalUnbounded`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181070Integrality.variableExponent`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform](../Invariants/HannaLegendreCentralBinomialTransform.md)
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../Residue/CompositionalSquareDyadicDenominators.md)

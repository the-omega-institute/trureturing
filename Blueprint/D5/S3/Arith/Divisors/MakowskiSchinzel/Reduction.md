# Minimal counterexamples and radical monotonicity

## Abstract

Minimal counterexamples and radical monotonicity

**Definition 1.1 (The normalized ratio).**

$$\forall n \in \mathbb{N},\; \operatorname{alpha}\left(n\right) = \frac{\operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)}{n}$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The ratio is rational. Division by zero gives alpha(0)=0.

**Definition 1.2 (Distinct non-Fermat odd prime factors).**

$$\forall n \in \mathbb{N},\; \operatorname{eta}\left(n\right) = \operatorname{card}\left(\operatorname{nonFermatFactors}\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.eta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The finite support consists of primes q dividing n with q different from 2 and q-1 not a power of 2. Multiplicity is discarded, and eta(0)=eta(1)=0.

**Theorem 1.3 (The totient-product factorization).**

$$\forall n \in \mathbb{N},\; \operatorname{alpha}\left(n\right) = \operatorname{abundancyIndex}\left(\operatorname{totient}\left(n\right)\right) \cdot \prod_{p \in \operatorname{primeFactors}\left(n\right)} (1 - \frac{1}{p})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For every natural n, alpha(n) is the abundancy index of its totient times the product of 1-1/p over its distinct prime divisors. The zero case is included. The abundancy index of a positive integer m is sigma(m)/m.

**Theorem 1.4 (The radical gives a lower ratio).**

$$\forall n \in \mathbb{N},\; n \ne 0 \Rightarrow \operatorname{alpha}\left(\operatorname{radical}\left(n\right)\right) \le \operatorname{alpha}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha_radical_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Passing to the radical preserves the prime support and decreases the totient's abundancy index by divisibility. The result compares the normalized ratios independently of the prime exponents. The nonzero condition is necessary: radical(0)=1, alpha(1)=1 and alpha(0)=0.

**Theorem 1.5 (Adjoining the factor two).**

$$\forall m \in \mathbb{N},\; \operatorname{Odd}\left(m\right) \Rightarrow \operatorname{alpha}\left(2 \cdot m\right) = \frac{\operatorname{alpha}\left(m\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For odd m, adjoining two preserves the totient and halves the normalized sigma-totient ratio. The oddness premise cannot be dropped: at m=2 the two sides are 3/4 and 1/4. The identity also holds at m=0.

**Theorem 1.6 (A squarefree minimal counterexample).**

$$\forall P \in \mathbb{N} \to Prop,\; \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Odd}\left(b\right) \Rightarrow \left(a \mid b \Rightarrow \left(P\left(b\right) \Rightarrow P\left(a\right)\right)\right)\right) \Rightarrow \left(\left(\exists n \in \mathbb{N},\; \operatorname{Odd}\left(n\right) \land \left(P\left(n\right) \land \operatorname{alpha}\left(n\right) < 1\right)\right) \Rightarrow \left(\exists m \in \mathbb{N},\; \operatorname{Odd}\left(m\right) \land \left(P\left(m\right) \land \left(\operatorname{Squarefree}\left(m\right) \land \left(\operatorname{alpha}\left(m\right) < 1 \land \left(\left(\forall d \in \mathbb{N},\; d \mid m \Rightarrow \left(d < m \Rightarrow 1 \le \operatorname{alpha}\left(d\right)\right)\right) \land \left(\forall d \in \mathbb{N},\; \operatorname{Odd}\left(d\right) \Rightarrow \left(P\left(d\right) \Rightarrow \left(d < m \Rightarrow 1 \le \operatorname{alpha}\left(d\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.exists_minimal_odd_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For a class P closed under divisors of odd members, an odd counterexample yields an odd, squarefree minimal counterexample in P. Every proper divisor has ratio at least 1. Every smaller odd member of P also has ratio at least 1. No closure condition is imposed on even members of P.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha_factorization`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha_radical_le`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.alpha_two_mul`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.eta`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.exists_minimal_odd_counterexample`

# Hadamard's truncated binomial limit

## Abstract

The truncated binomial limit equals the entire Hadamard factorial function at every complex parameter.

**Definition 1.1 (IsHadamard).**

$$\forall H \in (\mathbb{C}\to\mathbb{C}),\; \operatorname{IsHadamard}\left(H\right) \Leftrightarrow \left(\operatorname{Differentiable}\left(\mathbb{C}, H\right) \land \left(\left(\forall m \in \mathbb{N},\; H\left((m:\mathbb{C}) + 1\right) = (\operatorname{Nat.factorial}\left(m\right):\mathbb{C})\right) \land \left(\forall y \in \mathbb{C},\; (\forall m \in \mathbb{N},\; y \ne (m:\mathbb{C}) + 1) \Rightarrow H\left(y\right) = \frac{\operatorname{Complex.digamma}\left(1 - \frac{y}{2}\right) - \operatorname{Complex.digamma}\left(\frac{1 - y}{2}\right)}{2 \cdot \operatorname{Complex.Gamma}\left(1 - y\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.IsHadamard` (`✓ std3`).

*Citation.* David Ulgenes (2026). *OEIS A398064, truncated-binomial limit for Hadamard's Gamma function*. URL: <https://oeis.org/A398064>.

*Commentary.*

The unpaginated COMMENT field of OEIS A398064, revision 39, states: "The Hadamard function is an entire extension of the factorial function not equal to the gamma function. In other words, H(n) = (n-1)! for positive integers n." Here Differentiable over Complex expresses entire differentiability. The quotient specifies the function away from positive integers, where its factorial values give the removable continuation. The digamma quotient is the derivative form of Yin–Zhang equation (4.1).

**Definition 1.2 (truncation).**

$$\forall x \in \mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{truncation}\left(x, n\right) = \operatorname{Complex.exp}\left((x + 1) \cdot (\operatorname{Real.log}\left((n:\mathbb{R})\right):\mathbb{C})\right) \cdot \sum_{k\in\operatorname{Finset.range}\left(n + 1\right)} \frac{(-(1:\mathbb{C}))^{k}}{(n:\mathbb{C}) + (k:\mathbb{C})} \cdot \operatorname{Ring.choose}\left(x, k\right)$$

*Formalization.* `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.truncation` (`✓ std3`).

*Citation.* David Ulgenes (2026). *OEIS A398064, truncated-binomial limit for Hadamard's Gamma function*. URL: <https://oeis.org/A398064>.

*Commentary.*

OEIS A398064, unpaginated FORMULA field, revision 39: "Conjecture: H(x+1) = lim_{n->oo} n^{x+1} * Sum_{k=0..n} (-1)^k/(n+k) * binomial(x, k) such that H(1/4) = 0.79564036... . Changing the upper bound of the sum to oo yields Euler's product representation of the Gamma function." The displayed finite sum is truncation x n. Ring.choose gives the generalized binomial coefficient; the exponential uses the real logarithm of n. Both k=0 and k=n are included. Natural indices are cast to Complex in the denominator and to Real before Real.log. Only positive n affect the limit.

**Definition 1.3 (claim).**

$$claim \Leftrightarrow \left((\exists H \in (\mathbb{C}\to\mathbb{C}),\; \operatorname{IsHadamard}\left(H\right)) \land \left(\forall H \in (\mathbb{C}\to\mathbb{C}),\; \operatorname{IsHadamard}\left(H\right) \Rightarrow \left(\forall x \in \mathbb{C},\; \operatorname{Tendsto}\left(\operatorname{truncation}\left(x\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(H\left(x + 1\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.claim` (`✓ std3`).

*Citation.* David Ulgenes (2026). *OEIS A398064, truncated-binomial limit for Hadamard's Gamma function*. URL: <https://oeis.org/A398064>.

*Commentary.*

OEIS A398064, unpaginated FORMULA field, revision 39: "Conjecture: H(x+1) = lim_{n->oo} n^{x+1} * Sum_{k=0..n} (-1)^k/(n+k) * binomial(x, k) such that H(1/4) = 0.79564036... . Changing the upper bound of the sum to oo yields Euler's product representation of the Gamma function." The parameter x ranges over Complex, H maps Complex to Complex, and n tends to infinity through Naturals. Existence of the entire source function is asserted, followed by convergence for every function satisfying IsHadamard. The quoted decimal example and the statement about changing the upper limit to infinity are outside this proposition.

**Theorem 1.4 (result).**

$$(\exists H \in (\mathbb{C}\to\mathbb{C}),\; \operatorname{IsHadamard}\left(H\right)) \land \left(\forall H \in (\mathbb{C}\to\mathbb{C}),\; \operatorname{IsHadamard}\left(H\right) \Rightarrow \left(\forall x \in \mathbb{C},\; \operatorname{Tendsto}\left(\operatorname{truncation}\left(x\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(H\left(x + 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Ulgenes (2026). *OEIS A398064, truncated-binomial limit for Hadamard's Gamma function*. URL: <https://oeis.org/A398064>.

*Commentary.*

Euler's Gamma sequence supplies the scaled coefficient limit. On the left half-plane Re(x)<-1, a continuous weighted Riemann sum and two vanishing endpoints identify the limit with a Nielsen-beta integral. The digamma series identifies that integral, while a reciprocal-Gamma derivative construction supplies an entire factorial interpolation. The exact finite-sum shift and the interpolation's functional equation extend convergence to every complex parameter. The omitted infinite tail, convergence uniform in x, and altered cutoff ratios are separate questions.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.IsHadamard`
- Truth anchor: `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.claim`
- Truth anchor: `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.result`
- Truth anchor: `D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.truncation`
- Dependency: [D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds](../../Analytic/SeriesInequalities/NormalizedPochhammerBounds.md)
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling](../../Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.md)
- Dependency: [D5/S3/Weil/Analytic/BaezDuarteNewton](../Analytic/BaezDuarteNewton.md)

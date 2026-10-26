# Kotesovec's logarithmic limit for A265842

## Abstract

The logarithm of the weighted distinct-partition coefficient has Kotesovec's ratio asymptotic.

**Definition 1.1 (The source coefficient).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{Polynomial}.\operatorname{coeff}\left((\prod_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} (1 + \operatorname{Polynomial}.\operatorname{C}\left(k^{5}\right) \cdot \operatorname{Polynomial}.\operatorname{X}^{k}: \operatorname{Polynomial}\left(\mathbb{N}\right))), n\right)$$

*Formalization.* `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265842.a` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Vaclav Kotesovec (2018). *OEIS A022629 and the weighted distinct-partition logarithmic conjectures*. URL: <https://oeis.org/A022629>.

*Commentary.*

OEIS A265842, NAME (unpaginated): "Expansion of Product_{k>=1} (1 + k^5*x^k)." The coefficient index n ranges over all natural numbers, including zero. Only factors with index at most n contribute to degree n; the empty product gives a(0) = 1.

**Definition 1.2 (The source asymptotic).**

$$claim = (\operatorname{Filter}.\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \frac{\operatorname{Real}.\operatorname{log}\left((\operatorname{a}\left(n\right): \mathbb{R})\right)}{5 \cdot \operatorname{Real}.\operatorname{sqrt}\left(\frac{(n: \mathbb{R})}{2}\right) \cdot \left(\operatorname{Real}.\operatorname{log}\left(2 \cdot (n: \mathbb{R})\right) - 2\right)}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((1: \mathbb{R})\right)\right))$$

*Formalization.* `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265842.claim` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Vaclav Kotesovec (2018). *OEIS A022629 and the weighted distinct-partition logarithmic conjectures*. URL: <https://oeis.org/A022629>.

*Commentary.*

OEIS A265842, FORMULA (unpaginated): "Conjecture: log(a(n)) ~ 5*sqrt(n/2) * (log(2*n) - 2)." The symbol ~ means that the real quotient tends to one along all natural indices. Real.log and real division are total at the finitely many indices where their usual positive-domain interpretation does not apply.

**Theorem 1.3 (The proved logarithmic limit).**

$$\operatorname{Filter}.\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \frac{\operatorname{Real}.\operatorname{log}\left((\operatorname{a}\left(n\right): \mathbb{R})\right)}{5 \cdot \operatorname{Real}.\operatorname{sqrt}\left(\frac{(n: \mathbb{R})}{2}\right) \cdot \left(\operatorname{Real}.\operatorname{log}\left(2 \cdot (n: \mathbb{R})\right) - 2\right)}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((1: \mathbb{R})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265842.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Vaclav Kotesovec (2018). *OEIS A022629 and the weighted distinct-partition logarithmic conjectures*. URL: <https://oeis.org/A022629>.

*Commentary.*

A distinct partition whose parts are almost the first M positive integers contributes at least the r-th power of M factorial, where M is the largest index with M(M+1)/2 at most n. Every individual partition has controlled product, and the logarithm of the number of distinct partitions is at most twice the square root of n. The resulting two-sided estimates differ from r times the square root of 2n times (the logarithm of that square root minus one) by at most a constant depending on r times the square root of n. Dividing by the displayed denominator proves the ratio limit. This does not identify an additive second term or a coefficient prefactor.

## References

- Truth anchor: `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265842.a`
- Truth anchor: `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265842.claim`
- Truth anchor: `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265842.result`
- Dependency: [D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629](KotesovecA022629.md)

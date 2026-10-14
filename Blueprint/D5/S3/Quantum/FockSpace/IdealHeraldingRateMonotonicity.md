# Monotonicity of the ideal heralding rate

## Abstract

The ideal heralding rate of the photon distillation protocols strictly decreases from n = 5 and converges to one quarter.

**Definition 1.1 (The rational heralding rate).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.pRat}\left(n\right) = (\frac{(-1: \mathbb{Q})}{(n: \mathbb{Q})})^{(n - 1: \mathbb{N})} \cdot (\operatorname{Nat.factorial}\left((n - 1: \mathbb{N})\right): \mathbb{Q}) \cdot \sum_{t \in \operatorname{Finset.range}\left(n\right)} (\frac{((n: \mathbb{Q}) - (t: \mathbb{Q})) \cdot (-(n: \mathbb{Q}))^{t}}{(\operatorname{Nat.factorial}\left(t\right): \mathbb{Q})})$$

*Formalization.* `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.pRat` (`✓ std3`).

*Citation.* Jason Saied, Jeffrey Marshall, Namit Anand, Eleanor G. Rieffel (2025). *General protocols for the efficient distillation of indistinguishable photons*. DOI: [10.1103/PhysRevApplied.23.034079](https://doi.org/10.1103/PhysRevApplied.23.034079). URL: <https://arxiv.org/abs/2404.14217v4>.

*Commentary.*

For n > 2, this is the ideal heralding rate h_n(0) in Equation (III.9) of the source. Theorem III.5 identifies it for n-photon distillation protocols built from an n by n unitary whose first row has every entry equal to 1/sqrt(n). The factorial multiplies the sum. The exponent and the factorial argument use natural subtraction n - 1, whereas n - t in the summand is rational subtraction. The formula defines a rational value for every natural n, with field division equal to zero at a zero denominator.

**Definition 1.2 (The real heralding rate).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.p}\left(n\right) = (\operatorname{Rat.cast}\left(\operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.pRat}\left(n\right)\right): \mathbb{R})$$

*Formalization.* `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.p` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jason Saied, Jeffrey Marshall, Namit Anand, Eleanor G. Rieffel (2025). *General protocols for the efficient distillation of indistinguishable photons*. DOI: [10.1103/PhysRevApplied.23.034079](https://doi.org/10.1103/PhysRevApplied.23.034079). URL: <https://arxiv.org/abs/2404.14217v4>.

*Commentary.*

The rational rate is embedded into the real numbers by Rat.cast. This gives the real sequence with the same exact values.

**Definition 1.3 (Strict decrease and the quarter limit).**

$$(\operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.claim}) \Leftrightarrow ((\forall n \in \mathbb{N},\; (5 \le n) \Rightarrow (\operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.p}\left(n + 1\right) < \operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.p}\left(n\right))) \land (\operatorname{Filter.Tendsto}\left(\operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.p}, \operatorname{Filter.atTop}, \operatorname{nhds}\left((\frac{1}{4}: \mathbb{R})\right)\right)))$$

*Formalization.* `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.claim` (`✓ std3`).

*Citation.* Jason Saied, Jeffrey Marshall, Namit Anand, Eleanor G. Rieffel (2025). *General protocols for the efficient distillation of indistinguishable photons*. DOI: [10.1103/PhysRevApplied.23.034079](https://doi.org/10.1103/PhysRevApplied.23.034079). URL: <https://arxiv.org/abs/2404.14217v4>.

*Commentary.*

Conjecture III.7 states that the ideal heralding rate decreases to one quarter for n >= 5. The adjacent inequalities here are strict: p(n + 1) < p(n) for every natural n >= 5. The second clause is convergence along the natural numbers to the real number one quarter, also stated in Theorem III.5(2).

**Theorem 1.4 (The rate strictly decreases to one quarter).**

$$\operatorname{D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/saied-marshall-anand-rieffel-2025-heralding-rate-monotonicity` (proved) by `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"saied-marshall-anand-rieffel-2025-heralding-rate-monotonicity","declaration_gid":"D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jason Saied, Jeffrey Marshall, Namit Anand, Eleanor G. Rieffel (2025). *General protocols for the efficient distillation of indistinguishable photons*. DOI: [10.1103/PhysRevApplied.23.034079](https://doi.org/10.1103/PhysRevApplied.23.034079). URL: <https://arxiv.org/abs/2404.14217v4>.

*Commentary.*

For n >= 1, the finite sum has the exact decomposition p_n = A_n + (-1)^(n - 1) T_n, where A_n = n^2 integral from 0 to 1 of (1 - u) u^(n - 1) exp(n(u - 1)) du and T_n = 2 n! exp(-n) / n^(n - 1). The tail satisfies 0 <= T_n <= 2 n exp(-n).

Set r(u) = u exp(u - 1) and K(u) = 2(2u - 1)/(1 + u)^4. A primitive gives A_n = 1/4 + integral from 0 to 1 of K(u) r(u)^n du. Thus A_n - A_(n + 1) is the integral of K(u) r(u)^n (1 - r(u)). Bounding its negative part on [0, 1/2] and its positive part on [1 - 1/n, 1 - 1/(2n)] yields p_n - p_(n + 1) >= 1/(512 n^2) - (4n + 3) exp(-n) for n >= 16. The right side is positive, since 512 n^2 (4n + 3) < exp(n) on this range.

Exact rational evaluation gives p_n - p_(n + 1) > 0 for every n from 5 through 15, completing strict decrease for n >= 5. The kernel representation gives |A_n - 1/4| <= 2/(n + 1), and the tail bound gives |p_n - 1/4| <= 3/n for n >= 16. Squeezing this error to zero proves convergence to one quarter.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.claim`
- Truth anchor: `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.p`
- Truth anchor: `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.pRat`
- Truth anchor: `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.result`

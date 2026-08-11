# The Zeta Distribution as an Integer Gibbs Measure

## Abstract

The zeta distribution is the Gibbs measure for logarithmic integer energy.

**Definition 1.1 (Logarithmic energy has zeta Boltzmann weight).**

Lean statement: `D5/S3/Analytic/ZetaGibbs.weight`

*Formalization.* `D5/S3/Analytic/ZetaGibbs.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural-number state n and real inverse temperature s, the weight is the extended-nonnegative-real image of n to the power minus s. This is the Boltzmann factor exp(-s log n) on positive integers. At positive s the zero slot has weight zero, while the state n = 1 always has weight one.

**Definition 1.2 (The partition function is the total zeta weight).**

Lean statement: `D5/S3/Analytic/ZetaGibbs.partitionFunction`

*Formalization.* `D5/S3/Analytic/ZetaGibbs.partitionFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The partition function Z(s) is the ENNReal sum of all logarithmic Boltzmann weights over natural numbers. The zero slot contributes no mass in the regime s > 1, so this indexing agrees with the positive-integer Dirichlet series.

**Theorem 1.3 (The partition function is finite above one).**

$1<s \Rightarrow Z(s)\neq \infty$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaGibbs.partition_function_ne_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s > 1, the real p-series n^(-s) is summable. Mapping its nonnegative terms into ENNReal therefore gives a partition function different from infinity. The proof reuses Real.summable_nat_rpow and the standard ENNReal finite-tsum bridge.

**Theorem 1.4 (The partition function is positive).**

$0<Z(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaGibbs.partition_function_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n = 1 summand is exactly one, so the full partition function is strictly positive for every real s. In particular, normalization above inverse temperature one has both a nonzero and a finite denominator.

**Definition 1.5 (Normalization produces the zeta PMF).**

Lean statement: `D5/S3/Analytic/ZetaGibbs.zetaDist`

*Formalization.* `D5/S3/Analytic/ZetaGibbs.zetaDist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For s > 1, PMF.normalize applies to the zeta weight because its total is positive and finite. The result is a genuine probability mass function on natural numbers, with the zero state retaining zero mass.

**Theorem 1.6 (The zeta PMF has the Gibbs value formula).**

$$1<s \Rightarrow P_{s}(n)=\frac{w_{s}(n)}{\sum_{m\in \mathbb{N}}w_{s}(m)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaGibbs.zeta_dist_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise evaluation of PMF.normalize gives the Boltzmann weight times the inverse total weight, equivalently n^(-s) divided by Z(s). This is the exact Gibbs formula rather than only a support or proportionality statement.

**Theorem 1.7 (The real partition function is Riemann zeta).**

$$1<s \Rightarrow \operatorname{toReal}(Z(s))=\zeta(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaGibbs.partition_function_toReal_eq_riemannZeta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After taking the finite ENNReal total back to the reals and embedding it in the complex numbers, the partition function equals mathlib's riemannZeta at the real argument s. The proof uses mathlib's Dirichlet-series identity in the half-plane s > 1 and explicitly reconciles real rpow with complex cpow.

**Theorem 1.8 (Inverse temperature one forces divergence).**

$$Z(1)=\infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaGibbs.weight_one_tsum_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s = 1 the weight series is the harmonic series and its ENNReal total is infinity. Thus the strict hypothesis 1 < s bears the normalizability of the ensemble: PMF.normalize cannot receive the required finite-total proof at the critical inverse temperature.

## References

- Truth anchor: `D5/S3/Analytic/ZetaGibbs.partitionFunction`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.partition_function_ne_top`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.partition_function_pos`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.partition_function_toReal_eq_riemannZeta`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.weight`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.weight_one_tsum_eq_top`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.zetaDist`
- Truth anchor: `D5/S3/Analytic/ZetaGibbs.zeta_dist_apply`

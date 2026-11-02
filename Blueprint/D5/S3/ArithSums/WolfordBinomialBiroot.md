# Wolford's generalized binomial biroot

## Abstract

The original generalized binomial biroot converges for all positive real parameters and every positive root index.

The assertion is Conjecture 3.4 of arXiv:2508.14095v3. Both source summation bounds are inclusive. The ceiling is the exact rational ceiling, choose(m,j) is the natural binomial coefficient extended by zero for j>m, and each displayed exponent of c is an integer. Positive x and c are arbitrary real numbers, n ranges over every natural n>=1, and the limit uses all positive integer m, including every residue class. No parameter-uniform rate is asserted. positiveIndexQuotientSequence(x,c,n) denotes m mapped to beta(x,c,n,m), including the totalized zero value at m=0.

**Definition 1.1 (Exact ceiling).**

$$\forall m:\mathbb{N}, \forall n:\mathbb{N}, \operatorname{ceiling}\left(m, n\right)=\operatorname{ceilQ}\left(\frac{m}{n}\right)$$

*Formalization.* `D5/S3/ArithSums/WolfordBinomialBiroot.ceiling` (`✓ std3`).

*Citation.* Isaac Wolford (2025). *Combinatorial and Gaussian Foundations of Rational Nth Root Approximations: Theorems and Conjectures*. DOI: [10.48550/arXiv.2508.14095](https://doi.org/10.48550/arXiv.2508.14095). URL: <https://arxiv.org/abs/2508.14095v3>.

*Commentary.*

ceiling(m,n) is the natural ceiling of the rational quotient m/n. For n>=1 this is the ordinary integer ceiling. ceiling_bound proves m<=n*ceiling(m,n).

**Definition 1.2 (Inclusive source numerator).**

$$\forall x:\mathbb{R}, \forall c:\mathbb{R}, \forall n:\mathbb{N}, \forall m:\mathbb{N}, \operatorname{numerator}\left(x, c, n, m\right)=\sum_{k=0}^{\operatorname{ceiling}\left(m, n\right)} x^{k} \cdot c^{m - n \cdot k} \cdot \operatorname{choose}\left(m, n \cdot k\right)$$

*Formalization.* `D5/S3/ArithSums/WolfordBinomialBiroot.numerator` (`✓ std3`).

*Citation.* Isaac Wolford (2025). *Combinatorial and Gaussian Foundations of Rational Nth Root Approximations: Theorems and Conjectures*. DOI: [10.48550/arXiv.2508.14095](https://doi.org/10.48550/arXiv.2508.14095). URL: <https://arxiv.org/abs/2508.14095v3>.

*Commentary.*

The numerator includes k=0 and k=ceiling(m,n). An out-of-range binomial factor makes a padded term zero even when its signed c exponent is negative. Natural subtraction does not define the source exponent.

**Definition 1.3 (Inclusive source denominator).**

$$\forall x:\mathbb{R}, \forall c:\mathbb{R}, \forall n:\mathbb{N}, \forall m:\mathbb{N}, \operatorname{denominator}\left(x, c, n, m\right)=\sum_{k=0}^{\operatorname{ceiling}\left(m, n\right) - 1} x^{k} \cdot c^{m - n \cdot k - 1} \cdot \operatorname{choose}\left(m, n \cdot k + 1\right)$$

*Formalization.* `D5/S3/ArithSums/WolfordBinomialBiroot.denominator` (`✓ std3`).

*Citation.* Isaac Wolford (2025). *Combinatorial and Gaussian Foundations of Rational Nth Root Approximations: Theorems and Conjectures*. DOI: [10.48550/arXiv.2508.14095](https://doi.org/10.48550/arXiv.2508.14095). URL: <https://arxiv.org/abs/2508.14095v3>.

*Commentary.*

The denominator includes k=0 through ceiling(m,n)-1. For positive m and n this ceiling is positive, so the Lean range with length (ceiling-1)+1 has exactly the source indices. denominator_pos proves positivity using its k=0 term m*c^(m-1) and nonnegativity of every other term.

**Definition 1.4 (Positive-index quotient).**

$$\forall x:\mathbb{R}, \forall c:\mathbb{R}, \forall n:\mathbb{N}, \forall m:\mathbb{N}, (0<m\implies \operatorname{beta}\left(x, c, n, m\right)=\frac{\operatorname{numerator}\left(x, c, n, m\right)}{\operatorname{denominator}\left(x, c, n, m\right)})\land \operatorname{beta}\left(x, c, n, 0\right)=0$$

*Formalization.* `D5/S3/ArithSums/WolfordBinomialBiroot.beta` (`✓ std3`).

*Citation.* Isaac Wolford (2025). *Combinatorial and Gaussian Foundations of Rational Nth Root Approximations: Theorems and Conjectures*. DOI: [10.48550/arXiv.2508.14095](https://doi.org/10.48550/arXiv.2508.14095). URL: <https://arxiv.org/abs/2508.14095v3>.

*Commentary.*

beta is exactly numerator/denominator at every positive m and is totalized to zero at m=0. This isolated value does not affect atTop convergence.

**Theorem 1.5 (Full convergence and denominator domain).**

$$\forall x:\mathbb{R}, \forall c:\mathbb{R}, \forall n:\mathbb{N}, (0<x\land 0<c\land 1\le n)\implies (\forall m:\mathbb{N}, 0<m\implies 0<\operatorname{denominator}\left(x, c, n, m\right)\land \operatorname{Tendsto}\left(\operatorname{positiveIndexQuotientSequence}\left(x, c, n\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(x^{\frac{1}{n}}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/WolfordBinomialBiroot.result` (`✓ std3`). ∎

*Resolves.* `Problems/wolford-2025-generalized-binomial-biroot-conjecture-3-4` (proved) by `D5/S3/ArithSums/WolfordBinomialBiroot.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wolford-2025-generalized-binomial-biroot-conjecture-3-4","declaration_gid":"D5/S3/ArithSums/WolfordBinomialBiroot.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Isaac Wolford (2025). *Combinatorial and Gaussian Foundations of Rational Nth Root Approximations: Theorems and Conjectures*. DOI: [10.48550/arXiv.2508.14095](https://doi.org/10.48550/arXiv.2508.14095). URL: <https://arxiv.org/abs/2508.14095v3>.

*Commentary.*

For every positive real x,c and natural n>=1, all positive-index denominators are strictly positive and beta tends to x raised to the reciprocal real n. Real.rpow_pos_of_pos and Real.rpow_inv_natCast_pow identify this as the positive real nth root.

The finite state type is ZMod n. shift moves each state to its successor, and walk(a,b)=a*I+b*shift. shift_pow and walk_pow identify every power entry with the complete weighted binomial multisection. matrix_mul_nat is the scalar matrix identity used by walk_pow. walk_nonneg and walk_stochastic establish the stochastic hypotheses. walk_primitive selects the positive binomial summand indexed by the least nonnegative representative of j-i in the nth matrix power; it applies to arbitrary n, including composite n. walk_column identifies the uniform stationary row. walk_limit applies FiniteStochasticMixing.primitive_convergence and its uniqueness conclusion.

residue is the unnormalized weighted multisection. normalized_residue proves its exact scaling to a walk entry, residue_limit transfers entry convergence to 1/n, and residue_ratio_limit takes the ratio using the nonzero limit 1/n. weight, weight_zero and multisection give a finite bijection between source indices and all admissible binomial indices. numerator_residue and denominator_residue prove the literal source reconstruction for n>=2, including padded zero terms and signed exponents. limit_ge_two then transfers the exact quotient limit.

The source denominator for n=1 omits the constant binomial term. denominator_one proves the exact correction x*denominator=residue-c^m. limit_one divides by (c+x)^m and uses geometric decay of (c/(c+x))^m. Thus n=1 is proved from its original indices, without identifying it with the uncorrected residue ratio. result combines this case with limit_ge_two and consumes denominator_pos.

The generalized binomial biroot and convergence conjecture are due to Wolford, whose source proves the square-root case. The source-to-walk reconstruction above derives the general quotient limit from finite stochastic mixing.

## References

- Truth anchor: `D5/S3/ArithSums/WolfordBinomialBiroot.beta`
- Truth anchor: `D5/S3/ArithSums/WolfordBinomialBiroot.ceiling`
- Truth anchor: `D5/S3/ArithSums/WolfordBinomialBiroot.denominator`
- Truth anchor: `D5/S3/ArithSums/WolfordBinomialBiroot.numerator`
- Truth anchor: `D5/S3/ArithSums/WolfordBinomialBiroot.result`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing](../Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing.md)
